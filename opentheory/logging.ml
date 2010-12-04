(* ========================================================================= *)
(* OPENTHEORY PROOF LOGGING FOR HOL LIGHT                                    *)
(* Copyright (c) 2009 Joe Hurd, distributed under the GNU GPL version 2      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Setting up the log files: part 1                                          *)
(* ------------------------------------------------------------------------- *)

type log_state =
     Not_logging
   | Ready_logging
   | Active_logging of bool * out_channel;;

let log_state = ref Not_logging;;

let log_raw s =
    match (!log_state) with
      Active_logging (_,h) -> output_string h (s ^ "\n")
    | _ -> ();;

(* ------------------------------------------------------------------------- *)
(* Logging primitive types                                                   *)
(* ------------------------------------------------------------------------- *)

let namespace = "HOLLight";;

let mk_name s = namespace ^ "." ^ s;;

let log_num n = log_raw (string_of_int n);;

let log_name s = log_raw ("\"" ^ String.escaped s ^ "\"");;

let log_type_op_name s = log_name (mk_name s);;

let log_const_name s = log_name (mk_name s);;

let log_command s = log_raw s;;

(* ------------------------------------------------------------------------- *)
(* The dictionary                                                            *)
(* ------------------------------------------------------------------------- *)

let (log_dict_next_key,log_dict_reset_key) =
    let key = ref 0 in
    let next () = let k = !key in (key := k + 1; k) in
    let reset () = key := 0 in
    (next,reset);;

let (log_dict_reset,log_dict_reset_register) =
    let resets = ref [] in
    let register r = resets := r :: !resets in
    let reset_all () = List.iter (fun r -> r ()) (!resets) in
    let reset () = (reset_all (); log_dict_reset_key ()) in
    (reset,register);;

let log_dict_all (f : ('a -> unit) -> 'a -> unit) =
    let hashtbl = Hashtbl.create 10000 in
    let reset () = Hashtbl.clear hashtbl in
    let () = log_dict_reset_register reset in
    let mem x = Hashtbl.mem hashtbl x in
    let peek x = if mem x then Some (Hashtbl.find hashtbl x) else None in
    let save x =
        (let n = log_dict_next_key () in
         Hashtbl.add hashtbl x n;
         log_num n;
         log_command "def") in
    let rec log x =
        match (peek x) with
          Some n ->
          (log_num n;
           log_command "ref")
        | None ->
          (f log x;
           save x) in
    (mem,save,log);;

let log_dict (f : ('a -> unit) -> 'a -> unit) =
    match (log_dict_all f) with
      (_,_,log) -> log;;

(* ------------------------------------------------------------------------- *)
(* The HOL Light to OpenTheory interpretation.                               *)
(* ------------------------------------------------------------------------- *)

let mk_interpretation () =
    let int = open_in "opentheory/hol-light.int" in
    let rec read acc =
        try let l = input_line int in
            read (acc ^ "  interpret: " ^ l ^ "\n")
        with End_of_file -> acc in
    let res = read "" in
    let () = close_in int in
    res;;

let interpretation =
    let int = ref (None : string option) in
    let mk () =
        let s = mk_interpretation () in
        let () = int := Some s in
        s in
    fun () ->
        match !int with
          Some s -> s
        | None -> mk ();;

(* ------------------------------------------------------------------------- *)
(* Article files.                                                          *)
(* ------------------------------------------------------------------------- *)

type article =
     Auxiliary_article
   | Theory_article of string;;

let articles = ref ([] : (string * article) list);;

let is_auxiliary_article f =
    let n = String.length f in
    n >= 4 && String.sub f (n - 4) 4 = "-aux";;

let name_article (f,ty) =
    match ty with
      Auxiliary_article -> f
    | Theory_article s -> s;;

let exists_name_article f =
    List.exists (fun fty -> name_article fty = f) (!articles);;

let fresh_name_article f =
    let rec check i =
        let fi = f ^ "-a" ^ string_of_int i in
        if exists_name_article fi then check (i + 1) else fi in
    if exists_name_article f then check 1 else f;;

let fresh_name_auxiliary_article f =
    let s = String.sub f 0 (String.length f - 4) in
    let rec check i =
        let fi = s ^ "-a" ^ string_of_int i ^ "-aux" in
        if exists_name_article fi then check (i + 1) else fi in
    if exists_name_article f then check 1 else f;;

let filename_article fty =
    "opentheory/articles/" ^ name_article fty ^ ".art";;

let add_article n =
    let aux = is_auxiliary_article n in
    let nty = if aux then (fresh_name_auxiliary_article n, Auxiliary_article)
              else (n, Theory_article (fresh_name_article n)) in
    let () = articles := nty :: !articles in
    (aux, filename_article nty);;

(* ------------------------------------------------------------------------- *)
(* Writing theory files.                                                     *)
(* ------------------------------------------------------------------------- *)

let write_theory_file aux t ntys =
    let int = interpretation () in
    let thy = open_out ("opentheory/articles/" ^ t ^ ".thy") in
    let write_block n imps sint =
        let () = output_string thy ("\n" ^ n ^ " {\n" ^ imps) in
        let () = if sint then output_string thy int else () in
        let () = if n = "main" then ()
                 else output_string thy ("  article: \"" ^ n ^ ".art\"\n") in
        let () = output_string thy "}\n" in
        "  import: " ^ n ^ "\n" in
    let add_block (ts,xs,bs) (n,ty) =
          match ty with
            Auxiliary_article ->
              let x = write_block n bs (aux && t <> "hol-light") in
              (ts, xs ^ x, bs ^ x)
          | Theory_article f ->
            if aux || n <> t then (ts,xs,bs)
            else
              let x = write_block f bs true in
              (ts ^ x, xs, bs ^ x) in
    let () = output_string thy ("description: theory file for " ^ t ^ "\n") in
    let (ts,xs,_) = List.fold_left add_block ("","","") ntys in
    let _ = write_block "main" (if aux then xs else ts) false in
    let () = close_out thy in
    ();;

let write_theory_files () =
    let rec write_theories ntys =
        match ntys with
          [] -> ()
        | (n,ty) :: ntys' ->
          write_theories
            (match ty with
               Auxiliary_article ->
               let () = write_theory_file true n [(n,ty)] in
               ntys'
             | _ ->
               let () = write_theory_file false n (rev ntys) in
               List.filter (fun (n',_) -> n' <> n) ntys') in
    let ntys = !articles in
    let () = write_theories ntys in
    let () = write_theory_file true "hol-light" (rev ntys) in
    ();;

(* ------------------------------------------------------------------------- *)
(* Setting up the log files: part 2                                          *)
(* ------------------------------------------------------------------------- *)

let logfile_end () =
    match (!log_state) with
      Active_logging (_,h) ->
      (close_out h;
       log_state := Ready_logging)
    | _ -> ();;

let logfile n =
    logfile_end ();
    match (!log_state) with
      Ready_logging ->
      (log_dict_reset ();
       let (aux,f) = add_article n in
       let h = open_out f in
       log_state := Active_logging (aux,h))
    | _ -> ();;

let is_logging () =
    match (!log_state) with
      Active_logging _ -> true
    | _ -> false;;

let not_logging () = not (is_logging ());;

let is_aux_logging () =
    match (!log_state) with
      Active_logging (aux,_) -> aux
    | _ -> false;;

let not_aux_logging () = not (is_aux_logging ());;

let start_logging () =
    match (!log_state) with
      Not_logging -> log_state := Ready_logging
    | _ -> ();;

let stop_logging () =
    logfile_end ();
    match (!log_state) with
      Ready_logging -> (write_theory_files ();
                        log_state := Not_logging)
    | _ -> ();;

(* ------------------------------------------------------------------------- *)
(* Logging comments.                                                         *)
(* ------------------------------------------------------------------------- *)

let split s =
    let n = String.length s in
    let rec spl i =
        if i = n then []
        else if String.contains_from s i '\n' then
          let j = String.index_from s i '\n' in
          if j = i then "" :: spl (j + 1)
          else String.sub s i (j - i) :: spl (j + 1)
        else [String.sub s i (n - i)] in
    spl 0;;

let log_comment s =
    let ws = map (fun w -> if w = "" then "#" else "# " ^ w) (split s) in
    List.iter log_raw ws;;

(***
let log_comment_thm th = log_comment (string_of_thm th);;
***)

(* ------------------------------------------------------------------------- *)
(* Logging complex types                                                     *)
(* ------------------------------------------------------------------------- *)

let log_map (f : 'a -> 'b) (log_b : 'b -> unit) a = log_b (f a);;

let log_nil () = log_command "nil";;

let log_list (f : 'a -> unit) =
    let rec logl l =
        match l with
          [] -> log_nil ()
        | h :: t -> (f h; logl t; log_command "cons") in
    logl;;

let log_unit () = log_nil ();;

let log_sing (f : 'a -> unit) x =
    f x; log_nil (); log_command "cons";;

let log_pair (f : 'a -> unit) (g : 'b -> unit) (x,y) =
    f x; log_sing g y; log_command "cons";;

let log_triple (f : 'a -> unit) (g : 'b -> unit) (h : 'c -> unit) (x,y,z) =
    f x; log_pair g h (y,z); log_command "cons";;

let (log_type_op_mem,log_type_op_save,log_type_op) =
    let log _ n =
        (log_type_op_name n;
         log_command "typeOp") in
    log_dict_all log;;

let log_type_var n = log_name n;;

let log_type =
    let rec log f ty =
        if is_type ty then
          let (n,l) = dest_type ty in
          (log_type_op n; log_list f l; log_command "opType")
        else
          (log_type_var (dest_vartype ty); log_command "varType") in
    log_dict log;;

let (log_const_mem,log_const_save,log_const) =
    let log _ n =
        (log_const_name n;
         log_command "const") in
    log_dict_all log;;

let log_var v =
    let (n,ty) = dest_var v in
    (log_name n; log_type ty; log_command "var");;

let log_term =
    let rec log f tm =
        if is_const tm then
          let (n,ty) = dest_const tm in
          (log_const n; log_type ty; log_command "constTerm")
        else if is_var tm then
          (log_var tm; log_command "varTerm")
        else if is_comb tm then
          let (a,b) = dest_comb tm in
          (f a; f b; log_command "appTerm")
        else
          let (v,b) = dest_abs tm in
          (log_var v; f b; log_command "absTerm") in
    log_dict log;;

let log_inst =
  log_pair
    (log_list (log_pair log_type_var log_type))
    (log_list (log_pair log_var log_term));;

let log_type_inst =
    log_map
      (fun i -> (map (fun (ty,v) -> (dest_vartype v, ty)) i, []))
      log_inst;;

let log_term_inst =
    log_map
      (fun i -> ([], map (fun (tm,v) -> (v,tm)) i))
      log_inst;;

let (log_thm_mem,log_thm_save,log_thm) =
    let log _ th =
        (log_list log_term (hyp th);
         log_term (concl th);
         log_command "axiom") in
    log_dict_all log;;

(* ------------------------------------------------------------------------- *)
(* Logged version of the logical kernel                                      *)
(* ------------------------------------------------------------------------- *)

let REFL tm =
    let th = REFL tm in
    let () =
        if not_logging () || log_thm_mem th then ()
        else (log_term tm;
              log_command "refl";
              log_thm_save th;
              log_command "pop") in
    th;;

let MK_COMB (th1,th2) =
    let th = MK_COMB (th1,th2) in
    let () =
        if not_logging () || log_thm_mem th then ()
        else (log_thm th1;
              log_thm th2;
              log_command "appThm";
              log_thm_save th;
              log_command "pop") in
    th;;

let ABS v1 th2 =
    let th = ABS v1 th2 in
    let () =
        if not_logging () || log_thm_mem th then ()
        else (log_var v1;
              log_thm th2;
              log_command "absThm";
              log_thm_save th;
              log_command "pop") in
    th;;

let BETA tm =
    let th = BETA tm in
    let () =
        if not_logging () || log_thm_mem th then ()
        else (log_term tm;
              log_command "betaConv";
              log_thm_save th;
              log_command "pop") in
    th;;

let ASSUME tm =
    let th = ASSUME tm in
    let () =
        if not_logging () || log_thm_mem th then ()
        else (log_term tm;
              log_command "assume";
              log_thm_save th;
              log_command "pop") in
    th;;

let EQ_MP th1 th2 =
    let th = EQ_MP th1 th2 in
    let () =
        if not_logging () || log_thm_mem th then ()
        else (log_thm th1;
              log_thm th2;
              (*log_comment_thm th1;*)
              (*log_comment_thm th2;*)
              log_command "eqMp";
              (*log_comment_thm th;*)
              log_thm_save th;
              log_command "pop") in
    th;;

let DEDUCT_ANTISYM_RULE th1 th2 =
    let th = DEDUCT_ANTISYM_RULE th1 th2 in
    let () =
        if not_logging () || log_thm_mem th then ()
        else (log_thm th1;
              log_thm th2;
              log_command "deductAntisym";
              log_thm_save th;
              log_command "pop") in
    th;;

let INST_TYPE i1 th2 =
    let th = INST_TYPE i1 th2 in
    let () =
        if not_logging () || log_thm_mem th then ()
        else (log_type_inst i1;
              log_thm th2;
              log_command "subst";
              log_thm_save th;
              log_command "pop") in
    th;;

let INST i1 th2 =
    let th = INST i1 th2 in
    let () =
        if not_logging () || log_thm_mem th then ()
        else (log_term_inst i1;
              log_thm th2;
              (*log_comment_thm th2;*)
              log_command "subst";
              (*log_comment_thm th;*)
              log_thm_save th;
              log_command "pop") in
    th;;

let new_axiom tm =
    let th = new_axiom tm in
    let () =
        if not_logging () then ()
        else (log_thm th;
              log_command "pop") in
    th;;

let new_basic_definition tm =
    let th = new_basic_definition tm in
    let () =
        if not_logging () then ()
        else
          let (n,tm) = dest_eq (concl th) in
          let (n,_) = dest_const n in
          (log_const_name n;
           log_term tm;
           log_command "defineConst";
           log_thm_save th;
           log_command "pop";
           log_const_save n;
           log_command "pop") in
    th;;

let new_basic_type_definition ty (abs,rep) th =
    let (ar,ra) = new_basic_type_definition ty (abs,rep) th in
    let () =
        if not_logging () then ()
        else
          let lhs tm = fst (dest_eq tm) in
          let range ty = hd (tl (snd (dest_type ty))) in
          let (absTm,repTm) = dest_comb (lhs (concl ar)) in
          let (repTm,_) = dest_const (rator repTm) in
          let (absTm,newTy) = dest_const absTm in
          let newTy = range newTy in
          let (newTy,tyVars) = dest_type newTy in
          let tyVars = map dest_vartype tyVars in
          (log_type_op_name ty;
           log_const_name abs;
           log_const_name rep;
           log_list log_type_var tyVars;
           log_thm th;
           log_command "defineTypeOp";
           log_thm_save ra;
           log_command "pop";
           log_thm_save ar;
           log_command "pop";
           log_const_save repTm;
           log_command "pop";
           log_const_save absTm;
           log_command "pop";
           log_type_op_save newTy;
           log_command "pop") in
    (ar,ra);;

let TRANS th1 th2 =
    if not_logging () then TRANS th1 th2
    else
      let th3 = MK_COMB(REFL(rator(concl th1)),th2) in
      EQ_MP th3 th1;;

(* ------------------------------------------------------------------------- *)
(* Exporting theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

let export_raw_thm th =
    if not_logging () then ()
    else (log_thm th;
          log_list log_term (hyp th);
          log_term (concl th);
          log_command "thm");;

let export_thm th =
    if not_logging () then ()
    else if not_aux_logging () then export_raw_thm th
    else failwith "export_thm called in auxiliary mode";;

let export_aux_thm th =
    if not_logging () then ()
    else if is_aux_logging () then export_raw_thm th
    else failwith "export_aux_thm called when not in auxiliary mode";;

let export_if_aux_thm th =
    if not_logging () then ()
    else if is_aux_logging () then export_raw_thm th
    else ();;
