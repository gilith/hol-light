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
   | Active_logging of out_channel;;

let log_state = ref Not_logging;;

let log_raw s =
    match (!log_state) with
      Active_logging h -> output_string h (s ^ "\n")
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

let log_dict_all proj (f : ('a -> int) -> ('a -> unit) -> 'a -> unit) =
    let hashtbl = Hashtbl.create 10000 in
    let reset () = Hashtbl.clear hashtbl in
    let () = log_dict_reset_register reset in
    let mem x = Hashtbl.mem hashtbl (proj x) in
    let peek x = if mem x then Some (Hashtbl.find hashtbl (proj x)) else None in
    let save_ref x =
        match (peek x) with
          Some n -> n
        | None ->
          let n = log_dict_next_key () in
          let () = Hashtbl.add hashtbl (proj x) n in
          let () = log_num n in
          let () = log_command "def" in
          n in
    let save x = let _ = save_ref x in () in
    let rec log x =
        match (peek x) with
          Some n ->
            let () = log_num n in
            let () = log_command "ref" in
            ()
        | None ->
            let () = f save_ref log x in
            let () = save x in
            () in
    (save,log);;

let log_dict (f : ('a -> unit) -> 'a -> unit) =
    let proj x = x in
    let g _ log_rec x = f log_rec x in
    match (log_dict_all proj g) with
      (_,log) -> log;;

(* ------------------------------------------------------------------------- *)
(* Article files.                                                            *)
(* ------------------------------------------------------------------------- *)

type article = Article of string * string;;

let articles = ref ([] : article list);;

let reset_articles () = articles := [];;

let thy_article (Article (thy,_)) = thy;;

let name_article (Article (_,name)) = name;;

let exists_name_article name =
    List.exists (fun art -> name_article art = name) (!articles);;

let fresh_name_article name =
    let rec check i =
        let name_i = name ^ "-a" ^ string_of_int i in
        if exists_name_article name_i then check (i + 1) else name_i in
    if exists_name_article name then check 1 else name;;

let filename_article art =
    "opentheory/articles/" ^ name_article art ^ ".art";;

let add_article thy =
    let name = fresh_name_article thy in
    let art = Article (thy,name) in
    let () = articles := art :: !articles in
    filename_article art;;

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
(* Writing theory files.                                                     *)
(* ------------------------------------------------------------------------- *)

type theory_block =
     Article_theory_block of string
   | Package_theory_block of string
   | Union_theory_block;;

let write_theory_file thy names =
    let int = interpretation () in
    let h = open_out ("opentheory/articles/" ^ thy ^ ".thy") in
    let add_theory_block name imps sint block =
        let () = output_string h ("\n" ^ name ^ " {\n" ^ imps) in
        let () = if sint then output_string h int else () in
        let () =
            match block with
              Article_theory_block file ->
              output_string h ("  article: \"" ^ file ^ "\"\n")
            | Package_theory_block pkg ->
              output_string h ("  package: " ^ pkg ^ "\n")
            | Union_theory_block -> () in
        let () = output_string h "}\n" in
        "  import: " ^ name ^ "\n" in
    let add_article_block imps name =
        let file = name ^ ".art" in
        imps ^ add_theory_block name imps true (Article_theory_block file) in
    let add_union_block name imps =
        add_theory_block name imps false Union_theory_block in
    let () = output_string h ("description: theory file for " ^ thy ^ "\n") in
    let imps = List.fold_left add_article_block "" names in
    let _ = add_union_block "main" imps in
    let () = close_out h in
    ();;

let write_theory_files () =
    let rec write_theories arts =
        match arts with
          [] -> ()
        | art :: arts ->
            let thy = thy_article art in
            let is_thy a = thy_article a = thy in
            let not_thy a = not (is_thy a) in
            let names = map name_article (art :: List.filter is_thy arts) in
            let arts = List.filter not_thy arts in
            let () = write_theory_file thy (rev names) in
            write_theories arts in
    let arts = !articles in
    let () = write_theories arts in
    ();;

(* ------------------------------------------------------------------------- *)
(* Setting up the log files: part 2                                          *)
(* ------------------------------------------------------------------------- *)

let logfile_end () =
    match (!log_state) with
      Active_logging h ->
        let () = close_out h in
        let () = log_state := Ready_logging in
        ()
    | _ -> ();;

let is_auxiliary_thy_article thy =
    let len = String.length thy in
    len >= 4 && String.sub thy (len - 4) 4 = "-aux";;

let logfile thy =
    if is_auxiliary_thy_article thy then ()
    else
      let ()  = logfile_end () in
      match (!log_state) with
        Ready_logging ->
          let () = log_dict_reset () in
          let file = add_article thy in
          let h = open_out file in
          let () = log_state := Active_logging h in
          ()
      | _ -> ();;

let is_logging () =
    match (!log_state) with
      Active_logging _ -> true
    | _ -> false;;

let not_logging () = not (is_logging ());;

let start_logging () =
    match (!log_state) with
      Not_logging ->
        let () = reset_articles () in
        let () = log_state := Ready_logging in
        ()
    | _ -> ();;

let stop_logging () =
    let () = logfile_end () in
    match (!log_state) with
      Ready_logging ->
        let () = write_theory_files () in
        let () = log_state := Not_logging in
        ()
    | _ -> ();;

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

let (log_type_op_save,log_type_op) =
    let proj x = x in
    let log _ _ n =
        let () = log_type_op_name n in
        let () = log_command "typeOp" in
        () in
    log_dict_all proj log;;

let log_type_var n = log_name n;;

let log_type =
    let rec log f ty =
        if is_type ty then
          let (n,l) = dest_type ty in
          (log_type_op n; log_list f l; log_command "opType")
        else
          (log_type_var (dest_vartype ty); log_command "varType") in
    log_dict log;;

let (log_const_save,log_const) =
    let proj x = x in
    let log _ _ n =
        let () = log_const_name n in
        let () = log_command "const" in
        () in
    log_dict_all proj log;;

let log_var =
    let log _ v =
        let (n,ty) = dest_var v in
        let () = log_name n in
        let () = log_type ty in
        let () = log_command "var" in
        () in
    log_dict log;;

let log_term =
    let log log_rec tm =
        if is_const tm then
          let (n,ty) = dest_const tm in
          let () = log_const n in
          let () = log_type ty in
          let () = log_command "constTerm" in
          ()
        else if is_var tm then
          let () = log_var tm in
          let () = log_command "varTerm" in
          ()
        else if is_comb tm then
          let (a,b) = dest_comb tm in
          let () = log_rec a in
          let () = log_rec b in
          let () = log_command "appTerm" in
          ()
        else
          let (v,b) = dest_abs tm in
          let () = log_var v in
          let () = log_rec b in
          let () = log_command "absTerm" in
          () in
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

let log_thm =
    let proj x = dest_thm x in
    let log log_save log_rec th =
        match read_proof th with
          Axiom_proof ->
            let () = log_list log_term (hyp th) in
            let () = log_term (concl th) in
            let () = log_command "axiom" in
            ()
        | Refl_proof tm ->
            let () = log_term tm in
            let () = log_command "refl" in
            ()
        | Trans_proof (th1,th2) ->
            let tm = rator (concl th1) in
            let () = log_term tm in
            let () = log_command "refl" in
            let () = log_rec th2 in
            let () = log_command "appThm" in
            let () = log_rec th1 in
            let () = log_command "eqMp" in
            ()
        | Mk_comb_proof (th1,th2) ->
            let () = log_rec th1 in
            let () = log_rec th2 in
            let () = log_command "appThm" in
            ()
        | Abs_proof (v1,th2) ->
            let () = log_var v1 in
            let () = log_rec th2 in
            let () = log_command "absThm" in
            ()
        | Beta_proof tm ->
            let () = log_term tm in
            let () = log_command "betaConv" in
            ()
        | Assume_proof tm ->
            let () = log_term tm in
            let () = log_command "assume" in
            ()
        | Eq_mp_proof (th1,th2) ->
            let () = log_rec th1 in
            let () = log_rec th2 in
            let () = log_command "eqMp" in
            ()
        | Deduct_antisym_rule_proof (th1,th2) ->
            let () = log_rec th1 in
            let () = log_rec th2 in
            let () = log_command "deductAntisym" in
            ()
        | Inst_type_proof (i1,th2) ->
            let () = log_type_inst i1 in
            let () = log_rec th2 in
            let () = log_command "subst" in
            ()
        | Inst_proof (i1,th2) ->
            let () = log_term_inst i1 in
            let () = log_rec th2 in
            let () = log_command "subst" in
            ()
        | New_basic_definition_proof ->
            let (n,tm) = dest_eq (concl th) in
            let (n,_) = dest_const n in
            let () = log_const_name n in
            let () = log_term tm in
            let () = log_command "defineConst" in
            let i = log_save th in
            let () = log_command "pop" in
            let () = log_const_save n in
            let () = log_command "pop" in
            let () = log_num i in
            let () = log_command "ref" in
            ()
        | New_basic_type_definition_proof
            (is_ar,(ty,(abs,rep),exists_th),(ar,ra)) ->
            let lhs tm = fst (dest_eq tm) in
            let range ty = hd (tl (snd (dest_type ty))) in
            let (absTm,repTm) = dest_comb (lhs (concl ar)) in
            let (repTm,_) = dest_const (rator repTm) in
            let (absTm,newTy) = dest_const absTm in
            let newTy = range newTy in
            let (newTy,tyVars) = dest_type newTy in
            let tyVars = map dest_vartype tyVars in
            let () = log_type_op_name ty in
            let () = log_const_name abs in
            let () = log_const_name rep in
            let () = log_list log_type_var tyVars in
            let () = log_rec exists_th in
            let () = log_command "defineTypeOp" in
            let ra_i = log_save ra in
            let () = log_command "pop" in
            let ar_i = log_save ar in
            let () = log_command "pop" in
            let () = log_const_save repTm in
            let () = log_command "pop" in
            let () = log_const_save absTm in
            let () = log_command "pop" in
            let () = log_type_op_save newTy in
            let () = log_command "pop" in
            let () = log_num (if is_ar then ar_i else ra_i) in
            let () = log_command "ref" in
            () in
    let (_,logd) = log_dict_all proj log in
    logd;;

(* ------------------------------------------------------------------------- *)
(* Exporting theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

let export_thm th =
    let () =
        if not_logging () then () else
        let () = log_thm th in
        let () = log_list log_term (hyp th) in
        let () = log_term (concl th) in
        let () = log_command "thm" in
        let () = log_command "pop" in
        () in
    let () = delete_proof th in
    ();;

let export_aux_thm th = ();;

let export_if_aux_thm th = ();;
