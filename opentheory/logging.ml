(* ========================================================================= *)
(* OPENTHEORY PROOF LOGGING FOR HOL LIGHT                                    *)
(* Copyright (c) 2009 Joe Hurd, distributed under the GNU GPL version 2      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Tracking definitions.                                                     *)
(* ------------------------------------------------------------------------- *)

type type_op_definition =
     Type_op_definition of (thm * (thm * thm));;

type const_definition =
     Const_definition of thm
   | Abs_type_definition of string
   | Rep_type_definition of string;;

let (peek_type_op_definition,
     add_type_op_definition,
     delete_type_op_definition,
     list_type_op_definition) =
    let the_defs = ref ([] : (string * type_op_definition) list) in
    let mem ty = List.mem_assoc ty (!the_defs) in
    let peek ty = if mem ty then Some (List.assoc ty (!the_defs)) else None in
    let add ty def =
        if mem ty then failwith "redefinition of type op" else
        let () = the_defs := (ty,def) :: !the_defs in
        () in
    let delete tys =
        let pred (ty,_) = not (List.mem ty tys) in
        let () = the_defs := List.filter pred (!the_defs) in
        () in
    let list () = !the_defs in
    (peek,add,delete,list);;

let (peek_const_definition,
     add_const_definition,
     delete_const_definition,
     list_const_definition) =
    let the_defs = ref ([] : (string * const_definition) list) in
    let mem c = List.mem_assoc c (!the_defs) in
    let peek c = if mem c then Some (List.assoc c (!the_defs)) else None in
    let add c def =
        if mem c then failwith "redefinition of const" else
        let () = the_defs := (c,def) :: !the_defs in
        () in
    let delete cs =
        let pred (c,_) = not (List.mem c cs) in
        let () = the_defs := List.filter pred (!the_defs) in
        () in
    let list () = !the_defs in
    (peek,add,delete,list);;

let new_basic_definition tm =
    let th = new_basic_definition tm in
    let (c,_) = dest_eq (concl th) in
    let (c,_) = dest_const c in
    let () = add_const_definition c (Const_definition th) in
    th;;

let new_basic_type_definition ty (abs,rep) exists_th =
    let ar_ra = new_basic_type_definition ty (abs,rep) exists_th in
    let () = add_type_op_definition ty (Type_op_definition (exists_th,ar_ra)) in
    let () = add_const_definition abs (Abs_type_definition ty) in
    let () = add_const_definition rep (Rep_type_definition ty) in
    ar_ra;;

(* ------------------------------------------------------------------------- *)
(* Setting up the log files: part 1                                          *)
(* ------------------------------------------------------------------------- *)

type log_state =
     Not_logging
   | Ready_logging
   | Active_logging of out_channel;;

let log_env () =
    try (let r = Sys.getenv "OPENTHEORY_LOGGING" in
         if r = "0" then 0 else 2)
    with Not_found -> 1;;

let log_state =
    let initial_log_state =
        let l = log_env () in
        if l < 2 then Not_logging else
        let () = report "Logging the OpenTheory standard library" in
        Ready_logging in
    ref initial_log_state;;

let log_raw s =
    match (!log_state) with
      Active_logging h -> output_string h (s ^ "\n")
    | _ -> ();;

(* ------------------------------------------------------------------------- *)
(* Logging primitive types                                                   *)
(* ------------------------------------------------------------------------- *)

type opentheory_object =
     Type_op_object of string
   | Type_object of hol_type
   | Const_object of string
   | Var_object of term
   | Term_object of term
   | Thm_object of thm
   | List_object of opentheory_object list
   | Name_object of string
   | Num_object of int;;

let log_num n = log_raw (string_of_int n);;

let log_name s = log_raw ("\"" ^ String.escaped s ^ "\"");;

let (log_type_op_name,log_const_name) =
    let namespace = "HOLLight" in
    let mk_namespace_name s = namespace ^ "." ^ s in
    let log_namespace_name s = log_name (mk_namespace_name s) in
    (log_namespace_name,log_namespace_name);;

let log_command s = log_raw s;;

let log_nil () = log_command "nil";;

let log_list (log : 'a -> unit) =
    let rec logl l =
        match l with
          [] ->
          let () = log_nil () in
          ()
        | h :: t ->
          let () = log h in
          let () = logl t in
          let () = log_command "cons" in
          () in
    logl;;

let log_unit () = log_nil ();;

let log_sing (log_a : 'a -> unit) a =
    let () = log_a a in
    let () = log_nil () in
    let () = log_command "cons" in
    ();;

let log_pair (log_a : 'a -> unit) (log_b : 'b -> unit) (a,b) =
    let () = log_a a in
    let () = log_sing log_b b in
    let () = log_command "cons" in
    ();;

let log_type_var n = log_name n;;

(* ------------------------------------------------------------------------- *)
(* The dictionary.                                                           *)
(* ------------------------------------------------------------------------- *)

let (log_reset,log_term,log_thm,log_clear) =
    let (reset_key,next_key) =
        let key = ref 0 in
        let reset () = key := 0 in
        let next () = let k = !key in (key := k + 1; k) in
        (reset,next) in
    let (reset_dict,peek_dict,save_dict) =
        let hashtbl = Hashtbl.create 10000 in
        let reset () = Hashtbl.clear hashtbl in
        let mem x = Hashtbl.mem hashtbl x in
        let peek x = if mem x then Some (Hashtbl.find hashtbl x) else None in
        let save x =
            match (peek x) with
              Some k -> k
            | None ->
                let k = next_key () in
                let () = Hashtbl.add hashtbl x k in
                let () = log_num k in
                let () = log_command "def" in
                k in
        (reset,peek,save) in
    let reset () =
        let () = reset_key () in
        let () = reset_dict () in
        () in
    let clear () =
        let rec clear_up_to k =
            if k = 0 then () else
            let k = k - 1 in
            let () = log_num k in
            let () = log_command "remove" in
            let () = log_command "pop" in
            clear_up_to k in
        let () = clear_up_to (next_key ()) in
        let () = reset () in
        () in
    let saved ob =
        match (peek_dict ob) with
          Some k ->
            let () = log_num k in
            let () = log_command "ref" in
            true
        | None ->
            false in
    let rec log_type_op_def (exists_th,(ar,ra)) =
        let lhs tm = fst (dest_eq tm) in
        let range ty = hd (tl (snd (dest_type ty))) in
        let (absTm,repTm) = dest_comb (lhs (concl ar)) in
        let (repTm,_) = dest_const (rator repTm) in
        let (absTm,newTy) = dest_const absTm in
        let newTy = range newTy in
        let (newTy,tyVars) = dest_type newTy in
        let tyVars = map dest_vartype tyVars in
        let () = log_type_op_name newTy in
        let () = log_const_name absTm in
        let () = log_const_name repTm in
        let () = log_list log_type_var tyVars in
        let () = log_thm exists_th in
        let () = log_command "defineTypeOp" in
        let ra_k = save_dict (Thm_object ra) in
        let () = log_command "pop" in
        let ar_k = save_dict (Thm_object ar) in
        let () = log_command "pop" in
        let rep_k = save_dict (Const_object repTm) in
        let () = log_command "pop" in
        let abs_k = save_dict (Const_object absTm) in
        let () = log_command "pop" in
        let ty_k = save_dict (Type_op_object newTy) in
        let () = log_command "pop" in
        (ty_k,abs_k,rep_k,ar_k,ra_k)
    and log_type_op ty =
        let ob = Type_op_object ty in
        if saved ob then () else
        match (peek_type_op_definition ty) with
          Some (Type_op_definition tydef) ->
            let (k,_,_,_,_) = log_type_op_def tydef in
            let () = log_num k in
            let () = log_command "ref" in
            ()
        | None ->
            let () = log_type_op_name ty in
            let () = log_command "typeOp" in
            let _ = save_dict ob in
            ()
    and log_type ty =
        let ob = Type_object ty in
        if saved ob then () else
        let () =
            if is_type ty then
              let (n,l) = dest_type ty in
              let () = log_type_op n in
              let () = log_list log_type l in
              let () = log_command "opType" in
              ()
            else
              let () = log_type_var (dest_vartype ty) in
              let () = log_command "varType" in
              () in
        let _ = save_dict ob in
        ()
    and log_const_def th =
        let (c,tm) = dest_eq (concl th) in
        let (c,_) = dest_const c in
        let () = log_const_name c in
        let () = log_term tm in
        let () = log_command "defineConst" in
        let th_k = save_dict (Thm_object th) in
        let () = log_command "pop" in
        let c_k = save_dict (Const_object c) in
        let () = log_command "pop" in
        (c_k,th_k)
    and log_const c =
        let ob = Const_object c in
        if saved ob then () else
        match (peek_const_definition c) with
          None ->
            let () = log_const_name c in
            let () = log_command "const" in
            let _ = save_dict ob in
            ()
        | Some def ->
            match def with
              Const_definition cdef ->
                let (k,_) = log_const_def cdef in
                let () = log_num k in
                let () = log_command "ref" in
                ()
            | Abs_type_definition ty ->
              (match (peek_type_op_definition ty) with
                 Some (Type_op_definition tydef) ->
                   let (_,k,_,_,_) = log_type_op_def tydef in
                   let () = log_num k in
                   let () = log_command "ref" in
                   ()
               | None ->
                 failwith ("abs const out of type op definition scope: " ^ ty))
            | Rep_type_definition ty ->
              (match (peek_type_op_definition ty) with
                 Some (Type_op_definition tydef) ->
                   let (_,_,k,_,_) = log_type_op_def tydef in
                   let () = log_num k in
                   let () = log_command "ref" in
                   ()
               | None ->
                 failwith ("rep const out of type op definition scope: " ^ ty))
    and log_var v =
        let ob = Var_object v in
        if saved ob then () else
        let (n,ty) = dest_var v in
        let () = log_name n in
        let () = log_type ty in
        let () = log_command "var" in
        let _ = save_dict ob in
        ()
    and log_term tm =
        let ob = Term_object tm in
        if saved ob then () else
        let () =
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
              let () = log_term a in
              let () = log_term b in
              let () = log_command "appTerm" in
              ()
            else
              let (v,b) = dest_abs tm in
              let () = log_var v in
              let () = log_term b in
              let () = log_command "absTerm" in
              () in
        let _ = save_dict ob in
        ()
    and log_inst ins =
        log_pair
          (log_list (log_pair log_type_var log_type))
          (log_list (log_pair log_var log_term))
          ins
    and log_type_inst tyins =
        let conv (ty,v) = (dest_vartype v, ty) in
        let ins = (map conv tyins, []) in
        log_inst ins
    and log_term_inst tmins =
        let conv (tm,v) = (v,tm) in
        let ins = ([], map conv tmins) in
        log_inst ins
    and log_thm th =
        let ob = Thm_object th in
        if saved ob then () else
        let () =
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
                let () = log_thm th2 in
                let () = log_command "appThm" in
                let () = log_thm th1 in
                let () = log_command "eqMp" in
                ()
            | Mk_comb_proof (th1,th2) ->
                let () = log_thm th1 in
                let () = log_thm th2 in
                let () = log_command "appThm" in
                ()
            | Abs_proof (v1,th2) ->
                let () = log_var v1 in
                let () = log_thm th2 in
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
                let () = log_thm th1 in
                let () = log_thm th2 in
                let () = log_command "eqMp" in
                ()
            | Deduct_antisym_rule_proof (th1,th2) ->
                let () = log_thm th1 in
                let () = log_thm th2 in
                let () = log_command "deductAntisym" in
                ()
            | Inst_type_proof (i1,th2) ->
                let () = log_type_inst i1 in
                let () = log_thm th2 in
                let () = log_command "subst" in
                ()
            | Inst_proof (i1,th2) ->
                let () = log_term_inst i1 in
                let () = log_thm th2 in
                let () = log_command "subst" in
                ()
            | New_basic_definition_proof c ->
                (match (peek_const_definition c) with
                   Some (Const_definition cdef) ->
                     let (_,k) = log_const_def cdef in
                     let () = log_num k in
                     let () = log_command "ref" in
                     ()
                 | _ ->
                   failwith ("thm out of const definition scope: " ^ c))
            | New_basic_type_definition_proof (is_ar,ty) ->
                (match (peek_type_op_definition ty) with
                   Some (Type_op_definition tydef) ->
                     let (_,_,_,ar_k,ra_k) = log_type_op_def tydef in
                     let () = log_num (if is_ar then ar_k else ra_k) in
                     let () = log_command "ref" in
                     ()
                 | _ ->
                   failwith ("thm out of type op definition scope: " ^ ty)) in
        let _ = save_dict ob in
        () in
    (reset,log_term,log_thm,clear);;

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
            let c = String.length l = 0 || String.get l 0 = '#' in
            let acc = if c then acc else acc ^ "  interpret: " ^ l ^ "\n" in
            read acc
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
        let () = log_clear () in
        let () = close_out h in
        let () = log_state := Ready_logging in
        ()
    | _ -> ();;

let logfile thy =
    let () = logfile_end () in
    match (!log_state) with
      Ready_logging ->
        let () = log_reset () in
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
        let new_log_state =
            let l = log_env () in
            if l = 0 then Not_logging else Ready_logging in
        let () = log_state := new_log_state in
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

let start_logging_to h =
  match (!log_state) with
    Not_logging ->
      let () = log_reset () in
      let () = log_state := Active_logging h in
      ()
    | _ -> ();;

let stop_logging_to () =
  match (!log_state) with
    Active_logging h ->
      let () = close_out h in
      let () = log_state := Not_logging in
      ()
    | _ -> ();;

(* ------------------------------------------------------------------------- *)
(* Exporting theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

let thm_type_ops =
    let rec type_ops_in_types acc tys =
        match tys with
          [] -> acc
        | ty :: tys ->
          if is_vartype ty then type_ops_in_types acc tys
          else
            let (t,l) = dest_type ty in
            let acc = if List.mem t acc then acc else t :: acc in
            type_ops_in_types acc (l @ tys) in
    let rec type_ops_in_terms acc tms =
        match tms with
          [] -> acc
        | tm :: tms ->
          if is_var tm then
            let (_,ty) = dest_var tm in
            let acc = type_ops_in_types acc [ty] in
            type_ops_in_terms acc tms
          else if is_const tm then
            let (_,ty) = dest_const tm in
            let acc = type_ops_in_types acc [ty] in
            type_ops_in_terms acc tms
          else if is_comb tm then
            let (f,x) = dest_comb tm in
            type_ops_in_terms acc (f :: x :: tms)
          else
            let (v,b) = dest_abs tm in
            type_ops_in_terms acc (v :: b :: tms) in
    fun th -> type_ops_in_terms [] (concl th :: hyp th);;

let thm_consts =
    let rec consts_in_terms acc tms =
        match tms with
          [] -> acc
        | tm :: tms ->
          if is_var tm then consts_in_terms acc tms
          else if is_const tm then
            let (c,_) = dest_const tm in
            let acc = if List.mem c acc then acc else c :: acc in
            consts_in_terms acc tms
          else if is_comb tm then
            let (f,x) = dest_comb tm in
            consts_in_terms acc (f :: x :: tms)
          else
            let (_,b) = dest_abs tm in
            consts_in_terms acc (b :: tms) in
    fun th -> consts_in_terms [] (concl th :: hyp th);;

let export_thm th =
    let () =
        if not_logging () then () else
        let () = log_thm th in
        let () = log_list log_term (hyp th) in
        let () = log_term (concl th) in
        let () = log_command "thm" in
        () in
    let () = delete_proof th in
    let () = delete_type_op_definition (thm_type_ops th) in
    let () = delete_const_definition (thm_consts th) in
    ();;

(* ------------------------------------------------------------------------- *)
(* Haskellizing type variables.                                              *)
(* ------------------------------------------------------------------------- *)

let haskellize_thm =
    let mk_type_map acc v =
        let s = dest_vartype v in
        let s' = String.lowercase s in
        if s = s' then acc else (mk_vartype s', v) :: acc in
    fun th ->
        let vs = type_vars_in_term (concl th) in
        if length vs = 0 then th else
        INST_TYPE (List.fold_left mk_type_map [] vs) th;;

let export_haskell_thm th = export_thm (haskellize_thm th);;

(* ------------------------------------------------------------------------- *)
(* Special processing for axioms.                                            *)
(* ------------------------------------------------------------------------- *)

(***
let normalize_axiom =
    let name =
        let base = Char.code 'a' in
        let rec f n =
            if n = 0 then "" else
            let n = n - 1 in
            f (n / 26) ^ (String.make 1 (Char.chr (base + (n mod 26)))) in
        f in
    let my_find p l =
        (try (Some (List.find p l))
         with Not_found -> None) in
    let rec check tm acc n =
        match (my_find (aconv tm) acc) with
          Some tm -> (tm,acc,n)
        | None -> let (tm,acc,n) = rename tm acc n in (tm, tm :: acc, n)
    and rename tm acc n =
        if is_abs tm then
          let (v,tm) = dest_abs tm in
          let n = n + 1 in
          let w = mk_var (name n, snd (dest_var v)) in
          let tm = vsubst [(w,v)] tm in
          let (tm,acc,n) = check tm acc n in
          (mk_abs (w,tm), acc, n)
        else if is_comb tm then
          let (f,x) = dest_comb tm in
          let (f,acc,n) = check f acc n in
          let (x,acc,n) = check x acc n in
          (mk_comb (f,x), acc, n)
        else
          (tm,acc,n) in
    fun tm ->
        let (tm,_,_) = check tm [] 0 in
        tm;;

let ocaml_print_axiom =
    let thing_ops prefix =
        let pr n = prefix ^ string_of_int n in
        let empty = (-1,[],"") in
        let add x d (k,xs,acc) =
            let k = k + 1 in
            let xs = x :: xs in
            let s = pr k in
            let acc = acc ^ "      let " ^ s ^ " = " ^ d ^ " in\n" in
            (s,(k,xs,acc)) in
        let peek x =
            let rec pk n xs =
                match xs with
                  [] -> None
                | x' :: xs ->
                  if x = x' then Some (pr n) else
                  pk (n - 1) xs in
            fun (k,xs,_) -> pk k xs in
        (empty,add,peek) in
    let type_empty,type_add,type_peek = thing_ops "ty" in
    let term_empty,term_add,term_peek = thing_ops "tm" in
    let rec print_ty ty tys =
        match type_peek ty tys with
          None -> construct_ty ty tys
        | Some s -> (s,tys)
    and construct_ty ty tys =
        if is_fun_ty ty then
          let (f,x) = dest_fun_ty ty in
          let (fs,tys) = print_ty f tys in
          let (xs,tys) = print_ty x tys in
          let d = "mk_fun_ty " ^ fs ^ " " ^ xs in
          type_add ty d tys
        else if is_vartype ty then
          let s = dest_vartype ty in
          let d = "mk_vartype \"" ^ s ^ "\"" in
          type_add ty d tys
        else
          let (s,l) = dest_type ty in
          let () =
              (match l with
                 [] -> ()
               | _ -> failwith "non-nullary type operator") in
          let d = "mk_type (\"" ^ s ^ "\",[])" in
          type_add ty d tys in
    let rec print_tm tm tms tys =
        match term_peek tm tms with
          None -> construct_tm tm tms tys
        | Some s -> (s,tms,tys)
    and construct_tm tm tms tys =
        if is_abs tm then
          let (v,b) = dest_abs tm in
          let (vs,tms,tys) = print_tm v tms tys in
          let (bs,tms,tys) = print_tm b tms tys in
          let d = "mk_abs (" ^ vs ^ "," ^ bs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,tys)
        else if is_eq tm then
          let (f,x) = dest_eq tm in
          let (fs,tms,tys) = print_tm f tms tys in
          let (xs,tms,tys) = print_tm x tms tys in
          let d = "mk_eq (" ^ fs ^ "," ^ xs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,tys)
        else if is_comb tm then
          let (f,x) = dest_comb tm in
          let (fs,tms,tys) = print_tm f tms tys in
          let (xs,tms,tys) = print_tm x tms tys in
          let d = "mk_comb (" ^ fs ^ "," ^ xs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,tys)
        else if is_var tm then
          let (n,t) = dest_var tm in
          let (ts,tys) = print_ty t tys in
          let d = "mk_var (\"" ^ n ^ "\"," ^ ts ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,tys)
        else if tm = `(@):(A->bool)->A` then
          let d = "mk_const (\"@\",[])" in
          let (s,tms) = term_add tm d tms in
          (s,tms,tys)
        else
          failwith "unknown constant" in
    fun tm ->
      let (s,(_,_,tms),(_,_,tys)) = print_tm tm term_empty type_empty in
      let () = print (tys ^ tms ^ "      " ^ s ^ "\n") in
      ();;

let opentheory_print_axiom =
    let thing_ops prefix =
        let pr n = prefix ^ string_of_int n in
        let empty = (-1,[],"") in
        let add x d (k,xs,acc) =
            let k = k + 1 in
            let xs = x :: xs in
            let s = pr k in
            let acc = acc ^ "      val " ^ s ^ " = " ^ d ^ "\n" in
            (s,(k,xs,acc)) in
        let peek x =
            let rec pk n xs =
                match xs with
                  [] -> None
                | x' :: xs ->
                  if x = x' then Some (pr n) else
                  pk (n - 1) xs in
            fun (k,xs,_) -> pk k xs in
        (empty,add,peek) in
    let type_empty,type_add,type_peek = thing_ops "ty" in
    let var_empty,var_add,var_peek = thing_ops "v" in
    let term_empty,term_add,term_peek = thing_ops "tm" in
    let rec print_ty ty tys =
        match type_peek ty tys with
          None -> construct_ty ty tys
        | Some s -> (s,tys)
    and construct_ty ty tys =
        if is_fun_ty ty then
          let (f,x) = dest_fun_ty ty in
          let (fs,tys) = print_ty f tys in
          let (xs,tys) = print_ty x tys in
          let d = "Type.mkFun (" ^ fs ^ "," ^ xs ^ ")" in
          type_add ty d tys
        else if is_vartype ty then
          let s = dest_vartype ty in
          let d = "Type.mkVar (Name.mkGlobal \"" ^ s ^ "\")" in
          type_add ty d tys
        else if ty = bool_ty then
          let d = "Type.bool" in
          type_add ty d tys
        else if ty = `:ind` then
          let d = "Type.ind" in
          type_add ty d tys
        else
          failwith "unknown type operator" in
    let rec print_var v vars tys =
        match var_peek v vars with
          None -> construct_var v vars tys
        | Some s -> (s,vars,tys)
    and construct_var v vars tys =
        let (n,t) = dest_var v in
        let (ts,tys) = print_ty t tys in
        let d = "Var.mk (Name.mkGlobal \"" ^ n ^ "\", " ^ ts ^ ")" in
        let (s,vars) = var_add v d vars in
        (s,vars,tys) in
    let rec print_tm tm tms vars tys =
        match term_peek tm tms with
          None -> construct_tm tm tms vars tys
        | Some s -> (s,tms,vars,tys)
    and construct_tm tm tms vars tys =
        if is_abs tm then
          let (v,b) = dest_abs tm in
          let (vs,vars,tys) = print_var v vars tys in
          let (bs,tms,vars,tys) = print_tm b tms vars tys in
          let d = "mkAbs (" ^ vs ^ "," ^ bs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,vars,tys)
        else if is_eq tm then
          let (f,x) = dest_eq tm in
          let (fs,tms,vars,tys) = print_tm f tms vars tys in
          let (xs,tms,vars,tys) = print_tm x tms vars tys in
          let d = "mkEq (" ^ fs ^ "," ^ xs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,vars,tys)
        else if is_comb tm then
          let (f,x) = dest_comb tm in
          let (fs,tms,vars,tys) = print_tm f tms vars tys in
          let (xs,tms,vars,tys) = print_tm x tms vars tys in
          let d = "mkApp (" ^ fs ^ "," ^ xs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,vars,tys)
        else if is_var tm then
          let (vs,vars,tys) = print_var tm vars tys in
          let d = "mkVar " ^ vs in
          let (s,tms) = term_add tm d tms in
          (s,tms,vars,tys)
        else
          let (n,t) = dest_const tm in
          if n <> "@" then failwith "unknown constant" else
          let (_,t) = dest_fun_ty t in
          let (ts,tys) = print_ty t tys in
          let d = "mkSelect " ^ ts in
          let (s,tms) = term_add tm d tms in
          (s,tms,vars,tys) in
    fun tm ->
      let (s,(_,_,tms),(_,_,vars),(_,_,tys)) =
          print_tm tm term_empty var_empty type_empty in
      let () = print ("    let\n" ^ tys ^ vars ^ tms ^ "    in\n" ^
                      "      " ^ s ^ "\n" ^ "    end\n") in
      ();;
***)
