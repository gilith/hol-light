(* ========================================================================= *)
(* OPENTHEORY ARTICLE READING FOR HOL LIGHT                                  *)
(* Ramana Kumar, Joe Leslie-Hurd and Robert White                            *)
(* ========================================================================= *)

#load "unix.cma";;

module Int_map = Map.Make (struct type t = int let compare = compare end);;

module Import =
struct

(* ------------------------------------------------------------------------- *)
(* Constants.                                                                *)
(* ------------------------------------------------------------------------- *)

let import_directory = "opentheory/import";;

(* ------------------------------------------------------------------------- *)
(* Utility functions.                                                        *)
(* ------------------------------------------------------------------------- *)

let replace x = Str.global_replace (Str.regexp_string x);;

let open_command cmd =
    let (fd_in,fd_out) = Unix.pipe () in
    match Unix.fork () with
      0 -> let () = Unix.dup2 fd_out Unix.stdout in
           let () = Unix.close fd_out in
           let () = Unix.close fd_in in
           let () = Unix.execv "/bin/sh" [| "/bin/sh"; "-c"; cmd |] in
           failwith "returned from execv"
    | _ -> let () = Unix.close fd_out in
           let h = Unix.in_channel_of_descr fd_in in
           let () = set_binary_mode_in h false in
           h;;

let read_all_lines h =
    let rec loop l =
        try loop (input_line h :: l)
        with End_of_file -> l in
    rev (loop []);;

let read_from_command cmd =
    let h = open_command cmd in
    let l = read_all_lines h in
    let () = close_in h in
    l;;

(* ------------------------------------------------------------------------- *)
(* Interface to the opentheory tool.                                         *)
(* ------------------------------------------------------------------------- *)

let list_theories exp =
    let qexp = "'" ^ exp ^ "'" in
    let cmd = "opentheory list --dependency-order --format NAME " ^ qexp in
    read_from_command cmd;;

let required_theories thy =
    let rsubs = "(Requires & Subtheories)" in
    let reqs = "((Requires | Requires " ^ rsubs ^ ") - Subtheories) " ^ thy in
    let subs = rsubs ^ " " ^ thy in
    (list_theories reqs, list_theories subs);;

let theory_article thy =
    let cmd = "opentheory info --clear-local-names --article " ^ thy in
    open_command cmd;;

let theory_directory thy =
    let cmd = "opentheory info --directory " ^ thy in
    match read_from_command cmd with
      [dir] -> dir
    | _ -> failwith ("theory_directory: strange output for theory " ^ thy);;

(* ------------------------------------------------------------------------- *)
(* Alpha conversion.                                                         *)
(* ------------------------------------------------------------------------- *)

let ALPHA tm1 tm2 =
  try TRANS (REFL tm1) (REFL tm2)
  with Failure _ -> failwith "Import.ALPHA";;

let alpha_rule =
    let alpha_hyp th h =
        let hs' = hyp th in
        if mem h hs' then th else
        let th0 = ASSUME h in
        let th1 = DEDUCT_ANTISYM_RULE th0 th in
        EQ_MP th1 th0 in
    fun s th ->
    let (hs,c) = Sequent.dest s in
    let c' = concl th in
    let th = if c = c' then th else EQ_MP (ALPHA c' c) th in
    List.fold_left alpha_hyp th hs;;

(* ------------------------------------------------------------------------- *)
(* Miscellaneous syntax transformations to convert OpenTheory theorems into  *)
(* native HOL Light theorems.                                                *)
(* ------------------------------------------------------------------------- *)

let the_go_native_conv = ref REFL;;

let go_native_conv tm =
    let th = (!the_go_native_conv) tm in
    let (_,tm') = dest_eq (concl th) in
    if tm' = tm then None else Some th;;

let go_native_term tm =
    match go_native_conv tm with
      None -> (tm,None)
    | Some th -> let (_,tm') = dest_eq (concl th) in (tm', Some th);;

let go_native_term_list =
    let f tm ths =
        let (tm,tho) = go_native_term tm in
        let ths =
            match tho with
              None -> ths
            | Some th -> th :: ths in
        (tm,ths) in
    fun tms -> Object.maps f tms [];;

let (go_native_sequent,go_native_thm) =
    let sequent_convert s =
        let (h,c) = Sequent.dest s in
        let (h,aths) = go_native_term_list h in
        let (c,cth) = go_native_term c in
        let cvt = (aths,cth) in
        let seq =
            match cvt with
              ([],None) -> s
            | _ -> Sequent.mk (h,c) in
        (seq,cvt) in
    let reverse_convert (aths,cth) =
        let aths = map Object.SYM aths in
        let cth =
            match cth with
              Some th -> Some (Object.SYM th)
            | None -> None in
        (aths,cth) in
    let convert_thm =
        let convert_asm ath th =
            let ath = Object.SYM ath in
            let (asm,_) = dest_eq (concl ath) in
            Object.PROVE_HYP (EQ_MP ath (ASSUME asm)) th in
        let convert_concl cth th =
            match cth with
              Some eq -> EQ_MP eq th
            | None -> th in
        fun (aths,cth) th ->
        convert_concl cth (rev_itlist convert_asm aths th) in
    let go_sequent s =
        let (s,cvt) = sequent_convert s in
        (s, convert_thm (reverse_convert cvt)) in
    let go_thm th =
        let (_,cvt) = sequent_convert (Sequent.from_thm th) in
        convert_thm cvt th in
    (go_sequent,go_thm);;

(* ------------------------------------------------------------------------- *)
(* Fresh names for constants and type operators that are local to a theory.  *)
(* ------------------------------------------------------------------------- *)

let (new_theory_const_name,new_theory_type_op_name) =
    let new_name f thy =
        let r = ref 0 in
        let rec go () =
            let i = !r in
            let () = r := i + 1 in
            let n = thy ^ "_" ^ string_of_int i in
            if can f n then go () else n in
        go in
    (new_name get_const_type, new_name get_type_arity);;

(* ------------------------------------------------------------------------- *)
(* A type of import contexts.                                                *)
(* ------------------------------------------------------------------------- *)

type context =
    {const_context : Name.t -> string;
     type_op_context : Name.t -> string;
     axiom_context : Sequent.t -> thm};;

let theory_context thy =
    let new_const_name = new_theory_const_name thy in
    let new_type_op_name = new_theory_type_op_name thy in
    fun int thms ->
    let const_context n =
        if Name.is_empty n then new_const_name () else
        let n =
            match Interpretation.import_const int n with
              [] -> n
            | n :: _ -> n in
        match Name.dest_const n with
          Some s -> s
        | None -> failwith ("unknown constant " ^ Name.to_string n) in
    let type_op_context n =
        if Name.is_empty n then new_type_op_name () else
        let n =
            match Interpretation.import_type_op int n with
              [] -> n
            | n :: _ -> n in
        match Name.dest_type_op n with
          Some s -> s
        | None -> failwith ("unknown type operator " ^ Name.to_string n) in
    let axiom_context s =
        match peek_sequent_map thms s with
          Some (th,_) -> th
        | None -> failwith ("unknown assumption:\n" ^ Sequent.to_string s) in
    {const_context = const_context;
     type_op_context = type_op_context;
     axiom_context = axiom_context};;

let default_context =
    let ctxt =
        let ctxt_fn = theory_context "" in
        fun () -> ctxt_fn (!the_interpretation) (!the_exported_thms) in
    let const_context n = (ctxt ()).const_context n in
    let type_op_context n = (ctxt ()).type_op_context n in
    let axiom_context s = (ctxt ()).axiom_context s in
    {const_context = const_context;
     type_op_context = type_op_context;
     axiom_context = axiom_context};;

(* ------------------------------------------------------------------------- *)
(* A type of import states.                                                  *)
(* ------------------------------------------------------------------------- *)

type state =
    {stack : Object.t list;
     dict : Object.t Int_map.t;
     asms : thm list;
     thms : thm list};;

let is_digit = function
  | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> true
  | _ -> false;;

let initial_state =
    {stack = [];
     dict = Int_map.empty;
     asms = [];
     thms = []};;

let process_num state cmd =
    let {stack = stack; dict = dict; asms = asms; thms = thms} = state in
    let obj = Object.Num_object (int_of_string cmd) in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms};;

let process_name state cmd =
    match Name.from_string cmd with
      Some n ->
      let {stack = stack; dict = dict; asms = asms; thms = thms} = state in
      let obj = Object.Name_object n in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | None ->
      failwith ("bad name format in article: " ^ cmd);;

let process_command context state cmd =
    if String.length cmd = 0 then state else
    let c = String.get cmd 0 in
    if c = '#' then state else
    if c = '\"' then process_name state cmd else
    if is_digit c then process_num state cmd else
    let {stack = stack; dict = dict; asms = asms; thms = thms} = state in
    match (cmd,stack) with
      ("absTerm", objB :: objV :: stack) ->
      let obj = Object.mkAbsTerm objV objB in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("absThm", objB :: objV :: stack) ->
      let obj = Object.mkAbsThm objV objB in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("appTerm", objX :: objF :: stack) ->
      let obj = Object.mkAppTerm objF objX in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("appThm", objX :: objF :: stack) ->
      let obj = Object.mkAppThm objF objX in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("assume", objT :: stack) ->
      let obj = Object.mkAssume objT in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("axiom", objC :: objH :: stack) ->
      let (s,r) = go_native_sequent (Object.dest_sequent (objH,objC)) in
      let th = context.axiom_context s in
      let obj = Object.mk_thm (r th) in
      let stack = obj :: stack in
      let asms = th :: asms in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("betaConv", objT :: stack) ->
      let obj = Object.mkBetaConv objT in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("cons", objT :: objH :: stack) ->
      let obj = Object.mk_cons objH objT in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("const", objN :: stack) ->
      let obj = Object.mkConst (context.const_context) objN in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("constTerm", objT :: objC :: stack) ->
      let obj = Object.mkConstTerm objC objT in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("deductAntisym", objU :: objT :: stack) ->
      let obj = Object.mkDeductAntisym objT objU in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("def", Object.Num_object k :: (obj :: _ as stack)) ->
      let dict = Int_map.add k obj dict in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("defineConst", objT :: objN :: stack) ->
      let (objC,objD) = Object.mkDefineConst (context.const_context) objN objT in
      let stack = objD :: objC :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("defineConstList", objT :: objL :: stack) ->
      let (objC,objD) =
          Object.mkDefineConstList (context.const_context) objL objT in
      let stack = objD :: objC :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("defineTypeOp", objT :: objL :: objR :: objA :: objN :: stack) ->
      let (objT,objA,objR,objRA,objAR) =
          Object.mkDefineTypeOp
            (context.type_op_context) (context.const_context)
            objN objA objR objL objT in
      let stack = objAR :: objRA :: objR :: objA :: objT :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("eqMp", objU :: objT :: stack) ->
      let obj = Object.mkEqMp objT objU in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("hdTl", objL :: stack) ->
      let (objH,objT) = Object.mkHdTl objL in
      let stack = objT :: objH :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("nil", _) ->
      let stack = Object.mk_nil :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("opType", objL :: objT :: stack) ->
      let obj = Object.mkOpType objT objL in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("pop", _ :: stack) ->
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("pragma", _ :: stack) ->
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("proveHyp", objU :: objT :: stack) ->
      let obj = Object.mkProveHyp objT objU in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("ref", Object.Num_object k :: stack) ->
      let obj = Int_map.find k dict in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("refl", objT :: stack) ->
      let obj = Object.mkRefl objT in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("remove", Object.Num_object k :: stack) ->
      let obj = Int_map.find k dict in
      let dict = Int_map.remove k dict in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("subst", objT :: objS :: stack) ->
      let obj = Object.mkSubst objS objT in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("sym", objU :: stack) ->
      let obj = Object.mkSym objU in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("thm", objC :: objH :: objT :: stack) ->
      let s = Object.dest_sequent (objH,objC) in
      let th = go_native_thm (alpha_rule s (Object.dest_thm objT)) in
      let thms = th :: thms in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("trans", objU :: objT :: stack) ->
      let obj = Object.mkTrans objT objU in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("typeOp", objN :: stack) ->
      let obj = Object.mkTypeOp (context.type_op_context) objN in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("var", objT :: objN :: stack) ->
      let obj = Object.mkVar objN objT in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("varTerm", objV :: stack) ->
      let obj = Object.mkVarTerm objV in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("varType", objN :: stack) ->
      let obj = Object.mkVarType objN in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | ("version", _ :: stack) ->
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | _ -> failwith ("unhandled article line: " ^ cmd);;

(* ------------------------------------------------------------------------- *)
(* Importing articles.                                                       *)
(* ------------------------------------------------------------------------- *)

let read_article context name h =
    let rec loop line_number state =
        try let line = input_line h in
            let state =
                try process_command context state line
                with Failure f ->
                     failwith ("in " ^ name ^ " at line " ^
                               string_of_int line_number ^ ": " ^ line ^
                               "\nstack = " ^
                               Object.list_to_string (state.stack) ^
                               "\n" ^ f) in
            loop (line_number + 1) state
        with End_of_file -> state in
    let {stack = _; dict = _; asms = asms; thms = thms} =
        loop 1 initial_state in
    (rev asms, rev thms);;

let import_article filename =
    let h = open_in filename in
    let c = default_context in
    let n = "article " ^ filename in
    let thy = read_article c n h in
    let () = close_in h in
    thy;;

(* ------------------------------------------------------------------------- *)
(* Theory interpretations.                                                   *)
(* ------------------------------------------------------------------------- *)

let theory_interpretation thy =
    let rec first_existing files =
        match files with
          [] -> failwith ("no interpretation found for theory " ^ thy)
        | file :: files ->
          if Sys.file_exists file then file else first_existing files in
    let local_override_file = Filename.concat import_directory (thy ^ ".int") in
    let theory_file = Filename.concat (theory_directory thy) "hol-light.int" in
    first_existing [local_override_file; theory_file];;

(* ------------------------------------------------------------------------- *)
(* The set of imported theories.                                             *)
(* ------------------------------------------------------------------------- *)

let the_imported_theories = ref ([] : Theory.t list);;

let imported_theories () = !the_imported_theories;;

let peek_imported_theory n =
    let pred thy = Theory.name thy = n in
    let thys = imported_theories () in
    try Some (List.find pred thys)
    with Not_found -> None;;

let get_imported_theory n =
    match peek_imported_theory n with
      Some th -> th
    | None -> failwith ("theory " ^ n ^ " has not been imported");;

let is_imported_theory n =
    match peek_imported_theory n with
      Some _ -> true
    | None -> false;;

let add_imported_theory thy =
    let n = Theory.name thy in
    let thl = Theory.theorems thy in
    let () = List.iter (Export.add_exported_thm n) thl in
    let () = the_imported_theories := !the_imported_theories @ [thy] in
    ();;

(* ------------------------------------------------------------------------- *)
(* Theory bindings for theorems.                                             *)
(* ------------------------------------------------------------------------- *)

let exec_function =
    let exec (_ : string) : unit =
        failwith "Import.exec_function: not initialized" in
    ref exec;;

let bind_thm_names_mbox = ref (REFL (mk_var ("x",bool_ty)));;

let bind_thm_names =
    let ctxt_fn = theory_context "theorem names" in
    fun int thms bind renamer ->
    let bind_thm sth =
        let (s,tm) = dest_comb (concl sth) in
        let (_,s) = dest_comb s in
        let (s,_) = dest_abs s in
        let (s,_) = dest_var s in
        let s = renamer s in
        let th =
            match peek_sequent_map thms (Sequent.mk ([],tm)) with
              None -> failwith "bind_thm_names: couldn't find theorem"
            | Some (th,_) -> th in
        let () = bind_thm_names_mbox := th in
        let cmd = "let " ^ s ^ " = !Import.bind_thm_names_mbox;;" in
        let () = !exec_function cmd in
        () in
    let ctxt = ctxt_fn int thms in
    let h = open_in bind in
    let (_,sthl) = read_article ctxt "theorem names" h in
    let () = close_in h in
    List.iter bind_thm sthl;;

let theory_bindings n =
    let rec first_existing files =
        match files with
          [] ->
          let msg = "no HOL Light theorem names found for theory " ^ n in
          let () = warn true msg in
          None
        | file :: files ->
          if Sys.file_exists file then Some file else first_existing files in
    let local_override_file = Filename.concat import_directory (n ^ ".art") in
    let theory_file = Filename.concat (theory_directory n) "hol-light.art" in
    first_existing [local_override_file; theory_file];;

(* ------------------------------------------------------------------------- *)
(* Importing theories.                                                       *)
(* ------------------------------------------------------------------------- *)

let read_theory ctxt thy =
    let h = theory_article thy in
    let (a,t) = read_article ctxt ("theory " ^ thy) h in
    let () = close_in h in
    Theory.Theory (thy,a,t);;

let (auto_import_theory,import_theory) =
    let import_thy prefix thy =
        let int = !the_interpretation in
        let thms = !the_exported_thms in
        let ctxt = theory_context thy int thms in
        let th = read_theory ctxt thy in
        let () = print_endline (prefix ^ " " ^ Theory.to_string th) in
        let () = add_imported_theory th in
        th in
    let import_sub prefix thy =
        let _ = import_thy (prefix ^ "imported sub-theory") thy in
        () in
    let import_main prefix thy =
        let th = import_thy (prefix ^ "imported theory") thy in
        let () =
            match theory_bindings thy with
              None -> ()
            | Some bind ->
              let int = !the_interpretation in
              let thms = !the_exported_thms in
              bind_thm_names int thms bind I in
        th in
    let rec import_gen prefix thy =
        let (reqs,subs) = required_theories thy in
        let () = List.iter auto_import reqs in
        let () = extend_the_interpretation (theory_interpretation thy) in
        let () = List.iter (import_sub prefix) subs in
        import_main prefix thy
    and auto_import thy =
        if is_imported_theory thy then () else
        let _ = import_gen "auto-" thy in
        () in
    let import thy =
        match peek_imported_theory thy with
          None -> import_gen "" thy
        | Some th -> th in
    (auto_import,import);;

let import_theories =
    let import thy = let _ = import_theory thy in () in
    List.iter import;;

(* ------------------------------------------------------------------------- *)
(* Interpreting parametric theories.                                         *)
(* ------------------------------------------------------------------------- *)

type interpretation =
     {source_theory : string;
      interpretation : string;
      theorem_renamer : string -> string;
      destination_theory : string};;

let interpret_theory =
    let ctxt_fn = theory_context "interpret theory" in
    fun {source_theory = src;
         interpretation = int;
         theorem_renamer = renamer;
         destination_theory = dest} ->
    let (reqs,_) = required_theories src in
    let () = List.iter auto_import_theory reqs in
    let int = Interpretation.from_file int in
    let int = Interpretation.compose int (!the_interpretation) in
    let thms = !the_exported_thms in
    let ctxt = ctxt_fn int thms in
    let thy = read_theory ctxt src in
    let () = List.iter (Export.add_exported_thm dest) (Theory.theorems thy) in
    let () =
        match theory_bindings src with
          None -> ()
        | Some bind ->
          let thms = !the_exported_thms in
          bind_thm_names int thms bind renamer in
    thy;;

(* ------------------------------------------------------------------------- *)
(* Exporting theorem names for a particular theory.                          *)
(* ------------------------------------------------------------------------- *)

let export_theory_thm_names thy thys =
    let () =
        let msg = match !Export.the_current_theory with
                     None -> Some "outside of any theory"
                   | Some s -> if s = thy ^ "-hol-light-thm" then None else
                               Some ("in non-standard theory " ^ s) in
        match msg with
          None -> ()
        | Some m -> warn true ("export_theory_thm_names " ^ thy ^ " " ^ m) in
    let ths = filter_the_exported_thms thys in
    let () = export_thm_names ths in
    let () = add_imported_theory (Theory.Theory (thy,[],ths)) in
    ();;

end

let import_article = Import.import_article
and list_the_imported_theories = Import.imported_theories
and import_theory = Import.import_theory
and import_theories = Import.import_theories
and interpret_theory = Import.interpret_theory
and export_theory_thm_names = Import.export_theory_thm_names;;
