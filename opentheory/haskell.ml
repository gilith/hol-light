(* ========================================================================= *)
(* EXPORTING HOL LIGHT THEOREMS TO HASKELL                                   *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Haskellizing type variables in theorems.                                  *)
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
