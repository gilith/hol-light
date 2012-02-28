(* ========================================================================= *)
(* OPENTHEORY HASKELL LIBRARY                                                *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of the Haskell base.                                           *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-def";;

(* Numbers *)

let equal_numH_def = new_definition
  `(equal_numH : num -> num -> bool) = (=)`;;

export_thm equal_numH_def;;

(* Options *)

let (equal_optionH_none_none,equal_optionH_none_some,
     equal_optionH_some_none,equal_optionH_some_some) =
  let def = new_recursive_definition option_RECURSION
    `(!(eq : A -> A -> bool) (xo : A option).
        equal_optionH eq xo (NONE : A option) <=> is_none xo) /\
     (!(eq : A -> A -> bool) (xo : A option) x.
        equal_optionH eq xo (SOME x) <=>
          case_option F (\x'. eq x' x) xo)` in
  let none_none = prove
    (`!(eq : A -> A -> bool). equal_optionH eq NONE NONE`,
     REWRITE_TAC [def; is_none_def])
  and none_some = prove
    (`!(eq : A -> A -> bool) x. ~equal_optionH eq NONE (SOME x)`,
     REWRITE_TAC [def; case_option_def])
  and some_none = prove
    (`!(eq : A -> A -> bool) x. ~equal_optionH eq (SOME x) NONE`,
     REWRITE_TAC [def; is_none_def])
  and some_some = prove
    (`!(eq : A -> A -> bool) x1 x2.
        equal_optionH eq (SOME x1) (SOME x2) <=> eq x1 x2`,
     REWRITE_TAC [def; case_option_def]) in
  (none_none,none_some,some_none,some_some);;

export_thm equal_optionH_none_none;;
export_thm equal_optionH_none_some;;
export_thm equal_optionH_some_none;;
export_thm equal_optionH_some_some;;

let equal_optionH_def =
  CONJ equal_optionH_none_none
    (CONJ equal_optionH_none_some
       (CONJ equal_optionH_some_none equal_optionH_some_some));;

(* Lists *)

let (equal_listH_nil_nil,equal_listH_nil_cons,
     equal_listH_cons_nil,equal_listH_cons_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!(eq : A -> A -> bool) (l : A list).
        equal_listH eq l ([] : A list) <=> NULL l) /\
     (!(eq : A -> A -> bool) (l : A list) h t.
        equal_listH eq l (CONS h t) <=>
          case_list F (\h' t'. eq h' h /\ equal_listH eq t' t) l)` in
  let nil_nil = prove
    (`!(eq : A -> A -> bool). equal_listH eq [] []`,
     REWRITE_TAC [def; NULL])
  and nil_cons = prove
    (`!(eq : A -> A -> bool) h t. ~equal_listH eq [] (CONS h t)`,
     REWRITE_TAC [def; case_list_def])
  and cons_nil = prove
    (`!(eq : A -> A -> bool) h t. ~equal_listH eq (CONS h t) []`,
     REWRITE_TAC [def; NULL])
  and cons_cons = prove
    (`!(eq : A -> A -> bool) h1 t1 h2 t2.
        equal_listH eq (CONS h1 t1) (CONS h2 t2) <=>
        eq h1 h2 /\ equal_listH eq t1 t2`,
     REWRITE_TAC [def; case_list_def]) in
  (nil_nil,nil_cons,cons_nil,cons_cons);;

export_thm equal_listH_nil_nil;;
export_thm equal_listH_nil_cons;;
export_thm equal_listH_cons_nil;;
export_thm equal_listH_cons_cons;;

let equal_listH_def =
  CONJ equal_listH_nil_nil
    (CONJ equal_listH_nil_cons
       (CONJ equal_listH_cons_nil equal_listH_cons_cons));;

(* ------------------------------------------------------------------------- *)
(* Properties of the Haskell base.                                           *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-thm";;

(* Options *)

let equal_optionH_left_none = prove
  (`!(eq : A -> A -> bool) x. equal_optionH eq NONE x <=> is_none x`,
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `x : A option` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_none_def; equal_optionH_none_none; equal_optionH_none_some]);;

export_thm equal_optionH_left_none;;

let equal_optionH_right_none = prove
  (`!(eq : A -> A -> bool) x. equal_optionH eq x NONE <=> is_none x`,
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `x : A option` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_none_def; equal_optionH_none_none; equal_optionH_some_none]);;

export_thm equal_optionH_right_none;;

let equal_optionH = prove
  (`equal_optionH ((=) : A -> A -> bool) = (=)`,
   CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
   X_GEN_TAC `x1 : A option` THEN
   CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
   X_GEN_TAC `x2 : A option` THEN
   MP_TAC (ISPEC `x1 : A option` option_cases) THEN
   MP_TAC (ISPEC `x2 : A option` option_cases) THEN
   REPEAT STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   REWRITE_TAC [equal_optionH_def; option_distinct; option_inj]);;

export_thm equal_optionH;;

(* Lists *)

let equal_listH_left_nil = prove
  (`!(eq : A -> A -> bool) l. equal_listH eq [] l <=> NULL l`,
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `l : A list` list_CASES) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [NULL; equal_listH_nil_nil; equal_listH_nil_cons]);;

export_thm equal_listH_left_nil;;

let equal_listH_right_nil = prove
  (`!(eq : A -> A -> bool) l. equal_listH eq l [] <=> NULL l`,
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `l : A list` list_CASES) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [NULL; equal_listH_nil_nil; equal_listH_cons_nil]);;

export_thm equal_listH_right_nil;;

let equal_listH = prove
  (`equal_listH ((=) : A -> A -> bool) = (=)`,
   CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
   X_GEN_TAC `l1 : A list` THEN
   CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
   X_GEN_TAC `l2 : A list` THEN
   SPEC_TAC (`l2 : A list`,`l2 : A list`) THEN
   SPEC_TAC (`l1 : A list`,`l1 : A list`) THEN
   LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC [equal_listH_left_nil; NULL_EQ_NIL] THEN
    MATCH_ACCEPT_TAC EQ_SYM_EQ;
    ALL_TAC] THEN
   GEN_TAC THEN
   MP_TAC (ISPEC `l2 : A list` list_CASES) THEN
   STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [equal_listH_cons_nil; NOT_CONS_NIL];
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC [equal_listH_cons_cons; CONS_11]]);;

export_thm equal_listH;;

logfile_end ();;
