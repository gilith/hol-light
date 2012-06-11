(* ========================================================================= *)
(* OPENTHEORY HASKELL BASE                                                   *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition.                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-def";;

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

let lengthH_def = new_definition
  `(lengthH : A list -> num) = LENGTH`;;

export_thm lengthH_def;;

let rdecode_list_destH_def = new_definition
  `rdecode_list_destH =
     (rdecode_list_dest :
        (random -> A # random) -> A list -> random -> A list)`;;

export_thm rdecode_list_destH_def;;

let rdecode_listH_def = new_definition
  `rdecode_listH =
     (rdecode_list :
       (random -> A # random) -> random -> A list # random)`;;

export_thm rdecode_listH_def;;

(* Natural numbers *)

let rdecode_fib_destH_def = new_definition
  `rdecode_fib_destH = rdecode_fib_dest`;;

export_thm rdecode_fib_destH_def;;

let rdecode_fibH_def = new_definition
  `rdecode_fibH = rdecode_fib`;;

export_thm rdecode_fibH_def;;

(* Random streams *)

let rbitsH_def = new_definition
  `rbitsH = rbits`;;

export_thm rbitsH_def;;

(* ------------------------------------------------------------------------- *)
(* Properties.                                                               *)
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
   MP_TAC (ISPEC `l : A list` list_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [NULL; equal_listH_nil_nil; equal_listH_nil_cons]);;

export_thm equal_listH_left_nil;;

let equal_listH_right_nil = prove
  (`!(eq : A -> A -> bool) l. equal_listH eq l [] <=> NULL l`,
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `l : A list` list_cases) THEN
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
   MP_TAC (ISPEC `l2 : A list` list_cases) THEN
   STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [equal_listH_cons_nil; NOT_CONS_NIL];
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC [equal_listH_cons_cons; CONS_11]]);;

export_thm equal_listH;;

(* ------------------------------------------------------------------------- *)
(* Source.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-src";;

(* Options *)

let () = (export_haskell_thm o prove)
 (`(!(eq : A -> A -> bool). equal_optionH eq NONE NONE = T) /\
   (!(eq : A -> A -> bool) x. equal_optionH eq NONE (SOME x) = F) /\
   (!(eq : A -> A -> bool) x. equal_optionH eq (SOME x) NONE = F) /\
   (!(eq : A -> A -> bool) x1 x2.
      equal_optionH eq (SOME x1) (SOME x2) = eq x1 x2)`,
  REWRITE_TAC [] THEN
  ACCEPT_TAC equal_optionH_def);;

(* Lists *)

let () = (export_haskell_thm o prove)
 (`(!(eq : A -> A -> bool). equal_listH eq [] [] = T) /\
   (!(eq : A -> A -> bool) h t. equal_listH eq [] (CONS h t) = F) /\
   (!(eq : A -> A -> bool) h t. equal_listH eq (CONS h t) [] = F) /\
   (!(eq : A -> A -> bool) h1 t1 h2 t2.
      equal_listH eq (CONS h1 t1) (CONS h2 t2) =
      (eq h1 h2 /\ equal_listH eq t1 t2))`,
  REWRITE_TAC [] THEN
  ACCEPT_TAC equal_listH_def);;

let () = (export_haskell_thm o prove)
 (`(lengthH ([] : A list) = 0) /\
   (!(h : A) t. lengthH (CONS h t) = 1 + lengthH t)`,
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  REWRITE_TAC [lengthH_def; LENGTH_NIL; LENGTH_CONS; ADD1]);;

let () = (export_haskell_thm o prove)
 (`!(d : random -> A # random) l r.
     rdecode_list_destH d l r =
     let b,r' = rbit r in
     if b then l else
     let (x,r'') = d r' in
     rdecode_list_destH d (CONS x l) r''`,
  REWRITE_TAC [rdecode_list_destH_def] THEN
  ACCEPT_TAC rdecode_list_dest_def);;

let () = (export_haskell_thm o prove)
 (`!(d : random -> A # random).
     rdecode_listH d =
     \r.
       let (r1,r2) = rsplit r in
       (rdecode_list_destH d [] r1, r2)`,
  REWRITE_TAC [rdecode_listH_def; rdecode_list_destH_def; FUN_EQ_THM] THEN
  ACCEPT_TAC rdecode_list_def);;

(* Natural numbers *)

let () = (export_haskell_thm o prove)
 (`!b n f p r.
     rdecode_fib_destH b n f p r =
     let b',r' = rbit r in
     if b' /\ b then n
     else
       let s = f + p in
       rdecode_fib_destH b' (if b' then s + n else n) s f r'`,
  REWRITE_TAC [rdecode_fib_destH_def] THEN
  ACCEPT_TAC rdecode_fib_dest_def);;

let () = (export_haskell_thm o prove)
 (`rdecode_fibH =
   \r.
     let (r1,r2) = rsplit r in
     (rdecode_fib_destH F 0 1 0 r1 - 1, r2)`,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
  REWRITE_TAC [rdecode_fibH_def; rdecode_fib_destH_def] THEN
  ACCEPT_TAC rdecode_fib_def);;

(* Random streams *)

let () = (export_haskell_thm o prove)
 (`!n r.
     rbitsH n r =
     if n = 0 then ([],r) else
     let (b,r') = rbit r in
     let (l,r'') = rbitsH (n - 1) r' in
     (CONS b l, r'')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [rbitsH_def] THEN
  NUM_CASES_TAC `n : num` THENL
  [DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [rbits_zero];
   DISCH_THEN (X_CHOOSE_THEN `m : num` SUBST1_TAC) THEN
   REWRITE_TAC [NOT_SUC; rbits_suc; SUC_SUB1]]);;

(* ------------------------------------------------------------------------- *)
(* Testing.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-test";;

let () = (export_haskell_thm o prove)
 (`!r.
     let (n1,r') = rdecode_fibH r in
     let (n2,r'') = rdecode_fibH r' in
     (~(n1 = n2) \/ n2 = n1)`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_fibH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `n1 : num`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  PAIR_CASES_TAC `rdecode_fibH r'` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `n2 : num`
      (X_CHOOSE_THEN `r'' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC (TAUT `!x y. (x ==> y) ==> ~x \/ y`) THEN
  MATCH_ACCEPT_TAC EQ_SYM);;

logfile_end ();;
