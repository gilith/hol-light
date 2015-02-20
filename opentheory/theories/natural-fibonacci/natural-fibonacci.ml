(* ========================================================================= *)
(* FIBONACCI NUMBERS                                                         *)
(* Joe Leslie-Hurd                                                           *)
(*                                                                           *)
(* See http://en.wikipedia.org/wiki/Fibonacci_coding                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for Fibonacci numbers.                                    *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/natural-fibonacci/natural-fibonacci.int";;

(* ------------------------------------------------------------------------- *)
(* Existence of Fibonacci numbers.                                           *)
(* ------------------------------------------------------------------------- *)

logfile "natural-fibonacci-exists";;

let fibonacci_induction = prove
  (`!p : num -> bool.
      p 0 /\
      p 1 /\
      (!n. p n /\ p (n + 1) ==> p (n + 2)) ==>
      !n. p n`,
   REWRITE_TAC [ONE; TWO; ADD_CLAUSES] THEN
   REPEAT STRIP_TAC THEN
   WF_INDUCT_TAC `n : num` THEN
   MP_TAC (SPEC `n : num` num_CASES) THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `n' : num` num_CASES) THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_THEN `!n. p n /\ p (SUC n) ==> p (SUC (SUC n))` MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `SUC n''` THEN
    CONJ_TAC THEN
    MATCH_ACCEPT_TAC SUC_LT;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_ACCEPT_TAC SUC_LT]);;

export_thm fibonacci_induction;;

let fibonacci_recursion = prove
  (`!(h : (num -> A) -> num -> A).
       (!f g n.
          (!m. m + 1 = n \/ m + 2 = n ==> (f m = g m)) ==>
          (h f n = h g n)) ==>
       ?f. !n. f n = h f n`,
   SUBGOAL_THEN
     `!(h : (num -> A) -> num -> A).
         (!f g n.
            (!m. (\x y. x + 1 = y \/ x + 2 = y) m n ==> (f m = g m)) ==>
            (h f n = h g n)) ==>
         ?f. !n. f n = h f n` (ACCEPT_TAC o REWRITE_RULE []) THEN
   MATCH_MP_TAC WF_REC THEN
   MATCH_MP_TAC WF_SUBSET THEN
   EXISTS_TAC `(<) : num -> num -> bool` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [GSYM LE_SUC_LT; ADD1] THEN
    REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM SUBST_VAR_TAC THEN
     MATCH_ACCEPT_TAC LE_REFL;
     FIRST_X_ASSUM SUBST_VAR_TAC THEN
     REWRITE_TAC [LE_ADD_LCANCEL; TWO; SUC_LE]];
    ACCEPT_TAC WF_num]);;

export_thm fibonacci_recursion;;

let fibonacci_exists = prove
  (`?f.
      f 0 = 0 /\
      f 1 = 1 /\
      !n. f (n + 2) = f (n + 1) + f n`,
   SUBGOAL_THEN
     `?f. !n.
        f n =
        (\f' n'. if n' < 2 then n' else f' (n' - 1) + f' (n' - 2)) f n`
     MP_TAC THENL
   [MATCH_MP_TAC fibonacci_recursion THEN
    GEN_TAC THEN
    GEN_TAC THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC fibonacci_induction THEN
    REPEAT STRIP_TAC THENL
    [NUM_REDUCE_TAC;
     NUM_REDUCE_TAC;
     BOOL_CASES_TAC `n + 2 < 2` THENL
     [REWRITE_TAC [];
      REWRITE_TAC [ADD_SUB] THEN
      SUBGOAL_THEN `(f : num -> num) n = g n` SUBST1_TAC THENL
      [FIRST_X_ASSUM MATCH_MP_TAC THEN
       DISJ2_TAC THEN
       REFL_TAC;
       REWRITE_TAC [EQ_ADD_RCANCEL] THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       DISJ1_TAC THEN
       MATCH_MP_TAC SUB_ADD THEN
       REWRITE_TAC [TWO; ONE; LE_SUC; ADD_CLAUSES; LE_0]]]];
    REWRITE_TAC [] THEN
    STRIP_TAC THEN
    EXISTS_TAC `f : num -> num` THEN
    REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM (fun th -> ONCE_REWRITE_TAC [th]) THEN
     NUM_REDUCE_TAC;
     FIRST_X_ASSUM (fun th -> ONCE_REWRITE_TAC [th]) THEN
     NUM_REDUCE_TAC;
     FIRST_X_ASSUM
       (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
     SUBGOAL_THEN `n + 2 < 2 <=> F` SUBST1_TAC THENL
     [REWRITE_TAC [NOT_LT; LE_ADDR];
      REWRITE_TAC [ADD_SUB; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC [TWO; ADD_CLAUSES] THEN
      REWRITE_TAC [ADD_SUB; ADD1]]]]);;

export_thm fibonacci_exists;;

(* ------------------------------------------------------------------------- *)
(* Definition of Fibonacci numbers.                                          *)
(* ------------------------------------------------------------------------- *)

logfile "natural-fibonacci-def";;

let (fibonacci_zero,fibonacci_one,fibonacci_add2) =
  let def = new_specification ["fibonacci"] fibonacci_exists in
  let fib1 = CONJUNCT1 def in
  let def = CONJUNCT2 def in
  let fib2 = CONJUNCT1 def in
  let def = CONJUNCT2 def in
  (fib1,fib2,def);;

export_thm fibonacci_zero;;
export_thm fibonacci_one;;
export_thm fibonacci_add2;;

let fibonacci_def =
    CONJ fibonacci_zero (CONJ fibonacci_one fibonacci_add2);;

let (decode_fib_dest_nil,decode_fib_dest_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!f p. decode_fib_dest f p [] = 0) /\
     (!f p h t.
        decode_fib_dest f p (CONS h t) =
        let s = f + p in
        let n = decode_fib_dest s f t in
        if h then s + n else n)` in
  CONJ_PAIR def;;

export_thm decode_fib_dest_nil;;
export_thm decode_fib_dest_cons;;

let decode_fib_dest_def = CONJ decode_fib_dest_nil decode_fib_dest_cons;;

let decode_fib_def = new_definition
  `!l. decode_fib l = decode_fib_dest 1 0 l`;;

export_thm decode_fib_def;;

let encode_fib_mk_exists = prove
 (`?mk. !l n f p.
     mk l n f p =
      if p = 0 then l
      else if f <= n then mk (CONS T l) (n - f) p (f - p)
      else mk (CONS F l) n p (f - p)`,
  MP_TAC
   (ISPECL
      [`\ ((l : bool list), (n : num), (f : num), (p : num)).
          ~(p = 0)`;
       `\ ((l : bool list), (n : num), (f : num), (p : num)).
          if f <= n then (CONS T l, n - f, p, f - p)
          else (CONS F l, n, p, f - p)`;
       `\ ((l : bool list), (n : num), (f : num), (p : num)).
          l`] WF_REC_TAIL) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `mk : bool list # num # num # num -> bool list`
     STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\ (l : bool list) (n : num) (f : num) (p : num).
                (mk (l,n,f,p) : bool list)` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [] THEN
  FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  REWRITE_TAC [] THEN
  BOOL_CASES_TAC `p = 0` THENL
  [REWRITE_TAC [];
   REWRITE_TAC [] THEN
   MATCH_ACCEPT_TAC COND_RAND]);;

let encode_fib_mk_def =
  new_specification ["encode_fib_mk"] encode_fib_mk_exists;;

export_thm encode_fib_mk_def;;

let encode_fib_find_exists = prove
 (`!n. ?find. !f p.
     find f p =
       let s = f + p in
       if n < s then encode_fib_mk [] n f p else find s f`,
  GEN_TAC THEN
  MP_TAC
   (ISPECL
      [`\ ((f : num), (p : num)). ~(n < f + p)`;
       `\ ((f : num), (p : num)). (f + p, f)`;
       `\ ((f : num), (p : num)). encode_fib_mk [] n f p`] WF_REC_TAIL) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `find : num # num -> bool list`
     STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\ (f : num) (p : num). (find (f,p) : bool list)` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [] THEN
  FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  BOOL_CASES_TAC `n < f + (p : num)` THENL
  [REWRITE_TAC [];
   REWRITE_TAC []]);;

let encode_fib_find_def =
  new_specification ["encode_fib_find"]
    (REWRITE_RULE [SKOLEM_THM] encode_fib_find_exists);;

export_thm encode_fib_find_def;;

let encode_fib_def = new_definition
  `!n. encode_fib n = encode_fib_find n 1 0`;;

export_thm encode_fib_def;;

let (zeckendorf_nil,zeckendorf_cons) =
  let def = new_recursive_definition list_RECURSION
    `(zeckendorf [] <=> T) /\
     (!h t.
        zeckendorf (CONS h t) <=>
        if NULL t then h else ~(h /\ HD t) /\ zeckendorf t)` in
  CONJ_PAIR (REWRITE_RULE [] def);;

export_thm zeckendorf_nil;;
export_thm zeckendorf_cons;;

let zeckendorf_def = CONJ zeckendorf_nil zeckendorf_cons;;

let random_fib_dest_exists = prove
 (`?dest. !b (n : num) f p r.
     dest b n f p r =
       let (r1,r2) = split_random r in
       let b' = random_bit r1 in
       if b' /\ b then n else
       let s = f + p in
       dest b' (if b' then s + n else n) s f r2`,
  MP_TAC
   (ISPECL
      [`\ ((b : bool), (n : num), (f : num), (p : num), (r : random)).
          let (r1,r2) = split_random r in
          let b' = random_bit r1 in
          ~(b' /\ b)`;
       `\ ((b : bool), (n : num), (f : num), (p : num), (r : random)).
          let (r1,r2) = split_random r in
          let b' = random_bit r1 in
          let s = f + p in
          (b', (if b' then s + n else n), s, f, r2)`;
       `\ ((b : bool), (n : num), (f : num), (p : num), (r : random)).
          n`] WF_REC_TAIL) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `dest : bool # num # num # num # random -> num`
     STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
    `\ (b : bool) (n : num) (f : num) (p : num) (r : random).
       ((dest (b,n,f,p,r)) : num)` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [] THEN
  FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  PAIR_CASES_TAC `split_random r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `r1 : random`
       (X_CHOOSE_THEN `r2 : random` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  BOOL_CASES_TAC `random_bit r1 /\ b` THENL
  [REWRITE_TAC [];
   REWRITE_TAC []]);;

let random_fib_dest_def =
  new_specification ["random_fib_dest"] random_fib_dest_exists;;

export_thm random_fib_dest_def;;

let random_fib_def = new_definition
  `!r. random_fib r = random_fib_dest F 0 1 0 r - 1`;;

export_thm random_fib_def;;

let random_fib_list_def = new_definition
  `!f r.
     random_fib_list (f : random -> A) r =
     let (r1,r2) = split_random r in
     random_vector f (random_fib r1) r2`;;

export_thm random_fib_list_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of Fibonacci numbers.                                          *)
(* ------------------------------------------------------------------------- *)

logfile "natural-fibonacci-thm";;

export_thm fibonacci_induction;;  (* Re-export *)
export_thm fibonacci_recursion;;  (* Re-export *)

let fibonacci_suc_suc = prove
 (`!k. fibonacci (SUC (SUC k)) = fibonacci (SUC k) + fibonacci k`,
  GEN_TAC THEN
  SUBGOAL_THEN `SUC (SUC k) = k + 2` SUBST1_TAC THENL
  [REWRITE_TAC [TWO; ONE; ADD_CLAUSES];
   REWRITE_TAC [fibonacci_def; EQ_ADD_RCANCEL; ADD1]]);;

export_thm fibonacci_suc_suc;;

let fibonacci_two = prove
 (`fibonacci 2 = 1`,
  REWRITE_TAC [TWO; ONE; fibonacci_suc_suc; fibonacci_zero; ADD_CLAUSES] THEN
  REWRITE_TAC [fibonacci_one; GSYM ONE]);;

export_thm fibonacci_two;;

let fibonacci_eq_zero = prove
 (`!k. fibonacci k = 0 <=> k = 0`,
  MATCH_MP_TAC fibonacci_induction THEN
  REWRITE_TAC [fibonacci_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [ADD_EQ_0] THEN
  NUM_REDUCE_TAC);;

export_thm fibonacci_eq_zero;;

let fibonacci_mono_imp = prove
 (`!j k. j <= k ==> fibonacci j <= fibonacci k`,
  MATCH_MP_TAC fibonacci_induction THEN
  REWRITE_TAC [fibonacci_def; LE_0] THEN
  STRIP_TAC THENL
  [GEN_TAC THEN
   REWRITE_TAC [LT_NZ; ONE; LE_SUC_LT; fibonacci_eq_zero];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j + 2 <= j + k`
    (MP_TAC o ONCE_REWRITE_RULE [ADD_SYM] o
     REWRITE_RULE [LE_EXISTS] o REWRITE_RULE [LE_ADD_LCANCEL]) THENL
  [MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [LE_ADDR];
   ALL_TAC] THEN
  DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC [LE_ADD_RCANCEL] THEN
  STRIP_TAC THEN
  REWRITE_TAC [fibonacci_def] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `fibonacci (j + 1) + fibonacci d` THEN
  REWRITE_TAC [LE_ADD_LCANCEL; LE_ADD_RCANCEL] THEN
  STRIP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC;
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [LE_ADD_RCANCEL]]);;

export_thm fibonacci_mono_imp;;

let fibonacci_strictly_mono_suc = prove
 (`!j. ~(j = 1) ==> fibonacci j < fibonacci (SUC j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `j : num` num_CASES) THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC [LT_NZ; fibonacci_def; fibonacci_eq_zero; NOT_SUC];
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC
     [fibonacci_suc_suc; LT_ADD; LT_NZ; fibonacci_eq_zero; ONE; SUC_INJ]]);;

export_thm fibonacci_strictly_mono_suc;;

let fibonacci_strictly_mono_imp = prove
 (`!j k. ~(j = 1 /\ k = 2) /\ j < k ==> fibonacci j < fibonacci k`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE [LT_EXISTS]) THEN
  DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC [ADD_CLAUSES; TWO; SUC_INJ; DE_MORGAN_THM] THEN
  STRIP_TAC THENL
  [MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `fibonacci (SUC j)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC fibonacci_strictly_mono_suc THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC fibonacci_mono_imp THEN
    REWRITE_TAC [LE_SUC; LE_ADD]];
   MATCH_MP_TAC LET_TRANS THEN
   EXISTS_TAC `fibonacci (j + d)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC fibonacci_mono_imp THEN
    MATCH_ACCEPT_TAC LE_ADD;
    MATCH_MP_TAC fibonacci_strictly_mono_suc THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

export_thm fibonacci_strictly_mono_imp;;

let fibonacci_mono_imp' = prove
 (`!j k. ~(j = 2 /\ k = 1) /\ fibonacci j <= fibonacci k ==> j <= k`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC [NOT_LE] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC fibonacci_strictly_mono_imp THEN
  ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [CONJ_SYM] THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm fibonacci_mono_imp';;

let fibonacci_strictly_mono_imp' = prove
 (`!j k. fibonacci j < fibonacci k ==> j < k`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC [NOT_LT] THEN
  MATCH_ACCEPT_TAC fibonacci_mono_imp);;

export_thm fibonacci_strictly_mono_imp';;

let large_fibonacci = prove
 (`!n. ?k. n <= fibonacci k`,
  INDUCT_TAC THENL
  [REWRITE_TAC [LE_0];
   POP_ASSUM STRIP_ASSUME_TAC THEN
   EXISTS_TAC `SUC (SUC k)` THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `SUC (fibonacci k)` THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC [LE_SUC];
    REWRITE_TAC
     [LE_SUC_LT; fibonacci_suc_suc; LT_ADDR; LT_NZ; fibonacci_eq_zero;
      NOT_SUC]]]);;

export_thm large_fibonacci;;

let fibonacci_interval = prove
 (`!n. ?k. fibonacci k <= n /\ n < fibonacci (k + 1)`,
  GEN_TAC THEN
  MP_TAC ((REWRITE_RULE [MINIMAL] o REWRITE_RULE [LE_SUC_LT] o
           SPEC `SUC n`) large_fibonacci) THEN
  MP_TAC (SPEC `minimal k. n < fibonacci k` num_CASES) THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC [fibonacci_zero; LT];
   POP_ASSUM SUBST1_TAC THEN
   REWRITE_TAC [NOT_LT; LT_SUC_LE] THEN
   STRIP_TAC THEN
   EXISTS_TAC `n' : num` THEN
   ASM_REWRITE_TAC [GSYM ADD1] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_ACCEPT_TAC LE_REFL]);;

export_thm fibonacci_interval;;

let fibonacci_vorobev = prove
 (`!j k.
     fibonacci (j + k + 1) =
     fibonacci j * fibonacci k + fibonacci (j + 1) * fibonacci (k + 1)`,
  INDUCT_TAC THENL
  [REWRITE_TAC [ADD_CLAUSES; fibonacci_def; MULT_CLAUSES];
   ALL_TAC] THEN
  GEN_TAC THEN
  REWRITE_TAC [ONE; ADD_CLAUSES] THEN
  CONV_TAC (RAND_CONV (REWRITE_CONV [fibonacci_suc_suc])) THEN
  REWRITE_TAC [ADD_ASSOC; RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC [GSYM LEFT_ADD_DISTRIB] THEN
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [ADD_SYM])) THEN
  CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [ADD_SYM]))) THEN
  REWRITE_TAC [GSYM fibonacci_suc_suc] THEN
  ONCE_REWRITE_TAC [GSYM ADD_SUC] THEN
  REWRITE_TAC [ADD1] THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM ADD_ASSOC])) THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

export_thm fibonacci_vorobev;;

let decode_fib_nil = prove
 (`decode_fib [] = 0`,
  REWRITE_TAC [decode_fib_def; decode_fib_dest_def]);;

export_thm decode_fib_nil;;

let encode_fib_zero = prove
 (`encode_fib 0 = []`,
  REWRITE_TAC [encode_fib_def] THEN
  ONCE_REWRITE_TAC [encode_fib_find_def] THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF; ADD_CLAUSES; LT_NZ; ONE; NOT_SUC] THEN
  ONCE_REWRITE_TAC [encode_fib_mk_def] THEN
  REWRITE_TAC []);;

export_thm encode_fib_zero;;

let decode_fib_dest_append = prove
 (`!k l1 l2.
     decode_fib_dest (fibonacci (k + 1)) (fibonacci k) (APPEND l1 l2) =
     decode_fib_dest (fibonacci (k + 1)) (fibonacci k) l1 +
     decode_fib_dest (fibonacci (LENGTH l1 + (k + 1)))
       (fibonacci (LENGTH l1 + k)) l2`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  SPEC_TAC (`l1 : bool list`, `l1 : bool list`) THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC
     [APPEND; decode_fib_dest_def; LENGTH; ADD_CLAUSES; fibonacci_def];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [APPEND; decode_fib_dest_def; LENGTH; ADD_CLAUSES;
     GSYM fibonacci_add2] THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `SUC k`) THEN
  REWRITE_TAC [ONE; TWO; ADD_CLAUSES] THEN
  BOOL_CASES_TAC `h : bool` THEN
  REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL]);;

let decode_fib_append = prove
 (`!l1 l2.
     decode_fib (APPEND l1 l2) =
     decode_fib l1 +
     decode_fib_dest (fibonacci (LENGTH l1 + 1)) (fibonacci (LENGTH l1)) l2`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPECL [`0`; `l1 : bool list`; `l2 : bool list`]
       decode_fib_dest_append) THEN
  REWRITE_TAC [ADD_CLAUSES; fibonacci_def; decode_fib_def]);;

let encode_decode_fib_dest_mk = prove
 (`!n k l.
     n < fibonacci (k + 2) ==>
     decode_fib_dest 1 0
       (encode_fib_mk l n (fibonacci (k + 1)) (fibonacci k)) =
     n + decode_fib_dest (fibonacci (k + 1)) (fibonacci k) l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [fibonacci_add2] THEN
  SPEC_TAC (`l : bool list`, `l : bool list`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [fibonacci_def; ADD_CLAUSES] THEN
   REWRITE_TAC [GSYM LE_SUC_LT; ONE; LE_SUC; LE] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   ONCE_REWRITE_TAC [encode_fib_mk_def] THEN
   REWRITE_TAC [ADD_CLAUSES];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM ADD1; fibonacci_suc_suc] THEN
  REWRITE_TAC [ADD1] THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC [encode_fib_mk_def] THEN
  SUBGOAL_THEN `fibonacci (k + 1) = 0 <=> F` SUBST1_TAC THENL
  [REWRITE_TAC [fibonacci_eq_zero; GSYM ADD1; NOT_SUC];
   ALL_TAC] THEN
  REWRITE_TAC [] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [ADD_SUB2] THEN
   FIRST_X_ASSUM
     (MP_TAC o SPECL
        [`n - (fibonacci (k + 1) + fibonacci k)`;
         `CONS T l`]) THEN
   UNDISCH_TAC `n < (fibonacci (k + 1) + fibonacci k) + fibonacci (k + 1)` THEN
   FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [LE_EXISTS]) THEN
   DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
   REWRITE_TAC [ADD_SUB2; LT_ADD_LCANCEL] THEN
   STRIP_TAC THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `fibonacci (k + 1)` THEN
    ASM_REWRITE_TAC [LE_ADD];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [decode_fib_dest_def; LET_DEF; LET_END_DEF] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV (GSYM ADD_ASSOC))) THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   REWRITE_TAC [ADD_SUB2] THEN
   FIRST_X_ASSUM
     (MP_TAC o SPECL
        [`n : num`;
         `CONS F l`]) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [GSYM NOT_LE];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [decode_fib_dest_def; LET_DEF; LET_END_DEF]]);;

let encode_decode_fib_dest_find = prove
 (`!n k.
     decode_fib_dest 1 0
       (encode_fib_find n (fibonacci (k + 1)) (fibonacci k)) = n`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?j. n < fibonacci (j + 2) /\ k <= j` MP_TAC THENL
  [MP_TAC (SPEC `SUC n` large_fibonacci) THEN
   REWRITE_TAC [LE_SUC_LT] THEN
   DISCH_THEN (X_CHOOSE_THEN `i : num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `(i : num) + k` THEN
   REWRITE_TAC [LE_ADDR] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `fibonacci i` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC fibonacci_mono_imp THEN
   REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD];
   ALL_TAC] THEN
  STRIP_TAC THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE [LE_EXISTS]) THEN
  DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  SPEC_TAC (`d : num`, `d : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [ADD_CLAUSES] THEN
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [encode_fib_find_def] THEN
   REWRITE_TAC [GSYM fibonacci_add2] THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   MP_TAC (SPECL [`n : num`; `k : num`; `[] : bool list`]
                 encode_decode_fib_dest_mk) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [decode_fib_dest_def; ADD_CLAUSES];
   ALL_TAC] THEN
  REWRITE_TAC [ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [encode_fib_find_def] THEN
  REWRITE_TAC [GSYM fibonacci_add2] THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL
  [MP_TAC (SPECL [`n : num`; `k : num`; `[] : bool list`]
                 encode_decode_fib_dest_mk) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [decode_fib_dest_def; ADD_CLAUSES];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `SUC k`) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [ADD_CLAUSES];
   REWRITE_TAC [TWO; ONE; ADD_CLAUSES]]);;

let encode_decode_fib = prove
 (`!n. decode_fib (encode_fib n) = n`,
  GEN_TAC THEN
  REWRITE_TAC [decode_fib_def; encode_fib_def] THEN
  MP_TAC (SPECL [`n : num`; `0`] encode_decode_fib_dest_find) THEN
  REWRITE_TAC [ADD_CLAUSES; fibonacci_def]);;

export_thm encode_decode_fib;;

let null_encode_fib = prove
 (`!n. NULL (encode_fib n) <=> n = 0`,
  GEN_TAC THEN
  REWRITE_TAC [NULL_EQ_NIL] THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM encode_decode_fib] THEN
   ASM_REWRITE_TAC [encode_fib_zero];
   DISCH_THEN SUBST1_TAC THEN
   ACCEPT_TAC encode_fib_zero]);;

export_thm null_encode_fib;;

let zeckendorf_cons_imp = prove
 (`!h t. zeckendorf (CONS h t) ==> zeckendorf t`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [zeckendorf_nil];
   CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [zeckendorf_def])) THEN
   REWRITE_TAC [NULL] THEN
   STRIP_TAC]);;

export_thm zeckendorf_cons_imp;;

let zeckendorf_decode_fib_dest_lower_bound = prove
 (`!k h t.
     zeckendorf (CONS h t) ==>
     fibonacci ((k + 2) + LENGTH t) <=
     decode_fib_dest (fibonacci (k + 1)) (fibonacci k) (CONS h t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [ONE; TWO; ADD_CLAUSES] THEN
  SPEC_TAC (`h : bool`, `h : bool`) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  SPEC_TAC (`t : bool list`, `t : bool list`) THEN
  LIST_INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC
     [LENGTH; ADD_CLAUSES; decode_fib_dest_def; zeckendorf_def; NULL;
      GSYM fibonacci_suc_suc] THEN
   DISCH_THEN (SUBST_VAR_TAC o EQT_INTRO) THEN
   REWRITE_TAC [ADD_CLAUSES; LET_DEF; LET_END_DEF; LE_REFL];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [zeckendorf_def; decode_fib_dest_def; LENGTH] THEN
  REWRITE_TAC [NULL; HD; GSYM fibonacci_suc_suc; APPEND] THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`SUC k`; `h : bool`]) THEN
  ASM_REWRITE_TAC [ADD_CLAUSES] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  SPEC_TAC
    (`decode_fib_dest (fibonacci (SUC (SUC k))) (fibonacci (SUC k)) (CONS h t)`,
      `n : num`) THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `h' : bool` THEN
  REWRITE_TAC [LE_REFL; LE_ADDR]);;

let zeckendorf_decode_fib_lower_bound = prove
 (`!l. ~NULL l /\ zeckendorf l ==> fibonacci (LENGTH l + 1) <= decode_fib l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [NULL];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [NULL] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL [`0`; `h : bool`; `t : bool list`]
       zeckendorf_decode_fib_dest_lower_bound) THEN
  ASM_REWRITE_TAC
    [decode_fib_def; ADD_CLAUSES; fibonacci_zero; fibonacci_one] THEN
  REWRITE_TAC [ONE; TWO; THREE; ADD_CLAUSES; LENGTH]);;

export_thm zeckendorf_decode_fib_lower_bound;;

let zeckendorf_decode_fib_dest_upper_bound = prove
 (`!k h t l.
     zeckendorf (CONS h (APPEND t l)) ==>
     fibonacci (k + (if h then 1 else 2)) +
     decode_fib_dest (fibonacci (k + 1)) (fibonacci k) (CONS h t) <=
     fibonacci ((k + 3) + LENGTH t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [ONE; TWO; THREE; ADD_CLAUSES] THEN
  SPEC_TAC (`h : bool`, `h : bool`) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  SPEC_TAC (`t : bool list`, `t : bool list`) THEN
  LIST_INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   DISCH_THEN (K ALL_TAC) THEN
   REWRITE_TAC [LENGTH; ADD_CLAUSES] THEN
   BOOL_CASES_TAC `h : bool` THENL
   [REWRITE_TAC [decode_fib_dest_def; GSYM fibonacci_suc_suc] THEN
    REWRITE_TAC [ADD_CLAUSES; LET_DEF; LET_END_DEF] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [GSYM fibonacci_suc_suc] THEN
    MATCH_ACCEPT_TAC LE_REFL;
    REWRITE_TAC [decode_fib_dest_def; LET_DEF; LET_END_DEF; ADD_CLAUSES] THEN
    MATCH_MP_TAC fibonacci_mono_imp THEN
    MATCH_ACCEPT_TAC SUC_LE];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [zeckendorf_def; decode_fib_dest_def; LENGTH] THEN
  REWRITE_TAC [NULL; HD; GSYM fibonacci_suc_suc; APPEND] THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`SUC k`; `h : bool`]) THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM MP_TAC THEN
  BOOL_CASES_TAC `h' : bool` THENL
  [REWRITE_TAC [ADD_CLAUSES] THEN
   DISCH_THEN (SUBST_VAR_TAC o EQF_INTRO) THEN
   REWRITE_TAC
     [ADD_CLAUSES; ONCE_REWRITE_RULE [ADD_SYM] (GSYM fibonacci_suc_suc);
      ADD_ASSOC];
   ALL_TAC] THEN
  REWRITE_TAC [ADD_CLAUSES] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
    `fibonacci (SUC (k + (if h then SUC 0 else SUC (SUC 0)))) +
     decode_fib_dest (fibonacci (SUC (SUC k))) (fibonacci (SUC k))
       (CONS h t)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [LE_ADD_RCANCEL] THEN
   MATCH_MP_TAC fibonacci_mono_imp THEN
   BOOL_CASES_TAC `h : bool` THENL
   [REWRITE_TAC [ADD_CLAUSES; LE_REFL];
    REWRITE_TAC [ADD_CLAUSES; SUC_LE]];
   FIRST_ASSUM ACCEPT_TAC]);;

let zeckendorf_decode_fib_upper_bound = prove
 (`!l1 l2.
     zeckendorf (APPEND l1 l2) ==>
     decode_fib l1 < fibonacci (LENGTH l1 + 2)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`l1 : bool list`, `l1 : bool list`) THEN
  LIST_INDUCT_TAC THENL
  [DISCH_THEN (K ALL_TAC) THEN
   REWRITE_TAC [decode_fib_nil; LENGTH; ADD_CLAUSES; fibonacci_def; LT_NZ] THEN
   REWRITE_TAC [ONE; NOT_SUC];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [APPEND] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL [`0`; `h : bool`; `t : bool list`; `l2 : bool list`]
       zeckendorf_decode_fib_dest_upper_bound) THEN
  ASM_REWRITE_TAC
    [decode_fib_def; ADD_CLAUSES; fibonacci_zero; fibonacci_one;
     GSYM fibonacci_add2] THEN
  SUBGOAL_THEN `fibonacci (if h then 1 else 2) = 1` SUBST1_TAC THENL
  [BOOL_CASES_TAC `h : bool` THEN
   REWRITE_TAC [fibonacci_one; fibonacci_two];
   REWRITE_TAC [ONE; TWO; THREE; ADD_CLAUSES; LENGTH; LE_SUC_LT]]);;

export_thm zeckendorf_decode_fib_upper_bound;;

let bool_list_difference_lemma = prove
 (`!l1 l2.
     LENGTH l1 = LENGTH l2 /\
     ~(l1 = l2) ==>
     ?k1 k2 h t.
       l1 = APPEND k1 (CONS h t) /\
       l2 = APPEND k2 (CONS (~h) t)`,
  LIST_INDUCT_TAC THENL
  [LIST_INDUCT_TAC THENL
   [REWRITE_TAC [];
    REWRITE_TAC [LENGTH; NOT_SUC]];
   ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [LENGTH; NOT_SUC];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [LENGTH; SUC_INJ; CONS_11;
               TAUT `!x y. ~(x /\ y) <=> (y /\ ~x) \/ ~y`] THEN
  STRIP_TAC THENL
  [EXISTS_TAC `[] : bool list` THEN
   EXISTS_TAC `[] : bool list` THEN
   EXISTS_TAC `h : bool` THEN
   EXISTS_TAC `t' : bool list` THEN
   ASM_REWRITE_TAC [APPEND; CONS_11] THEN
   MATCH_MP_TAC (TAUT `!x y. ~(y <=> x) ==> (x <=> ~y)`) THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `t' : bool list`) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  EXISTS_TAC `CONS (h : bool) k1` THEN
  EXISTS_TAC `CONS (h' : bool) k2` THEN
  EXISTS_TAC `h'' : bool` THEN
  EXISTS_TAC `t'' : bool list` THEN
  ASM_REWRITE_TAC [APPEND; CONS_11]);;

let zeckendorf_decode_fib_dominate = prove
 (`!l1 l2 t.
     LENGTH l1 = LENGTH l2 /\
     zeckendorf (APPEND l1 (CONS F t)) /\
     zeckendorf (APPEND l2 (CONS T t)) ==>
     decode_fib (APPEND l1 (CONS F t)) < decode_fib (APPEND l2 (CONS T t))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM APPEND_SING] THEN
  REWRITE_TAC [APPEND_ASSOC] THEN
  ONCE_REWRITE_TAC [decode_fib_append] THEN
  ASM_REWRITE_TAC [LT_ADD_RCANCEL; LENGTH_APPEND; LENGTH] THEN
  REWRITE_TAC [decode_fib_append; decode_fib_dest_def; GSYM fibonacci_add2] THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF; ADD_CLAUSES] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `fibonacci (LENGTH (l1 : bool list) + 2)` THEN
  STRIP_TAC THENL
  [MATCH_MP_TAC zeckendorf_decode_fib_upper_bound THEN
   EXISTS_TAC `CONS F t` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ASM_REWRITE_TAC [LE_ADDR]]);;

let zeckendorf_decode_fib_length_mono = prove
 (`!l1 l2.
     zeckendorf l1 /\ zeckendorf l2 /\ LENGTH l1 < LENGTH l2 ==>
     decode_fib l1 < decode_fib l2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `fibonacci (LENGTH (l1 : bool list) + 2)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC zeckendorf_decode_fib_upper_bound THEN
   EXISTS_TAC `[] : bool list` THEN
   ASM_REWRITE_TAC [APPEND_NIL];
   ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `fibonacci (LENGTH (l2 : bool list) + 1)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC fibonacci_mono_imp THEN
   ASM_REWRITE_TAC [TWO; ONE; ADD_CLAUSES; LE_SUC_LT; LT_SUC];
   ALL_TAC] THEN
  MATCH_MP_TAC zeckendorf_decode_fib_lower_bound THEN
  ASM_REWRITE_TAC [NULL_EQ_NIL] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `LENGTH (l1 : bool list) < LENGTH (l2 : bool list)` THEN
  ASM_REWRITE_TAC [LENGTH; LT]);;

export_thm zeckendorf_decode_fib_length_mono;;

let zeckendorf_decode_fib_inj = prove
 (`!l1 l2.
     zeckendorf l1 /\ zeckendorf l2 /\ decode_fib l1 = decode_fib l2 ==>
     l1 = l2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM LE_ANTISYM; GSYM NOT_LT] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (l1 : bool list) = LENGTH (l2 : bool list)` MP_TAC THENL
  [REWRITE_TAC [GSYM LE_ANTISYM] THEN
   REWRITE_TAC [GSYM NOT_LT] THEN
   CONJ_TAC THENL
   [STRIP_TAC THEN
    UNDISCH_TAC `~(decode_fib l2 < decode_fib l1)` THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC zeckendorf_decode_fib_length_mono THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    UNDISCH_TAC `~(decode_fib l1 < decode_fib l2)` THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC zeckendorf_decode_fib_length_mono THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`l1 : bool list`; `l2 : bool list`]
                bool_list_difference_lemma) THEN
  BOOL_CASES_TAC `l1 = (l2 : bool list)` THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `h : bool` THENL
  [UNDISCH_TAC `~(decode_fib l2 < decode_fib l1)` THEN
   POP_ASSUM (SUBST_VAR_TAC o EQT_INTRO) THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   REWRITE_TAC [LENGTH_APPEND; LENGTH; EQ_ADD_RCANCEL] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC zeckendorf_decode_fib_dominate THEN
   ASM_REWRITE_TAC [];
   UNDISCH_TAC `~(decode_fib l1 < decode_fib l2)` THEN
   POP_ASSUM (SUBST_VAR_TAC o EQF_INTRO) THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   REWRITE_TAC [LENGTH_APPEND; LENGTH; EQ_ADD_RCANCEL] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC zeckendorf_decode_fib_dominate THEN
   ASM_REWRITE_TAC []]);;

export_thm zeckendorf_decode_fib_inj;;

let zeckendorf_encode_fib_mk = prove
 (`!n k l.
     ~NULL l /\
     ((n < fibonacci (k + 1) /\ zeckendorf l) \/
      (n < fibonacci (k + 2) /\ zeckendorf (CONS T l))) ==>
     zeckendorf (encode_fib_mk l n (fibonacci (k + 1)) (fibonacci k))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [fibonacci_add2] THEN
  SPEC_TAC (`l : bool list`, `l : bool list`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [encode_fib_mk_def] THEN
   REWRITE_TAC [fibonacci_def] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC zeckendorf_cons_imp THEN
   EXISTS_TAC `T` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM ADD1; fibonacci_suc_suc; NOT_SUC] THEN
  REWRITE_TAC [ADD1] THEN
  ONCE_REWRITE_TAC [encode_fib_mk_def] THEN
  SUBGOAL_THEN `fibonacci (k + 1) = 0 <=> F` SUBST1_TAC THENL
  [REWRITE_TAC [fibonacci_eq_zero; GSYM ADD1; NOT_SUC];
   ALL_TAC] THEN
  REWRITE_TAC [] THEN
  REWRITE_TAC [ADD_SUB2] THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC [GSYM NOT_LT] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [NULL] THEN
   DISJ2_TAC THEN
   ASM_REWRITE_TAC [zeckendorf_def; NULL; HD];
   ALL_TAC] THEN
  COND_CASES_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [REWRITE_TAC [NULL];
    DISJ1_TAC THEN
    CONJ_TAC THENL
    [POP_ASSUM (MP_TAC o REWRITE_RULE [LE_EXISTS]) THEN
     DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
     REWRITE_TAC [ADD_SUB2] THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [LT_ADD_LCANCEL];
     FIRST_ASSUM ACCEPT_TAC]];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [REWRITE_TAC [NULL];
    DISJ2_TAC THEN
    ASM_REWRITE_TAC [GSYM NOT_LE] THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM (K ALL_TAC) THEN
    ASM_REWRITE_TAC [zeckendorf_def; NULL; HD] THEN
    STRIP_TAC]]);;

let zeckendorf_encode_fib_find = prove
 (`!n k.
     fibonacci (k + 1) <= n ==>
     zeckendorf (encode_fib_find n (fibonacci (k + 1)) (fibonacci k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?j. fibonacci (j + 1) <= n /\ n < fibonacci (j + 2) /\ k <= j`
    MP_TAC THENL
  [MP_TAC (SPEC `n : num` fibonacci_interval) THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `k + 1 < SUC k'`
     (MP_TAC o REWRITE_RULE [LT_SUC_LE; LE_EXISTS]) THENL
   [REWRITE_TAC [ADD1] THEN
    MATCH_MP_TAC fibonacci_strictly_mono_imp' THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `n : num` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
   EXISTS_TAC `k + d : num` THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [ADD_CLAUSES; ONE; TWO; LE_ADD] THEN
   REPEAT STRIP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  STRIP_TAC THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE [LE_EXISTS]) THEN
  DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [IMP_IMP] THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  SPEC_TAC (`d : num`, `d : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [ADD_CLAUSES] THEN
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [encode_fib_find_def] THEN
   REWRITE_TAC [GSYM fibonacci_add2] THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   ONCE_REWRITE_TAC [encode_fib_mk_def] THEN
   ASM_REWRITE_TAC [fibonacci_eq_zero] THEN
   COND_CASES_TAC THENL
   [ACCEPT_TAC zeckendorf_nil;
    ALL_TAC] THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   REWRITE_TAC [fibonacci_def] THEN
   MP_TAC (SPEC `k : num` num_CASES) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [ONE; TWO; NOT_SUC; ADD_CLAUSES] THEN
   REWRITE_TAC [LE_EXISTS] THEN
   DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
   REWRITE_TAC [LT_ADD_LCANCEL; ADD_SUB2] THEN
   REWRITE_TAC [fibonacci_suc_suc; ADD_SUB2] THEN
   REWRITE_TAC [ADD1] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC zeckendorf_encode_fib_mk THEN
   STRIP_TAC THENL
   [REWRITE_TAC [NULL];
    ALL_TAC] THEN
   DISJ1_TAC THEN
   ASM_REWRITE_TAC [zeckendorf_def; NULL; HD];
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC [ONE; TWO; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [encode_fib_find_def] THEN
  REWRITE_TAC [GSYM fibonacci_suc_suc] THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `fibonacci (SUC (SUC (k + d))) <= n` THEN
   REWRITE_TAC [NOT_LE] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `fibonacci (SUC (SUC k))` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC fibonacci_mono_imp THEN
   REWRITE_TAC [LE_SUC; LE_ADD];
   ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [ADD_CLAUSES]);;

let zeckendorf_encode_fib = prove
 (`!n. zeckendorf (encode_fib n)`,
  GEN_TAC THEN
  REWRITE_TAC [encode_fib_def] THEN
  MP_TAC (SPEC `n : num` num_CASES) THEN
  STRIP_TAC THENL
  [ONCE_REWRITE_TAC [encode_fib_find_def] THEN
   ASM_REWRITE_TAC
     [LET_DEF; LET_END_DEF; ONE; LT_SUC_LE; LE_0; ADD_CLAUSES] THEN
   ONCE_REWRITE_TAC [encode_fib_mk_def] THEN
   REWRITE_TAC [zeckendorf_nil];
   MP_TAC (SPECL [`n : num`; `0`] zeckendorf_encode_fib_find) THEN
   REWRITE_TAC [ADD_CLAUSES; fibonacci_def] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [ONE; LE_SUC; LE_0]]);;

export_thm zeckendorf_encode_fib;;

let zeckendorf_decode_encode_fib = prove
 (`!l. zeckendorf l <=> encode_fib (decode_fib l) = l`,
  GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   MATCH_MP_TAC zeckendorf_decode_fib_inj THEN
   ASM_REWRITE_TAC [zeckendorf_encode_fib; encode_decode_fib];
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_ACCEPT_TAC zeckendorf_encode_fib]);;

export_thm zeckendorf_decode_encode_fib;;

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* Prototyping in Standard ML.                                               *)
(* ------------------------------------------------------------------------- *)

(*
local
  fun mkFib l n f p =
      if p = 0 then l
      else if f <= n then mkFib (true :: l) (n - f) p (f - p)
      else mkFib (false :: l) n p (f - p);

  fun findMax n f p =
      let
        val s = f + p
      in
        if n < s then mkFib [] n f p else findMax n s f
      end;
in
  fun encode n = findMax n 1 0;
end;

encode 0;
encode 1;
encode 2;
encode 10;
encode 11;
encode 12;
encode 13;

local
  fun destFib f p l =
      case l of
        [] => 0
      | h :: t =>
        let
          val s = f + p

          val n = destFib s f t
        in
          if h then s + n else n
        end;
in
  fun decode l = destFib 1 0 l;
end;

(decode o encode) 0;
(decode o encode) 1;
(decode o encode) 2;
(decode o encode) 10;
(decode o encode) 11;
(decode o encode) 12;
(decode o encode) 13;

(* A decoding function that just uses subtraction *)

local
  fun destFib b n d f p l =
      case l of
        [] => if b then n - d else d - n
      | h :: t =>
        let
          val s = p - f

          val n = if h then n - s else n
        in
          destFib (not b) d n s f t
        end;
in
  val decodeSub = destFib true 0 0 1 0;
end;

(decodeSub o encode) 0;
(decodeSub o encode) 1;
(decodeSub o encode) 2;
(decodeSub o encode) 10;
(decodeSub o encode) 11;
(decodeSub o encode) 12;
(decodeSub o encode) 13;
*)
