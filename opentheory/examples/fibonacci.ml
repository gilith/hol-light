(* ------------------------------------------------------------------------- *)
(* Fibonacci encoding of natural numbers.                                    *)
(* Joe Hurd                                                                  *)
(*                                                                           *)
(* See http://en.wikipedia.org/wiki/Fibonacci_coding                         *)
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
     FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
     SUBGOAL_THEN `n + 2 < 2 <=> F` SUBST1_TAC THENL
     [REWRITE_TAC [NOT_LT; LE_ADDR];
      REWRITE_TAC [ADD_SUB; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC [TWO; ADD_CLAUSES] THEN
      REWRITE_TAC [ADD_SUB; ADD1]]]]);;

export_thm fibonacci_exists;;

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

let (decode_fib_dest_nil,decode_fib_dest_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!n f p. decode_fib_dest n f p [] = (n : num)) /\
     (!n f p h t.
        decode_fib_dest n f p (CONS h t) =
          let s = f + p in
          decode_fib_dest (if h then n + s else n) s f t)` in
  CONJ_PAIR def;;

export_thm decode_fib_dest_nil;;
export_thm decode_fib_dest_cons;;

let decode_fib_dest_def = CONJ decode_fib_dest_nil decode_fib_dest_cons;;

let decode_fib_def = new_definition
  `!l. decode_fib l = decode_fib_dest 0 1 0 l`;;

export_thm decode_fib_def;;

logfile "natural-fibonacci-thm";;

let fibonacci_suc_suc = prove
 (`!k. fibonacci (SUC (SUC k)) = fibonacci (SUC k) + fibonacci k`,
  GEN_TAC THEN
  SUBGOAL_THEN `SUC (SUC k) = k + 2` SUBST1_TAC THENL
  [REWRITE_TAC [TWO; ONE; ADD_CLAUSES];
   REWRITE_TAC [fibonacci_def; EQ_ADD_RCANCEL; ADD1]]);;

export_thm fibonacci_suc_suc;;

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

let encode_decode_fib_dest_mk = prove
 (`!n k l.
     n < fibonacci (k + 2) ==>
     decode_fib_dest 0 1 0
       (encode_fib_mk l n (fibonacci (k + 1)) (fibonacci k)) =
     decode_fib_dest n (fibonacci (k + 1)) (fibonacci k) l`,
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
   REWRITE_TAC [];
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
   AP_THM_TAC THEN
   AP_THM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
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

export_thm encode_decode_fib_dest_mk;;

let encode_decode_fib_dest_find = prove
 (`!n k.
     decode_fib_dest 0 1 0
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
   REWRITE_TAC [decode_fib_dest_def];
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
   REWRITE_TAC [decode_fib_dest_def];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `SUC k`) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [ADD_CLAUSES];
   REWRITE_TAC [TWO; ONE; ADD_CLAUSES]]);;

export_thm encode_decode_fib_dest_find;;

let encode_decode_fib = prove
 (`!n. decode_fib (encode_fib n) = n`,
  GEN_TAC THEN
  REWRITE_TAC [decode_fib_def; encode_fib_def] THEN
  MP_TAC (SPECL [`n : num`; `0`] encode_decode_fib_dest_find) THEN
  REWRITE_TAC [ADD_CLAUSES; fibonacci_def]);;

export_thm encode_decode_fib;;

logfile_end ();;

(* Prototyping in Standard ML

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
encode 11;
encode 12;
encode 13;

local
  fun destFib n f p l =
      case l of
        [] => n
      | h :: t =>
        let
          val s = f + p
        in
          destFib (if h then n + s else n) s f t
        end;
in
  fun decode l = destFib 0 1 0 l;
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
      | x :: l =>
        let
          val p = p - f

          val n = if x then n - p else n
        in
          destFib (not b) d n p f l
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
