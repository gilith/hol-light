(* ========================================================================= *)
(* MONTGOMERY MULTIPLICATION                                                 *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for Montgomery multiplication.                            *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/montgomery/montgomery.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of Montgomery multiplication [1].                              *)
(*                                                                           *)
(* 1. http://en.wikipedia.org/wiki/Montgomery_reduction                      *)
(* ------------------------------------------------------------------------- *)

logfile "montgomery-def";;

let montgomery_reduce_def = new_definition
  `!n r k a.
     montgomery_reduce n r k a =
     (a + ((a * k) MOD r) * n) DIV r`;;

export_thm montgomery_reduce_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of Montgomery multiplication.                                  *)
(* ------------------------------------------------------------------------- *)

logfile "montgomery-thm";;

let montgomery_reduce_correct = prove
  (`!n r s k a.
      ~(n = 0) /\
      r * s = k * n + 1 ==>
      montgomery_reduce n r k a MOD n = (a * s) MOD n`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [ZERO_MULT; GSYM ADD1; NOT_SUC];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `(montgomery_reduce n r k a * (r * s)) MOD n` THEN
   CONJ_TAC THENL
   [SPEC_TAC (`montgomery_reduce n r k a`,`m : num`) THEN
    GEN_TAC THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_REWRITE_TAC [LEFT_ADD_DISTRIB; MULT_1] THEN
    MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `(m * k * n) MOD n = 0` SUBST1_TAC THENL
    [REWRITE_TAC [MULT_ASSOC] THEN
     ONCE_REWRITE_TAC [MULT_SYM] THEN
     MATCH_MP_TAC MOD_MULT THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    REWRITE_TAC [ZERO_ADD] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC MOD_MOD_REFL THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [MULT_ASSOC; montgomery_reduce_def] THEN
   MP_TAC (SPEC `n : num` MOD_MULT_MOD2') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MP_TAC (SPECL [`a + (a * k) MOD r * n`; `r : num`] DIVISION_DEF_DIV) THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN `(a + (a * k) MOD r * n) MOD r = 0` SUBST1_TAC THENL
   [MP_TAC (SPEC `r : num` MOD_MOD_REFL') THEN
    MP_TAC (SPEC `r : num` MOD_MULT_MOD2') THEN
    MP_TAC (SPEC `r : num` MOD_ADD_MOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
    POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
    SUBGOAL_THEN `a + (a * k) * n = a * (1 + k * n)` SUBST1_TAC THENL
    [REWRITE_TAC [LEFT_ADD_DISTRIB; MULT_1; MULT_ASSOC];
     ALL_TAC] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    MATCH_MP_TAC MOD_MULT THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [ADD_0] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   SUBGOAL_THEN `((a * k) MOD r * n) MOD n = 0` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC [MULT_SYM] THEN
    MATCH_MP_TAC MOD_MULT THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [ADD_0] THEN
   MATCH_MP_TAC MOD_MOD_REFL THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm montgomery_reduce_correct;;

let montgomery_reduce_bound = prove
  (`!n r k a.
      ~(n = 0) /\
      ~(r = 0) /\
      a <= n * r ==>
      montgomery_reduce n r k a < 2 * n`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [montgomery_reduce_def] THEN
   MATCH_MP_TAC LT_LDIV THEN
   CONV_TAC (RAND_CONV (REWR_CONV MULT_SYM)) THEN
   REWRITE_TAC [GSYM MULT_ASSOC] THEN
   REWRITE_TAC [MULT_2] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `a + n * r : num` THEN
   ASM_REWRITE_TAC [LT_ADD_LCANCEL; LE_ADD_RCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV MULT_SYM)) THEN
   ASM_REWRITE_TAC [LT_MULT_RCANCEL] THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm montgomery_reduce_bound;;

let montgomery_reduce_unnormalized_bound = prove
  (`!n r k a.
      ~(n = 0) /\
      ~(r = 0) /\
      a <= r * r ==>
      montgomery_reduce n r k a < r + n`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [montgomery_reduce_def] THEN
   MATCH_MP_TAC LT_LDIV THEN
   REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `a + r * n : num` THEN
   ASM_REWRITE_TAC [LT_ADD_LCANCEL; LE_ADD_RCANCEL; LT_MULT_RCANCEL] THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm montgomery_reduce_unnormalized_bound;;

(* ------------------------------------------------------------------------- *)
(* A Montgomery multiplication circuit to calculate double exponentials.     *)
(* ------------------------------------------------------------------------- *)

(***
let bits_and_def = new_definition
  `!m n.
     bits_and m n =
     if LENGTH l1 <= LENGTH l2 then
       zipwith ( /\ ) l1 (take (LENGTH l1) l2)
     else
       zipwith ( /\ ) (take (LENGTH l2) l1) l2`;;

let bits_or_def = new_definition
  `!l1 l2.
     bits_or l1 l2 =
     if LENGTH l1 <= LENGTH l2 then
       APPEND
         (zipwith ( \/ ) l1 (take (LENGTH l1) l2))
         (drop (LENGTH l1) l2)
     else
       zipwith ( \/ ) (take (LENGTH l2) l1) l2`;;

let bits_add_def = new_definition
  `!a b. bits_add a b = num_to_bits (bits_to_num a + bits_to_num b)`;;

let bits_multiply_def = new_definition
  `!a b. bits_multiply a b = num_to_bits (bits_to_num a * bits_to_num b)`;;

let bits_montgomery_reduce_def = new_definition
  `!n r k a.
     bits_montgomery_reduce n r k a =
     num_to_bits
       (montgomery_reduce (bits_to_num n) (2 EXP r) (bits_to_num k)
         (bits_to_num a))`;;



let bits_montgomery_reduce = prove
  (`!n r k a.
      bits_to_num (bits_montgomery_reduce n r k a) =
      let ak = bits_multiply a k in
      let m = bits_and ak (replicate T r) in
      let mn = bits_multiply m n in
      let amn = bits_add a mn in
      let t = bits_shr amn r in
      let z = if bits_bit t r then bits_sub t n else t in
      bits_to_num (bits_and z (replicate T r))`,
   NO_TAC);;

let montgomery_double_exp_def = new_definition
  `!n r k a m.
     montgomery_double_exp n r k a m =
       let b = m = 0 in
       let a2 = (if b then 1 else a) * a in
       let

     montgomery_reduce n r k a =
     (a + ((a * k) MOD r) * n) DIV r`;;

     ~(r = 0) /\
     2 EXP r * s = k * n + 1 ==>

export_thm montgomery_reduce_def;;

     ~(r = 0) /\
     2 EXP r * s = k * n + 1 ==>
***)

logfile_end ();;
