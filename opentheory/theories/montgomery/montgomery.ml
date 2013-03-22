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

let (montgomery_double_exp_zero,montgomery_double_exp_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!n r k a. montgomery_double_exp n r k a 0 = a) /\
     (!n r k a m.
        montgomery_double_exp n r k a (SUC m) =
        let b = montgomery_reduce n r k (a * a) in
        let c = if r <= b then b - n else b in
        montgomery_double_exp n r k c m)` in
  CONJ_PAIR def;;

export_thm montgomery_double_exp_zero;;
export_thm montgomery_double_exp_suc;;

let montgomery_double_exp_def =
    CONJ montgomery_double_exp_zero montgomery_double_exp_suc;;

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
  (`!n r k m a.
      ~(n = 0) /\
      ~(r = 0) /\
      a <= r * m ==>
      montgomery_reduce n r k a < m + n`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [montgomery_reduce_def] THEN
   MATCH_MP_TAC LT_LDIV THEN
   REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `a + r * n : num` THEN
   ASM_REWRITE_TAC [LT_ADD_LCANCEL; LE_ADD_RCANCEL; LT_MULT_RCANCEL] THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm montgomery_reduce_bound;;

let montgomery_reduce_normalized_bound = prove
  (`!n r k a.
      ~(n = 0) /\
      ~(r = 0) /\
      a <= r * n ==>
      montgomery_reduce n r k a < 2 * n`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [MULT_2] THEN
   MATCH_MP_TAC montgomery_reduce_bound THEN
   ASM_REWRITE_TAC []);;

export_thm montgomery_reduce_normalized_bound;;

let montgomery_reduce_unnormalized_bound = prove
  (`!n r k a.
      ~(n = 0) /\
      ~(r = 0) /\
      a <= r * r ==>
      montgomery_reduce n r k a < r + n`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC montgomery_reduce_bound THEN
   ASM_REWRITE_TAC []);;

export_thm montgomery_reduce_unnormalized_bound;;

let montgomery_double_exp_correct = prove
  (`!n r s k a m.
      ~(n = 0) /\
      n <= r /\
      r * s = k * n + 1 ==>
      montgomery_double_exp n r k a m MOD n =
      ((a * s) EXP (2 EXP m) * r) MOD n`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`a : num`, `a : num`) THEN
   SPEC_TAC (`m : num`, `m : num`) THEN
   INDUCT_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC [montgomery_double_exp_zero; EXP_0; EXP_1] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    MP_TAC (SPEC `n : num` MOD_MULT_RMOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `(s * r) MOD n = 1 MOD n` SUBST1_TAC THENL
    [MATCH_MP_TAC MOD_EQ THEN
     EXISTS_TAC `k : num` THEN
     ONCE_REWRITE_TAC [MULT_SYM; ADD_SYM] THEN
     FIRST_ASSUM ACCEPT_TAC;
     ASM_REWRITE_TAC [MULT_1]];
    ALL_TAC] THEN
   GEN_TAC THEN
   ASM_REWRITE_TAC
     [montgomery_double_exp_suc; EXP_SUC; LET_DEF; LET_END_DEF; EXP_MULT;
      EXP_2] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MP_TAC (SPEC `n : num` MOD_EXP_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   MP_TAC (SPEC `n : num` MOD_MULT_LMOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MP_TAC (SPEC `n : num` MOD_EXP_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [MULT_ASSOC] THEN
   MP_TAC (SPEC `n : num` MOD_MULT_LMOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   REWRITE_TAC [MULT_ASSOC] THEN
   COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `((montgomery_reduce n r k (a * a) - n) + n) MOD n` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EQ_SYM THEN
     MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
     MP_TAC (SPEC `n : num` MOD_REFL) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [ADD_0] THEN
     MATCH_MP_TAC MOD_MOD_REFL THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `montgomery_reduce n r k (a * a) MOD n` THEN
     CONJ_TAC THENL
     [AP_THM_TAC THEN
      AP_TERM_TAC THEN
      MATCH_MP_TAC SUB_ADD THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `r : num` THEN
      ASM_REWRITE_TAC [];
      MATCH_MP_TAC montgomery_reduce_correct THEN
      ASM_REWRITE_TAC []]];
    MATCH_MP_TAC montgomery_reduce_correct THEN
    ASM_REWRITE_TAC []]);;

export_thm montgomery_double_exp_correct;;

let montgomery_double_exp_bound = prove
  (`!n r k a m.
      ~(n = 0) /\
      n <= r /\
      a < r ==>
      montgomery_double_exp n r k a m < r`,
   REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   SPEC_TAC (`a : num`, `a : num`) THEN
   SPEC_TAC (`m : num`, `m : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [montgomery_double_exp_zero];
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [montgomery_double_exp_suc; LET_DEF; LET_END_DEF] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [GSYM NOT_LT] THEN
   ASM_CASES_TAC `montgomery_reduce n r k (a * a) < r` THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   ONCE_REWRITE_TAC [GSYM (SPEC `n : num` LT_ADD_RCANCEL)] THEN
   SUBGOAL_THEN
     `montgomery_reduce n r k (a * a) - n + n =
      montgomery_reduce n r k (a * a)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUB_ADD THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [GSYM NOT_LT];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MATCH_MP_TAC montgomery_reduce_unnormalized_bound THEN
   ASM_REWRITE_TAC [] THEN
   CONJ_TAC THENL
   [DISCH_THEN SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [NOT_LT; LE_0];
    POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LT_LE]) THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `a * r : num` THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL; LE_MULT_RCANCEL]]);;

export_thm montgomery_double_exp_bound;;

(* ------------------------------------------------------------------------- *)
(* Definition of a Montgomery multiplication circuit.                        *)
(* ------------------------------------------------------------------------- *)

(***
let montgomery_comb_def = new_definition
  `!n k rx ry rz xs xc
    ys yc sa sb sx sy sz so ca cb ks kc ns nc rs rc
    ys' yc' sa' sb' sx' sy' sz' so' ca' cb' ks' kc' ns' nc' rs' rc'
    zs' zc'.
      montgomery_comb
        n k rx ry rz xs xc
        ys yc sa sb sx sy sz so ca cb ks kc ns nc rs rc
        ys' yc' sa' sb' sx' sy' sz' so' ca' cb' ks' kc' ns' nc' rs' rc'
        zs' zc' <=>
      ?r
       ys0 ys1 yc0 yc1
       ys0' ys1' yc0' yc1'.
         width n = r /\
         width k = r /\
         width rx = r /\
         width ry = r /\
         width rz = r /\
         width xs = r /\
         width xc = r
         /\
         (width ys = r /\
          wire ys 0 ys0 /\
          bsub ys 1 (r-1) ys1) /\
         (width yc = r /\
          bsub yc 0 (r-1) yc0 /\
          wire yc (r-1) yc1) /\
         width sa = r /\
         width sb = r /\
         width ca = r /\
         width cb = r /\
         width ks = r /\
         width kc = r /\
         width ns = r /\
         width nc = r /\
         width rs = r /\
         width rc = r
         /\
         (width ys' = r /\
          bsub ys' 0 (r-1) ys0' /\
          wire ys' (r-1) ys1') /\
         (width yc' = r /\
          bsub yc' 0 (r-1) yc0' /\
          wire yc' (r-1) yc1') /\
         width sa' = r /\
         width sb' = r /\
         width ca' = r /\
         width cb' = r /\
         width ks' = r /\
         width kc' = r /\
         width ns' = r /\
         width nc' = r /\
         width rs' = r /\
         width rc' = r
         /\
         width zs' = r /\
         width zc' = r
         /\
         compressor2 ys1 yc0 ys0' yc0' /\
         ys1' = yc1 /\
         yc1' = ground`;;

export_thm montgomery_comb_def;;

(* ------------------------------------------------------------------------- *)
(* Correctness of a Montgomery multiplication circuit.                       *)
(* ------------------------------------------------------------------------- *)

let montgomery_comb_ysc = prove
 (`!n k rx ry rz xs xc
    ys yc sa sb sx sy sz so ca cb ks kc ns nc rs rc
    ys' yc' sa' sb' sx' sy' sz' so' ca' cb' ks' kc' ns' nc' rs' rc'
    zs' zc' t.
      montgomery_comb
        n k rx ry rz xs xc
        ys yc sa sb sx sy sz so ca cb ks kc ns nc rs rc
        ys' yc' sa' sb' sx' sy' sz' so' ca' cb' ks' kc' ns' nc' rs' rc'
        zs' zc' ==>
      bits_to_num (bsignal ys' t) + 2 * bits_to_num (bsignal yc' t) =
      (bits_to_num (bsignal ys t) + 2 * bits_to_num (bsignal yc t)) DIV 2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [montgomery_comb_def] THEN
  STRIP_TAC THEN

***)

(* ------------------------------------------------------------------------- *)
(* Automatically generating verified Montgomery multiplication circuits.     *)
(* ------------------------------------------------------------------------- *)

let rec bitwidth_num n =
    if eq_num n num_0 then num_0 else
    succ_num (bitwidth_num (quo_num n num_2));;

let mk_montgomery n =
    let r = mk_numeral (add_num (bitwidth_num (dest_numeral n)) num_2) in
    let egcd =
        let rth = NUM_REDUCE_CONV (mk_comb (`(EXP) 2`, r)) in
        let eth = prove_egcd (rhs (concl rth)) n in
        CONV_RULE (LAND_CONV (REWR_CONV MULT_SYM THENC
                              LAND_CONV (REWR_CONV (SYM rth)))) eth in
    let s = rand (lhs (concl egcd)) in
    let k = lhand (lhand (rhs (concl egcd))) in
    (egcd,s,k);;

(* ------------------------------------------------------------------------- *)
(* LCS35 Time Capsule Crypto-Puzzle [1].                                     *)
(*                                                                           *)
(* 1. http://people.csail.mit.edu/rivest/lcs35-puzzle-description.txt        *)
(* ------------------------------------------------------------------------- *)

(***
let time_capsule_n_def = new_definition
  `time_capsule_n =
   6314466083072888893799357126131292332363298818330841375588990772701957128924885547308446055753206513618346628848948088663500368480396588171361987660521897267810162280557475393838308261759713218926668611776954526391570120690939973680089721274464666423319187806830552067951253070082020241246233982410737753705127344494169501180975241890667963858754856319805507273709904397119733614666701543905360152543373982524579313575317653646331989064651402133985265800341991903982192844710212464887459388853582070318084289023209710907032396934919962778995323320184064522476463966355937367009369212758092086293198727008292431243681`;;

export_thm time_capsule_n_def;;

let time_capsule_t_def = new_definition
  `time_capsule_t = 79685186856218`;;

export_thm time_capsule_t_def;;

let time_capsule_z_def = new_definition
  `time_capsule_z =
   4273385266812394147070994861525419078076239304748427595531276995752128020213613672254516516003537339494956807602382848752586901990223796385882918398855224985458519974818490745795238804226283637519132355620865854807750610249277739682050363696697850022630763190035330004501577720670871722527280166278354004638073890333421755189887803390706693131249675969620871735333181071167574435841870740398493890811235683625826527602500294010908702312885095784549814408886297505226010693375643169403606313753753943664426620220505295457067077583219793772829893613745614142047193712972117251792879310395477535810302267611143659071382`;;

export_thm time_capsule_z_def;;
***)

logfile_end ();;
