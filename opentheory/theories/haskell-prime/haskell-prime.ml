(* ========================================================================= *)
(* PRIME NUMBERS                                                             *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for prime numbers.                                        *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/haskell-prime/haskell-prime.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of prime numbers.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-prime-def";;

let sieveH_tybij = define_haskell_type
  `:sieve`
  [];;

export_thm sieveH_tybij;;

let mk_sieveH_def = define_haskell_const
  `mk_sieve : num # (num # num # num) list -> sieve`;;

export_thm mk_sieveH_def;;

let dest_sieveH_def = define_haskell_const
  `dest_sieve : sieve -> num # (num # num # num) list`;;

export_thm dest_sieveH_def;;

let max_sieveH_def = define_haskell_const
  `max_sieve : sieve -> num`;;

export_thm max_sieveH_def;;

let inc_counters_sieveH_def = define_haskell_const
  `inc_counters_sieve :
   num -> num -> (num # num # num) list -> bool # (num # num # num) list`;;

export_thm inc_counters_sieveH_def;;

let inc_sieveH_def = define_haskell_const
  `inc_sieve : sieve -> bool # sieve`;;

export_thm inc_sieveH_def;;

let init_sieveH_def = define_haskell_const
  `init_sieve : sieve`;;

export_thm init_sieveH_def;;

let next_sieveH_def = define_haskell_const
  `next_sieve : sieve -> num # sieve`;;

export_thm next_sieveH_def;;

let primesH_def = define_haskell_const
  `primes : num stream`;;

export_thm primesH_def;;

(* ------------------------------------------------------------------------- *)
(* Haskell source for prime numbers.                                         *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-prime-src";;

let () = (export_haskell_thm o prove)
 (`!s. mk_sieveH (dest_sieveH s) = s`,
  HASKELL_TAC [sieve_tybij]);;

let () = (export_haskell_thm o prove)
 (`!s. max_sieveH s = FST (dest_sieveH s)`,
  HASKELL_TAC [max_sieve_def]);;

let () = (export_haskell_thm o prove)
 (`init_sieveH = mk_sieveH (1,[])`,
  HASKELL_TAC [init_sieve_def]);;

let () = (export_haskell_thm o prove)
 (`(!n i. inc_counters_sieveH n i [] = (T,[n,0,0])) /\
   (!n i p k j ps.
      inc_counters_sieveH n i (CONS (p,k,j) ps) =
      let k' = (k + i) MOD p in
      let j' = j + i in
      if k' = 0 then (F, CONS (p,0,j') ps) else
      let (b,ps') = inc_counters_sieveH n j' ps in
      (b,CONS (p,k',0) ps'))`,
  HASKELL_TAC [inc_counters_sieve_def]);;

let () = (export_haskell_thm o prove)
 (`inc_sieveH =
   \s.
     let (n,ps) = dest_sieveH s in
     let n' = n + 1 in
     let (b,ps') = inc_counters_sieveH n' 1 ps in
     (b, mk_sieveH (n',ps'))`,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
  X_GEN_TAC `s : sieveH` THEN
  HASKELL_TAC [inc_sieve_def] THEN
  PAIR_CASES_TAC `dest_sieve (destH_sieveH s)` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `n : num`
      (X_CHOOSE_THEN `ps : (num # num # num) list` STRIP_ASSUME_TAC)) THEN
  PAIR_CASES_TAC `inc_counters_sieve (n + 1) 1 ps` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `b : bool`
      (X_CHOOSE_THEN `ps' : (num # num # num) list` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF; map_snd_def]);;

let () = (export_haskell_thm o prove)
 (`!s.
     next_sieveH s =
     let (b,s') = inc_sieveH s in
     if b then (max_sieveH s', s') else
     next_sieveH s'`,
  GEN_TAC THEN
  HASKELL_TAC [] THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [next_sieve_def])) THEN
  PAIR_CASES_TAC `inc_sieve (destH_sieveH s)` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `b : bool`
      (X_CHOOSE_THEN `s' : sieve` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF; map_snd_def] THEN
  BOOL_CASES_TAC `b : bool` THEN
  HASKELL_TAC []);;

let () = (export_haskell_thm o prove)
 (`primesH = sunfoldH next_sieveH init_sieveH`,
  HASKELL_TAC [GSYM correct_sieve] THEN
  MATCH_MP_TAC snth_eq_imp THEN
  SPEC_TAC (`init_sieve`, `s : sieve`) THEN
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  INDUCT_TAC THENL
  [GEN_TAC THEN
   ONCE_REWRITE_TAC [sunfold] THEN
   PAIR_CASES_TAC `next_sieve s` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `p : num`
       (X_CHOOSE_THEN `s' : sieve` STRIP_ASSUME_TAC)) THEN
   ASM_HASKELL_TAC [LET_DEF; LET_END_DEF; snth_scons_zero];
   GEN_TAC THEN
   ONCE_REWRITE_TAC [sunfold] THEN
   PAIR_CASES_TAC `next_sieve s` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `p : num`
       (X_CHOOSE_THEN `s' : sieve` STRIP_ASSUME_TAC)) THEN
   ASM_HASKELL_TAC [LET_DEF; LET_END_DEF; snth_scons_suc]]);;

(* ------------------------------------------------------------------------- *)
(* QuickCheck tests for prime numbers.                                       *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-prime-test";;

let () = (export_haskell_thm o prove)
 (`~(snthH primesH 0 = 0)`,
  HASKELL_TAC [] THEN
  STRIP_ASSUME_TAC (REWRITE_RULE [] (SPEC `primes` primes_equiv_test)));;

let () = (export_haskell_thm o prove)
 (`!r.
     let (i,r') = rdecode_geometricH r in
     let (j,r'') = rdecode_geometricH r' in
     (snthH primesH i <= snthH primesH j <=> i <= j)`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_geometricH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `i : num`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  PAIR_CASES_TAC `rdecode_geometricH r'` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `j : num`
      (X_CHOOSE_THEN `r'' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  MATCH_ACCEPT_TAC primes_mono_le);;

let () = (export_haskell_thm o prove)
 (`!r.
     let (i,r') = rdecode_geometricH r in
     let (j,r'') = rdecode_geometricH r' in
     ~dividesH (snthH primesH i) (snthH primesH ((i + j) + 1))`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_geometricH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `i : num`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  PAIR_CASES_TAC `rdecode_geometricH r'` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `j : num`
      (X_CHOOSE_THEN `r'' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [GSYM ADD_ASSOC] THEN
  STRIP_ASSUME_TAC (REWRITE_RULE [] (SPEC `primes` primes_equiv_test)) THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

let () = (export_haskell_thm o prove)
 (`!r.
     let (n,r') = rdecode_fibH r in
     let (i,r'') = rdecode_geometricH r' in
     EX (\p. dividesH p (n + 2)) (stakeH primesH i) \/
     snthH primesH i <= n + 2`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_fibH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `n : num`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  PAIR_CASES_TAC `rdecode_geometricH r'` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `i : num`
      (X_CHOOSE_THEN `r'' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  STRIP_ASSUME_TAC (REWRITE_RULE [] (SPEC `primes` primes_equiv_test)) THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

logfile_end ();;
