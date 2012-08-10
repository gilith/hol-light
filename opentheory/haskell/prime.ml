(* ========================================================================= *)
(* PRIMES IN HASKELL                                                         *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(***
type_invention_error := false;;
***)

(* ------------------------------------------------------------------------- *)
(* Definition.                                                               *)
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
(* Source.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-prime-src";;

(* ------------------------------------------------------------------------- *)
(* Testing.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-prime-test";;

logfile_end ();;
