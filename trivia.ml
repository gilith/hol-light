(* ========================================================================= *)
(* Trivial odds and ends.                                                    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "class.ml";;

(* ------------------------------------------------------------------------- *)
(* Combinators. We don't bother with S and K, which seem of little use.      *)
(* ------------------------------------------------------------------------- *)

logfile "function-def";;

parse_as_infix ("o",(26,"right"));;

let o_PRIM_DEF = new_definition
 `(o) = \ (f : B -> C) g (x : A). f (g x)`;;

export_thm o_PRIM_DEF;;

let I_DEF = new_definition
 `I = \ (x:A). x`;;

export_thm I_DEF;;

let K_DEF = new_definition
 `K = \ (x:A) (y:B). x`;;

export_thm K_DEF;;

let S_DEF = new_definition
 `S = \ (f : A -> B -> C) (g : A -> B) (x:A). (f x) (g x)`;;

export_thm S_DEF;;

let C_DEF = new_definition
 `C = \ (f : A -> B -> C) (x:B) (y:A). f y x`;;

export_thm C_DEF;;

let W_DEF = new_definition
 `W = \ (f : A -> A -> B) (x:A). f x x`;;

export_thm W_DEF;;

logfile "function-thm";;

let o_DEF = prove
 (`!f g. (o) (f:B->C) g = \x:A. f(g(x))`,
  REWRITE_TAC [o_PRIM_DEF]);;

let o_THM = prove
 (`!f:B->C. !g:A->B. !x:A. (f o g) x = f(g(x))`,
  PURE_REWRITE_TAC [o_DEF] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  REPEAT GEN_TAC THEN REFL_TAC);;

export_thm o_THM;;

let o_ASSOC' = prove
 (`!f:C->D. !g:B->C. !h:A->B. (f o g) o h = f o (g o h)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [o_DEF] THEN
  CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
  REFL_TAC);;

export_thm o_ASSOC';;

let o_ASSOC = prove
 (`!f:C->D. !g:B->C. !h:A->B. f o (g o h) = (f o g) o h`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_ACCEPT_TAC o_ASSOC');;

export_thm o_ASSOC;;

let I_THM = prove
 (`!x:A. I x = x`,
  REWRITE_TAC [I_DEF]);;

export_thm I_THM;;

let I_O = prove
 (`!f:A->B. I o f = f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_DEF; I_THM]);;

export_thm I_O;;

let O_I = prove
 (`!f:A->B. f o I = f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_DEF; I_THM]);;

export_thm O_I;;

let I_O_ID = prove
 (`!f:A->B. (I o f = f) /\ (f o I = f)`,
  REWRITE_TAC [I_O; O_I]);;

let K_THM = prove
 (`!(x:A) (y:B). K x y = x`,
  REWRITE_TAC [K_DEF]);;

export_thm K_THM;;

let S_THM = prove
 (`!(f : A -> B -> C) (g : A -> B) (x:A). S f g x = (f x) (g x)`,
  REWRITE_TAC [S_DEF]);;

export_thm S_THM;;

let C_THM = prove
 (`!(f : A -> B -> C) (x:B) (y:A). C f x y = f y x`,
  REWRITE_TAC [C_DEF]);;

export_thm C_THM;;

let W_THM = prove
 (`!(f : A -> A -> B) (x:A). W f x = f x x`,
  REWRITE_TAC [W_DEF]);;

export_thm W_THM;;

let SKX_EQ_I = prove
 (`!x. S (K : A -> B -> A) (x : A -> B) = (I : A -> A)`,
  REWRITE_TAC [S_DEF; K_THM; I_DEF]);;

export_thm SKX_EQ_I;;

let CC_EQ_I = prove
  (`!(f : A -> B -> C). C (C f) = f`,
   REWRITE_TAC [C_THM; FUN_EQ_THM]);;

export_thm CC_EQ_I;;

(* ------------------------------------------------------------------------- *)
(* The theory "1" (a 1-element type).                                        *)
(* ------------------------------------------------------------------------- *)

logfile "unit-def";;

let EXISTS_ONE_REP = prove
 (`?b:bool. b`,
  EXISTS_TAC `T` THEN
  BETA_TAC THEN ACCEPT_TAC TRUTH);;

let one_tydef =
  new_type_definition "1" ("one_ABS","one_REP") EXISTS_ONE_REP;;

let one_DEF = new_definition
 `one = @x:1. T`;;

let one = prove
 (`!v:1. v = one`,
  MP_TAC(GEN_ALL (SPEC `one_REP a` (CONJUNCT2 one_tydef))) THEN
  REWRITE_TAC[CONJUNCT1 one_tydef] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM (CONJUNCT1 one_tydef)] THEN
  ASM_REWRITE_TAC[]);;

export_thm one;;

logfile "unit-thm";;

let one_axiom = prove
 (`!f g. f = (g:A->1)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[one] THEN REFL_TAC);;

export_thm one_axiom;;

let one_INDUCT = prove
 (`!p. p one ==> !x. p x`,
  ONCE_REWRITE_TAC[one] THEN REWRITE_TAC[]);;

export_thm one_INDUCT;;

let one_RECURSION = prove
 (`!e:A. ?fn. fn one = e`,
  GEN_TAC THEN EXISTS_TAC `\x:1. e:A` THEN BETA_TAC THEN REFL_TAC);;

export_thm one_RECURSION;;

let one_Axiom = prove
 (`!e:A. ?!fn. fn one = e`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM; one_RECURSION] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  ONCE_REWRITE_TAC [one] THEN ASM_REWRITE_TAC[]);;

export_thm one_Axiom;;

(* ------------------------------------------------------------------------- *)
(* Add the type "1" to the inductive type store.                             *)
(* ------------------------------------------------------------------------- *)

inductive_type_store :=
  ("1",(1,one_INDUCT,one_RECURSION))::(!inductive_type_store);;
