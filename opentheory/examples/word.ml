(* ------------------------------------------------------------------------- *)
(* A functor theory of words.                                                *)
(* ------------------------------------------------------------------------- *)

new_constant ("word_width", `:num`);;

logfile "word-def";;

let word_size_def = new_definition
  `word_size = 2 EXP word_width`;;

export_thm word_size_def;;

let word_size_nonzero = prove
  (`~(word_size = 0)`,
   REWRITE_TAC [word_size_def; EXP_EQ_0] THEN
   NUM_REDUCE_TAC);;

export_thm word_size_nonzero;;

(* Start of parametric theory instantiation: modular *)

(* modular-mod *)

let lt_word_size = new_axiom
  `!n. n < word_size ==> n MOD word_size = n`;;

let word_size_lt = new_axiom
  `!n. n MOD word_size < word_size`;;

let mod_mod_word_size = new_axiom
  `!n. n MOD word_size MOD word_size = n MOD word_size`;;

let add_mod_word_size = new_axiom
  `!m n.
     (m MOD word_size + n MOD word_size) MOD word_size =
     (m + n) MOD word_size`;;

let mult_mod_word_size = new_axiom
  `!m n.
     (m MOD word_size * n MOD word_size) MOD word_size =
     (m * n) MOD word_size`;;

(* modular-def *)

new_type ("word",0);;

new_constant ("word_add", `:word -> word -> word`);;
new_constant ("word_mult", `:word -> word -> word`);;
new_constant ("word_neg", `:word -> word`);;
new_constant ("word_sub", `:word -> word -> word`);;
new_constant ("word_le", `:word -> word -> bool`);;
new_constant ("word_lt", `:word -> word -> bool`);;
new_constant ("num_to_word", `:num -> word`);;
new_constant ("word_to_num", `:word -> num`);;

let word_to_num_to_word = new_axiom
  `!x. num_to_word (word_to_num x) = x`;;

let num_to_word_inj = new_axiom
  `!x y.
     x < word_size /\ y < word_size /\ num_to_word x = num_to_word y ==>
     x = y`;;

let num_to_word_to_num = new_axiom
  `!x. word_to_num (num_to_word x) = x MOD word_size`;;

let num_to_word_add = new_axiom
  `!x1 y1.
     num_to_word (x1 + y1) = word_add (num_to_word x1) (num_to_word y1)`;;

let num_to_word_mult = new_axiom
  `!x1 y1.
     num_to_word (x1 * y1) = word_mult (num_to_word x1) (num_to_word y1)`;;

let word_neg_def = new_axiom
  `!x. word_neg x = num_to_word (word_size - word_to_num x)`;;

let word_sub_def = new_axiom
  `!x y. word_sub x y = word_add x (word_neg y)`;;

let word_le_def = new_axiom
  `!x y. word_le x y = word_to_num x <= word_to_num y`;;

let word_lt_def = new_axiom
  `!x y. word_lt x y = ~(word_le y x)`;;

(* modular-thm *)

let word_to_num_inj = new_axiom
  `!x y. word_to_num x = word_to_num y ==> x = y`;;

let num_to_word_eq = new_axiom
  `!x y. num_to_word x = num_to_word y <=> x MOD word_size = y MOD word_size`;;

let word_to_num_bound = new_axiom
  `!x. word_to_num x < word_size`;;

let word_to_num_div_bound = new_axiom
  `!x. word_to_num x DIV word_size = 0`;;

let word_add_to_num = new_axiom
  `!x y.
     word_to_num (word_add x y) =
     (word_to_num x + word_to_num y) MOD word_size`;;

(* End of parametric theory instantiation: modular *)

logfile "word-bits-def";;

let word_shl_def = new_definition
 `!w n. word_shl w n = num_to_word ((2 EXP n) * word_to_num w)`;;

export_thm word_shl_def;;

let word_shr_def = new_definition
 `!w n. word_shr w n = num_to_word (word_to_num w DIV (2 EXP n))`;;

export_thm word_shr_def;;

let word_bit_def = new_definition
 `!w n. word_bit w n = ODD (word_to_num (word_shr w n))`;;

export_thm word_bit_def;;

let word_to_list_def = new_definition
 `!w. word_to_list w = MAP (word_bit w) (interval 0 word_width)`;;

export_thm word_to_list_def;;

let list_to_word_def = new_recursive_definition list_RECURSION
  `(list_to_word [] = num_to_word 0) /\
   (!h t.
      list_to_word (CONS h t) =
      if h then word_add (word_shl (list_to_word t) 1) (num_to_word 1)
      else word_shl (list_to_word t) 1)`;;

export_thm list_to_word_def;;

let is_word_list_def = new_definition
 `!l. is_word_list (l : bool list) <=> LENGTH l = word_width`;;

export_thm is_word_list_def;;

let word_and_def = new_definition
  `!w1 w2.
     word_and w1 w2 =
     list_to_word (zipwith ( /\ ) (word_to_list w1) (word_to_list w2))`;;

export_thm word_and_def;;

let word_or_def = new_definition
  `!w1 w2.
     word_or w1 w2 =
     list_to_word (zipwith ( \/ ) (word_to_list w1) (word_to_list w2))`;;

export_thm word_or_def;;

let word_not_def = new_definition
  `!w. word_not w = list_to_word (MAP (~) (word_to_list w))`;;

export_thm word_not_def;;

logfile "word-bits-thm";;

let is_word_to_list = prove
  (`!w. is_word_list (word_to_list w)`,
   REWRITE_TAC
     [is_word_list_def; word_to_list_def; LENGTH_MAP; length_interval]);;

export_thm is_word_to_list;;

let cond_mod_2 = prove
  (`!n. (if ODD n then 1 else 0) = n MOD 2`,
   GEN_TAC THEN
   MP_TAC (SPEC `n:num` EVEN_OR_ODD) THEN
   STRIP_TAC THENL
   [MP_TAC (SPEC `n:num` EVEN_MOD) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC (SPEC `n:num` NOT_ODD) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]);
    MP_TAC (SPEC `n:num` ODD_MOD) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th])]);;

let word_bit_mod_2 = prove
  (`!w n.
      (if word_bit w n then 1 else 0) =
      (word_to_num w DIV (2 EXP n)) MOD 2`,
   REWRITE_TAC [word_bit_def; word_shr_def; num_to_word_to_num; cond_mod_2] THEN
   REPEAT GEN_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC lt_word_size THEN
   MATCH_MP_TAC LET_TRANS THEN
   EXISTS_TAC `word_to_num w` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC DIV_LE THEN
    REWRITE_TAC [EXP_EQ_0] THEN
    NUM_REDUCE_TAC;
    REWRITE_TAC [word_to_num_bound]]);;

let nil_to_word_to_num = prove
  (`word_to_num (list_to_word []) = 0`,
   REWRITE_TAC [list_to_word_def; num_to_word_to_num] THEN
   MATCH_MP_TAC lt_word_size THEN
   REWRITE_TAC [LT_NZ; word_size_nonzero]);;

export_thm nil_to_word_to_num;;

let cons_to_word_to_num = prove
  (`!h t.
      word_to_num (list_to_word (CONS h t)) =
      (2 * word_to_num (list_to_word t) + (if h then 1 else 0)) MOD word_size`,
   REWRITE_TAC [list_to_word_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `h : bool` BOOL_CASES_AX) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC
      [word_add_to_num; word_shl_def; EXP_1; word_to_num_to_word] THEN
    REWRITE_TAC [num_to_word_to_num; add_mod_word_size];
    ASM_REWRITE_TAC [word_shl_def; EXP_1; word_to_num_to_word; ADD_0] THEN
    REWRITE_TAC [num_to_word_to_num; add_mod_word_size]]);;

export_thm cons_to_word_to_num;;

let word_to_list_to_word = prove
  (`!w. list_to_word (word_to_list w) = w`,
   GEN_TAC THEN
   REWRITE_TAC [word_to_list_def] THEN
   MATCH_MP_TAC word_to_num_inj THEN
   MATCH_MP_TAC (ITAUT`!p q. (p ==> q) /\ p ==> q`) THEN
   EXISTS_TAC
     `!k.
        k <= word_width ==>
        word_to_num
          (list_to_word (MAP (word_bit w) (interval (word_width - k) k))) =
          word_to_num w DIV (2 EXP (word_width - k))` THEN
   CONJ_TAC THENL
   [DISCH_THEN (MP_TAC o SPEC `word_width`) THEN
    REWRITE_TAC [SUB_REFL; LE_REFL; EXP; DIV_1];
    MATCH_MP_TAC num_INDUCTION THEN
    CONJ_TAC THENL
    [REWRITE_TAC
       [SUB; interval_def; MAP; nil_to_word_to_num; GSYM word_size_def;
        word_to_num_div_bound];
     REPEAT STRIP_TAC THEN
     PAT_ASSUM `X ==> Y` THEN
     MATCH_MP_TAC (ITAUT `X /\ (Y ==> Z) ==> ((X ==> Y) ==> Z)`) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `SUC k` THEN
      ASM_REWRITE_TAC [LE; LE_REFL];
      REWRITE_TAC [interval_def; MAP; cons_to_word_to_num] THEN
      KNOW_TAC `word_width - k = SUC (word_width - SUC k)` THENL
      [ASM_ARITH_TAC;
       DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
       DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
       REWRITE_TAC [word_bit_mod_2] THEN
       ONCE_REWRITE_TAC [MULT_SYM] THEN
       REWRITE_TAC [EXP] THEN
       MP_TAC (SPECL [`word_to_num w`; `2 EXP (word_width - SUC k)`;
                       `2`] (ONCE_REWRITE_RULE [MULT_SYM] DIV_DIV)) THEN
       MATCH_MP_TAC (ITAUT `X /\ (Y ==> Z) ==> ((X ==> Y) ==> Z)`) THEN
       CONJ_TAC THENL
       [REWRITE_TAC [GSYM EXP; EXP_EQ_0] THEN
        NUM_REDUCE_TAC;
        DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
        MP_TAC (SPECL [`word_to_num w DIV (2 EXP (word_width - SUC k))`;
                        `2`] DIVISION) THEN
        MATCH_MP_TAC (ITAUT `X /\ (Y ==> Z) ==> ((X ==> Y) ==> Z)`) THEN
        CONJ_TAC THENL
        [NUM_REDUCE_TAC;
         DISCH_THEN (fun th -> REWRITE_TAC [GSYM (CONJUNCT1 th)]) THEN
         MATCH_MP_TAC lt_word_size THEN
         MATCH_MP_TAC LET_TRANS THEN
         EXISTS_TAC `word_to_num w` THEN
         CONJ_TAC THENL
         [MATCH_MP_TAC DIV_LE THEN
          REWRITE_TAC [EXP_EQ_0] THEN
          NUM_REDUCE_TAC;
          REWRITE_TAC [word_to_num_bound]]]]]]]]);;

export_thm word_to_list_to_word;;

(***
let list_to_word_to_list = prove
  (`!l.
      word_to_list (list_to_word l) =
      if LENGTH l <= word_width then
        APPEND l (REPLICATE (word_width - LENGTH l) F)
      else
        take word_width l`

let list_to_word_to_list = prove
  (`!l. LENGTH l = word_width <=> word_to_list (list_to_word l) = l`,
   GEN_TAC THEN
   EQ_TAC THENL
   [

let num_to_word_list = prove
  (`(num_to_word 0 = list_to_word []) /\
    (!n. num_to_word n = list_to_word []) /\

word_and (list_to_word []) l2 = list_to_word []) /\
    (!l1. word_and l1 (list_to_word []) = list_to_word []) /\
    (!h1 t1 h2 t2.

let word_and_list = prove
  (`(!l2. word_and (list_to_word []) l2 = list_to_word []) /\
    (!l1. word_and l1 (list_to_word []) = list_to_word []) /\
    (!h1 t1 h2 t2.
       word_and (list_to_word (CONS h1 t1)) (list_to_word (CONS h2 t2)) =
       list_to_word (CONS (h1 /\ h2) (word_to_list (word_and (list_to_word t1) (CONS h1 t1)) (list_to_word (CONS h2 t2)) =
!w1 w2.
     word_and w1 w2 =
     list_to_word (zipwith ( /\ ) (word_to_list w1) (word_to_list w2))`;;
***)

logfile_end ();;
