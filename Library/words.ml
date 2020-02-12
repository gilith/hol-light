(* ========================================================================= *)
(*          Theory of machine words using finite indexing types.             *)
(*                                                                           *)
(* Introduces a type `:N word` of N-bit words (N being a type of size N).    *)
(* Note that this builds in a priori the assumption the wordsize is nonzero. *)
(* Some abbreviations like `:byte` = `8 word` are often used for brevity.    *)
(*                                                                           *)
(* Mappings `val:N word->num` and `word:num->N word` for unsigned values,    *)
(* and similar 2s-complement `ival:N word->int` and `iword:int->word`, cast  *)
(* (reducing modulo word in one direction) between words and numbers.        *)
(* The `bit` function gives a specific bit as a Boolean.                     *)
(*                                                                           *)
(* The usual operations are provided like `word_add`, `word_xor`; currently  *)
(* for explicitness we don't overload the usual operators. Some have signed  *)
(* and unsigned variants (e.g. `word_ushr` is unsigned/logical shift right,  *)
(* while `word_ishr` is signed/arithmetical shift right).                    *)
(*                                                                           *)
(* For some cases where the result is debatable or machine-dependent, we     *)
(* have versions that match the JVM tagged with a "j" (e.g. `word_jshr`      *)
(* truncates shift counts modulo word size).                                 *)
(*                                                                           *)
(* There are conversions like WORD_REDUCE_CONV for reducing via proof        *)
(* expressions built up from concrete words like `word 255:byte`.            *)
(*                                                                           *)
(* Some simple decision procedures for proving basic equalities are here too *)
(* and have limited and somewhat complementary scopes:                       *)
(*  - WORD_RULE for simple algebraic properties                              *)
(*  - WORD_BITWISE_RULE for bitwise-type properties of logical operations    *)
(*  - WORD_ARITH for things involving numerical values                       *)
(* ========================================================================= *)

let HAS_SIZE_8 = HAS_SIZE_DIMINDEX_RULE `:8`;;
let HAS_SIZE_16 = HAS_SIZE_DIMINDEX_RULE `:16`;;
let HAS_SIZE_32 = HAS_SIZE_DIMINDEX_RULE `:32`;;
let HAS_SIZE_64 = HAS_SIZE_DIMINDEX_RULE `:64`;;
let HAS_SIZE_128 = HAS_SIZE_DIMINDEX_RULE `:128`;;
let HAS_SIZE_256 = HAS_SIZE_DIMINDEX_RULE `:256`;;
let HAS_SIZE_512 = HAS_SIZE_DIMINDEX_RULE `:512`;;

let DIMINDEX_8 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_8;;
let DIMINDEX_16 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_16;;
let DIMINDEX_32 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_32;;
let DIMINDEX_64 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_64;;
let DIMINDEX_128 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_128;;
let DIMINDEX_256 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_256;;
let DIMINDEX_512 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_512;;

(* ------------------------------------------------------------------------- *)
(* Pre-cache some sizes to speed up computation (only affects efficiency).   *)
(* ------------------------------------------------------------------------- *)

let word_sizes = ref ([]:thm list);;
let word_pow2sizes = ref ([]:thm list);;

let word_SIZE_CONV = ref NO_CONV;;
let word_POW2SIZE_CONV = ref NO_CONV;;

let add_word_sizes =
  let ptm = `(EXP) 2` in
  let sumconv = GEN_REWRITE_CONV I [DIMINDEX_FINITE_SUM] in
  let rec conv tm =
    ((sumconv THENC BINOP_CONV conv THENC NUM_ADD_CONV) ORELSEC
     DIMINDEX_CONV) tm in
  let conv2 tm =
    match tm with
      Comb(t,d) when t = ptm -> (RAND_CONV conv THENC NUM_EXP_CONV) tm
    | _ -> failwith "conv2" in
  let _ = (word_SIZE_CONV := conv; word_POW2SIZE_CONV := conv2) in
  fun l -> let m = !word_sizes
           and m2 = !word_pow2sizes
           and l2 = map (CONV_RULE(RAND_CONV NUM_EXP_CONV) o AP_TERM ptm) l in
           if subset l m then () else
           (word_sizes := union l m;
            word_pow2sizes := union l2 m2;
            word_SIZE_CONV :=
             (GEN_REWRITE_CONV I (!word_sizes) ORELSEC conv);
            word_POW2SIZE_CONV :=
             (GEN_REWRITE_CONV I (!word_pow2sizes) ORELSEC conv2));;

add_word_sizes [DIMINDEX_1; DIMINDEX_2; DIMINDEX_3; DIMINDEX_4];;

add_word_sizes [DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64];;

add_word_sizes [DIMINDEX_128; DIMINDEX_256; DIMINDEX_512];;

(* ------------------------------------------------------------------------- *)
(* Pushing and pulling to combine nested MOD or rem terms.                   *)
(* ------------------------------------------------------------------------- *)

let MOD_DOWN_CONV =
  let MOD_SUC_MOD = METIS[ADD1; MOD_ADD_MOD; MOD_MOD_REFL]
   `(SUC(m MOD n)) MOD n = SUC m MOD n` in
  let addmul_conv = GEN_REWRITE_CONV I
    [GSYM MOD_SUC_MOD; GSYM MOD_ADD_MOD; GSYM MOD_MULT_MOD2; GSYM MOD_EXP_MOD]
  and mod_conv = GEN_REWRITE_CONV I [MOD_MOD_REFL] in
  let rec downconv tm =
   ((addmul_conv THENC LAND_CONV downconv) ORELSEC
    (mod_conv THENC downconv) ORELSEC
    SUB_CONV downconv) tm
  and upconv =
    GEN_REWRITE_CONV DEPTH_CONV
     [MOD_SUC_MOD; MOD_ADD_MOD; MOD_MULT_MOD2; MOD_EXP_MOD; MOD_MOD_REFL] in
  downconv THENC upconv;;

let INT_REM_DOWN_CONV =
  let addmul_conv = GEN_REWRITE_CONV I
    [GSYM INT_NEG_REM; GSYM INT_ADD_REM; GSYM INT_SUB_REM;
     GSYM INT_MUL_REM; GSYM INT_POW_REM]
  and mod_conv = GEN_REWRITE_CONV I [INT_REM_REM] in
  let rec downconv tm =
   ((addmul_conv THENC LAND_CONV downconv) ORELSEC
    (mod_conv THENC downconv) ORELSEC
    SUB_CONV downconv) tm
  and upconv =
    GEN_REWRITE_CONV DEPTH_CONV
     [INT_NEG_REM; INT_ADD_REM; INT_SUB_REM; INT_MUL_REM;
      INT_POW_REM; INT_REM_REM] in
  downconv THENC upconv;;

(* ------------------------------------------------------------------------- *)
(* Some generic lemmas about digit sums.                                     *)
(* ------------------------------------------------------------------------- *)

let DIGITSUM_WORKS_GEN = prove
 (`!B n k.
    nsum {i | i < k} (\i. B EXP i * n DIV (B EXP i) MOD B) = n MOD (B EXP k)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  SIMP_TAC[NUMSEG_CLAUSES_LT; NSUM_CLAUSES; MOD_1; EXP; FINITE_NUMSEG_LT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; LT_REFL] THEN
  MESON_TAC[MOD_MULT_MOD; MULT_SYM]);;

let DIGITSUM_WORKS = prove
 (`!B n k.
        n < B EXP k
        ==> nsum {i | i < k} (\i. B EXP i * n DIV (B EXP i) MOD B) = n`,
  SIMP_TAC[DIGITSUM_WORKS_GEN; MOD_LT]);;

let DIGITSUM_BOUND = prove
 (`!B b k. (!i. i < k ==> b i < B)
           ==> nsum {i | i < k} (\i. B EXP i * b i) < B EXP k`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; ARITH] THEN
  REWRITE_TAC[LT] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ARITH_RULE
   `s < e /\ e * (x + 1) <= e * b ==> s + e * x < b * e`) THEN
  ASM_SIMP_TAC[LE_MULT_LCANCEL; ARITH_RULE `b + 1 <= c <=> b < c`]);;

let DIGITSUM_SPLIT = prove
 (`!B b s n.
        FINITE s
        ==> B EXP n * nsum {i | i IN s /\ n <= i} (\i. B EXP (i - n) * b i) +
            nsum {i | i IN s /\ i < n} (\i. B EXP i * b i) =
            nsum s (\i. B EXP i * b i)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM NSUM_LMUL; MULT_ASSOC; GSYM EXP_ADD] THEN
  SIMP_TAC[ARITH_RULE `n:num <= i ==> n + i - n = i`] THEN
  MATCH_MP_TAC NSUM_UNION_EQ THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  SET_TAC[]);;

let DIGITSUM_DIV,DIGITSUM_MOD = (CONJ_PAIR o prove)
 (`(!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) DIV (B EXP n) =
            nsum {i | i IN s /\ n <= i} (\i. B EXP (i - n) * b i)) /\
   (!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) MOD (B EXP n) =
            nsum {i | i IN s /\ i < n} (\i. B EXP i * b i))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `B = 0` THENL
   [ASM_REWRITE_TAC[CONJUNCT1 LT; SET_RULE `(!x. ~(x IN s)) <=> s = {}`] THEN
    SIMP_TAC[EMPTY_GSPEC; NOT_IN_EMPTY; CONJUNCT1 NSUM_CLAUSES] THEN
    REWRITE_TAC[DIV_0; MOD_0];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [MULT_SYM] THEN
    MATCH_MP_TAC(GSYM DIGITSUM_SPLIT) THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[SET_RULE
     `{x | x IN s /\ P x} = {x | x IN {y | P y} /\ x IN s}`] THEN
    REWRITE_TAC[NSUM_RESTRICT_SET; MESON[MULT_CLAUSES]
     `(if p then a * b else 0) = a * (if p then b else 0)`] THEN
    MATCH_MP_TAC DIGITSUM_BOUND THEN ASM_MESON_TAC[LE_1]]);;

let DIGITSUM_MOD_NUMSEG = prove
 (`!B b m n.
        (!i. i < m ==> b i < B)
        ==> nsum {i | i < m} (\i. B EXP i * b i) MOD (B EXP n) =
            nsum {i | i < MIN m n} (\i. B EXP i * b i)`,
  SIMP_TAC[DIGITSUM_MOD; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  REWRITE_TAC[ARITH_RULE `i < MIN m n <=> i < m /\ i < n`]);;

let DIGITSUM_DIV_NUMSEG = prove
 (`!B b m n.
        (!i. i < m ==> b i < B)
        ==> nsum {i | i < m} (\i. B EXP i * b i) DIV (B EXP n) =
            nsum {i | i < m - n} (\i. B EXP i * b(i + n))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIGITSUM_DIV; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `{i:num | i < m /\ n <= i} = IMAGE (\i. i + n) {i | i < m - n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; ARITH_RULE
     `x:num = y + n <=> y = x - n /\ n <= x`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2] THEN ARITH_TAC;
    SIMP_TAC[NSUM_IMAGE; EQ_ADD_RCANCEL; o_DEF; ADD_SUB]]);;

let DIGITSUM_DIV_MOD = prove
 (`!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) DIV (B EXP n) MOD B =
            if n IN s then b n else 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_MOD] THEN
  REWRITE_TAC[MESON[EXP; MULT_SYM] `B EXP n * B = B EXP SUC n`] THEN
  ASM_SIMP_TAC[DIGITSUM_MOD] THEN
  ASM_SIMP_TAC[DIGITSUM_DIV; FINITE_RESTRICT; IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; ARITH_RULE `i < SUC n /\ n <= i <=> i = n`] THEN
  REWRITE_TAC[MESON[] `i IN s /\ i = n <=> n IN s /\ i = n`] THEN
  ASM_CASES_TAC `(n:num) IN s` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; NSUM_CLAUSES] THEN
  REWRITE_TAC[SING_GSPEC; NSUM_SING; SUB_REFL; MULT_CLAUSES; EXP]);;

(* ------------------------------------------------------------------------- *)
(* Mapping a Boolean to the natural number 1 (true) or 0 (false)             *)
(* ------------------------------------------------------------------------- *)

let bitval = new_definition
 `bitval b = if b then 1 else 0`;;

let BITVAL_CLAUSES = prove
 (`bitval F = 0 /\ bitval T = 1`,
  REWRITE_TAC[bitval]);;

let BITVAL_BOUND = prove
 (`!b. bitval b <= 1`,
  REWRITE_TAC[bitval] THEN ARITH_TAC);;

let BITVAL_BOUND_ALT = prove
 (`!b. bitval b < 2`,
  REWRITE_TAC[bitval] THEN ARITH_TAC);;

let ODD_BITVAL = prove
 (`!b. ODD(bitval b) <=> b`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES; ARITH]);;

let EVEN_BITVAL = prove
 (`!b. EVEN(bitval b) <=> ~b`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES; ARITH]);;

let NUM_AS_BITVAL = prove
 (`!n. n <= 1 <=> ?b. n = bitval b`,
  REWRITE_TAC[EXISTS_BOOL_THM; BITVAL_CLAUSES] THEN ARITH_TAC);;

let NUM_AS_BITVAL_ALT = prove
 (`!n. n < 2 <=> ?b. n = bitval b`,
  REWRITE_TAC[EXISTS_BOOL_THM; BITVAL_CLAUSES] THEN ARITH_TAC);;

let BITVAL_EQ_0 = prove
 (`!b. bitval b = 0 <=> ~b`,
  GEN_TAC THEN REWRITE_TAC[bitval] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_EQ_1 = prove
 (`!b. bitval b = 1 <=> b`,
  GEN_TAC THEN REWRITE_TAC[bitval] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_NOT = prove
 (`!b. bitval(~b) = 1 - bitval b`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_AND = prove
 (`!b c. bitval(b /\ c) = bitval b * bitval c`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_OR = prove
 (`!b c. bitval(b \/ c) = (bitval b + bitval c) - bitval b * bitval c`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_IFF = prove
 (`!b c. bitval(b <=> c) =
         (1 + 2 * bitval b * bitval c) - (bitval b + bitval c)`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_XOR = prove
 (`!b c. bitval(~(b <=> c)) = (bitval b + bitval c) - 2 * bitval b * bitval c`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let INT_BITVAL_NOT = prove
 (`!b. &(bitval(~b)):int = &1 - &(bitval b)`,
  SIMP_TAC[BITVAL_NOT; GSYM INT_OF_NUM_SUB; BITVAL_BOUND]);;

let BITVAL_ODD = prove
 (`!n. bitval(ODD n) = n MOD 2`,
  REWRITE_TAC[bitval; GSYM NOT_EVEN; MOD_2_CASES; COND_SWAP]);;

(* ------------------------------------------------------------------------- *)
(* Some more binary-specific lemmas.                                         *)
(* ------------------------------------------------------------------------- *)

let ODD_MOD_POW2 = prove
 (`!n k. ODD(n MOD 2 EXP k) <=> ~(k = 0) /\ ODD n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[MOD_1; EXP; ODD] THEN
  REWRITE_TAC[MESON[ODD_MOD; EXP_1] `ODD n <=> n MOD (2 EXP 1) = 1`] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> MIN k 1 = 1`]);;

let BINARY_DIGITSUM_BOUND = prove
 (`!b k. nsum {i | i < k} (\i. 2 EXP i * bitval(b i)) < 2 EXP k`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC DIGITSUM_BOUND THEN
  REWRITE_TAC[BITVAL_BOUND_ALT]);;

let BINARY_DIGITSUM_SPLIT = prove
 (`!b s n.
        FINITE s
        ==> 2 EXP n *
            nsum {i | i IN s /\ n <= i} (\i. 2 EXP (i - n) * bitval(b i)) +
            nsum {i | i IN s /\ i < n} (\i. 2 EXP i * bitval(b i)) =
            nsum s (\i. 2 EXP i * bitval(b i))`,
  MATCH_ACCEPT_TAC DIGITSUM_SPLIT);;

let BINARY_DIGITSUM_DIV = prove
 (`!b s n.
        FINITE s
        ==> nsum s (\i. 2 EXP i * bitval(b i)) DIV (2 EXP n) =
            nsum {i | i IN s /\ n <= i} (\i. 2 EXP (i - n) * bitval(b i))`,
  SIMP_TAC[DIGITSUM_DIV; BITVAL_BOUND_ALT]);;

let BINARY_DIGITSUM_MOD = prove
 (`!b s n.
        FINITE s
        ==> nsum s (\i. 2 EXP i * bitval(b i)) MOD (2 EXP n) =
            nsum {i | i IN s /\ i < n} (\i. 2 EXP i * bitval(b i))`,
  SIMP_TAC[DIGITSUM_MOD; BITVAL_BOUND_ALT]);;

(* ------------------------------------------------------------------------- *)
(* The type "N word" is in bijection with "bool^N"                           *)
(* ------------------------------------------------------------------------- *)

let word_tybij =
  let th = prove (`?x:bool^N. T`,REWRITE_TAC[]) in
  REWRITE_RULE[]
   (new_type_definition "word" ("mk_word","bitvector") th);;

let WORD_EQ_BITVECTOR = prove
 (`!v w:N word. v = w <=> bitvector v = bitvector w`,
  MESON_TAC[word_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Set up some specific sizes that we want.                                  *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("nybble",`:(4)word`);;
new_type_abbrev("byte",`:(8)word`);;
new_type_abbrev("int16",`:(16)word`);;
new_type_abbrev("int32",`:(32)word`);;
new_type_abbrev("int64",`:(64)word`);;
new_type_abbrev("int128",`:(128)word`);;

(* ------------------------------------------------------------------------- *)
(* Individual selection of bits, indexing from 0 as usual.                   *)
(* ------------------------------------------------------------------------- *)

let bit = new_definition
 `bit i (w:N word) =
    if i < dimindex(:N) then (bitvector w)$(i + 1)
    else F`;;

let WORD_EQ_BITS_ALT = prove
 (`!v w:N word. v = w <=> !i. i < dimindex(:N) ==> bit i v = bit i w`,
  REPEAT GEN_TAC THEN SIMP_TAC[WORD_EQ_BITVECTOR; bit; CART_EQ] THEN
  MESON_TAC[ARITH_RULE `i < n ==> 1 <= i + 1 /\ i + 1 <= n`;
            ARITH_RULE `1 <= i /\ i <= n ==> i = (i - 1) + 1 /\ i - 1 < n`]);;

let WORD_EQ_BITS = prove
 (`!v w:N word. v = w <=> !i. bit i v = bit i w`,
  MESON_TAC[bit; WORD_EQ_BITS_ALT]);;

let BIT_TRIVIAL = prove
 (`!w:(N)word i. dimindex(:N) <= i ==> (bit i w <=> F)`,
  SIMP_TAC[GSYM NOT_LT; bit]);;

(* ------------------------------------------------------------------------- *)
(* Mappings to and from sets of bits.                                        *)
(* ------------------------------------------------------------------------- *)

let bits_of_word = new_definition
 `bits_of_word (w:N word) = {i | bit i w}`;;

let word_of_bits = new_definition
 `word_of_bits s:N word = mk_word(lambda i. (i - 1) IN s)`;;

let IN_BITS_OF_WORD = prove
 (`!(w:N word) i. i IN bits_of_word w <=> bit i w`,
  REWRITE_TAC[bits_of_word; IN_ELIM_THM]);;

let BIT_WORD_OF_BITS = prove
 (`!s i. bit i (word_of_bits s:N word) <=> i < dimindex(:N) /\ i IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit; word_of_bits] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[word_tybij] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
   `i < n ==> 1 <= i + 1 /\ i + 1 <= n`)) THEN
  ASM_SIMP_TAC[LAMBDA_BETA; ADD_SUB]);;

let WORD_OF_BITS_EQ = prove
 (`!s t. word_of_bits s:N word = word_of_bits t <=>
         !i. i < dimindex(:N) ==> (i IN s <=> i IN t)`,
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS] THEN MESON_TAC[]);;

let WORD_OF_BITS_OF_WORD = prove
 (`!w:N word. word_of_bits(bits_of_word w) = w`,
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; bits_of_word; IN_ELIM_THM]);;

let BITS_OF_WORD_OF_BITS = prove
 (`!s. bits_of_word(word_of_bits s:N word) = s INTER {i | i < dimindex(:N)}`,
  GEN_TAC THEN REWRITE_TAC[bits_of_word] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; BIT_WORD_OF_BITS] THEN
  CONV_TAC TAUT);;

let BITS_OF_WORD_EQ = prove
 (`!v w:N word. bits_of_word v = bits_of_word w <=> v = w`,
  MESON_TAC[WORD_OF_BITS_OF_WORD]);;

let WORD_OF_BITS = prove
 (`!w:N word. w = word_of_bits {i | bit i w}`,
  REWRITE_TAC[GSYM bits_of_word; WORD_OF_BITS_OF_WORD]);;

let WORD_OF_BITS_ALT = prove
 (`!w:N word. w = word_of_bits {i | i < dimindex(:N) /\ bit i w}`,
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let FINITE_BITS_OF_WORD = prove
 (`!w:N word. FINITE(bits_of_word w)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i | i < dimindex(:N)}` THEN
  REWRITE_TAC[bits_of_word; FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

(* ------------------------------------------------------------------------- *)
(* Mapping to and from natural number values (treating as unsigned word).    *)
(* ------------------------------------------------------------------------- *)

let val_def = new_definition
 `val (w:N word) =
    nsum {i | i < dimindex(:N)} (\i. 2 EXP i * bitval(bit i w))`;;

let word = new_definition
 `(word:num->N word) n =
    mk_word(lambda i. ODD(n DIV (2 EXP (i - 1))))`;;

let BIT_WORD = prove
 (`!i n. bit i (word n:N word) <=> i < dimindex(:N) /\ ODD(n DIV (2 EXP i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[word; word_tybij] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; ADD_SUB; ARITH_RULE `1 <= i + 1`;
               ARITH_RULE `i < n ==> i + 1 <= n`]);;

let BIT_WORD_0 = prove
 (`!i. bit i (word 0:N word) <=> F`,
  REWRITE_TAC[BIT_WORD; DIV_0; ODD]);;

let BITS_OF_WORD_0 = prove
 (`bits_of_word(word 0:N word) = {}`,
  REWRITE_TAC[bits_of_word; BIT_WORD_0; EMPTY_GSPEC]);;

let BITS_OF_WORD_EQ_EMPTY = prove
 (`!w:N word. bits_of_word w = {} <=> w = word 0`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_0]);;

let BITVAL_BIT_WORD = prove
 (`!i n. bitval(bit i (word n:N word)) =
         if i < dimindex(:N) then (n DIV (2 EXP i)) MOD 2 else 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[BIT_WORD; bitval; ODD_MOD] THEN
  ARITH_TAC);;

let WORD_VAL = prove
 (`!w:N word. word(val w) = w`,
  GEN_TAC THEN SIMP_TAC[WORD_EQ_BITS_ALT; val_def; BIT_WORD] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SIMP_TAC[BINARY_DIGITSUM_DIV; FINITE_NUMSEG_LT] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; GSYM numseg; ARITH_RULE
   `k < n ==> (i < n /\ k <= i <=> k <= i /\ i <= n - 1)`] THEN
  ASM_SIMP_TAC[NSUM_CLAUSES_LEFT; ARITH_RULE `k < n ==> k <= n - 1`] THEN
  MATCH_MP_TAC(MESON[ODD; ODD_ADD]
   `~ODD n /\ (ODD m <=> p) ==> (ODD(m + n) <=> p)`) THEN
  REWRITE_TAC[SUB_REFL; EXP; NOT_ODD; MULT_CLAUSES] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_CLOSED THEN
    SIMP_TAC[EVEN; EVEN_ADD; EVEN_MULT; EVEN_EXP; IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let VAL_WORD = prove
 (`!n. val(word n:N word) = n MOD (2 EXP (dimindex(:N)))`,
  GEN_TAC THEN SIMP_TAC[val_def; BITVAL_BIT_WORD] THEN
  SPEC_TAC(`dimindex(:N)`,`k:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; MOD_1] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_MOD] THEN ARITH_TAC);;

let FORALL_WORD = prove
 (`!P. (!x:N word. P x) <=> (!n. P(word n))`,
  MESON_TAC[WORD_VAL]);;

let EXISTS_WORD = prove
 (`!P. (?x:N word. P x) <=> (?n. P(word n))`,
  MESON_TAC[WORD_VAL]);;

let VAL_WORD_0 = prove
 (`val(word 0:(N)word) = 0`,
  SIMP_TAC[VAL_WORD; MOD_0; EXP_EQ_0; ARITH_EQ]);;

let VAL_WORD_1 = prove
 (`val(word 1:(N)word) = 1`,
  REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `1 = 2 EXP 0`] THEN
  SIMP_TAC[LT_EXP; LE_1; DIMINDEX_GE_1] THEN ARITH_TAC);;

let WORD_BITVAL = prove
 (`!b. word(bitval b) = if b then word 1 else word 0`,
  REWRITE_TAC[bitval] THEN MESON_TAC[]);;

let VAL_WORD_BITVAL = prove
 (`!b. val(word(bitval b)) = bitval b`,
  MATCH_MP_TAC bool_INDUCT THEN
  REWRITE_TAC[VAL_WORD_1; VAL_WORD_0; BITVAL_CLAUSES]);;

let VAL_WORD_EQ = prove
 (`!n. n < 2 EXP dimindex(:N) ==> val(word n :(N)word) = n`,
  SIMP_TAC[VAL_WORD; MOD_LT]);;

let VAL_EQ = prove
 (`!(v:N word) (w:N word). val v = val w <=> v = w`,
  MESON_TAC[WORD_VAL]);;

let VAL_EQ_0 = prove
 (`!w:(N)word. val w = 0 <=> w = word 0`,
  MESON_TAC[VAL_WORD_0; VAL_EQ]);;

let VAL_EQ_1 = prove
 (`!w:(N)word. val w = 1 <=> w = word 1`,
  MESON_TAC[VAL_WORD_1; VAL_EQ]);;

let VAL_EQ_BITVAL = prove
 (`!w:(N)word b. val w = bitval b <=> w = word(bitval b)`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES; VAL_EQ_0; VAL_EQ_1]);;

let WORD_BITVAL_EQ_0 = prove
 (`!b. word(bitval b):N word = word 0 <=> ~b`,
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_BITVAL; BITVAL_EQ_0]);;

let WORD_BITVAL_EQ_1 = prove
 (`!b. word(bitval b):N word = word 1 <=> b`,
  REWRITE_TAC[GSYM VAL_EQ_1; VAL_WORD_BITVAL; BITVAL_EQ_1]);;

let WORD_NE_10 = prove
 (`~(word 1:N word = word 0)`,
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_1] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_EQ = prove
 (`!x y. word x:(N)word = word y <=> (x == y) (mod (2 EXP dimindex(:N)))`,
  MESON_TAC[VAL_WORD; WORD_VAL; CONG]);;

let VAL_BOUND = prove
 (`!w:N word. val w < 2 EXP dimindex(:N)`,
  REWRITE_TAC[val_def; BINARY_DIGITSUM_BOUND]);;

let INT_VAL_BOUND = prove
 (`!w:N word. &(val w):int < &2 pow dimindex(:N)`,
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT; VAL_BOUND]);;

let VAL_MOD_REFL = prove
 (`!x:(N)word. (val x) MOD (2 EXP dimindex(:N)) = val x`,
  MESON_TAC[MOD_LT; VAL_BOUND]);;

let VAL_WORD_EQ_EQ = prove
 (`!n. val(word n:N word) = n <=> n < 2 EXP dimindex(:N)`,
  MESON_TAC[VAL_WORD_EQ; VAL_BOUND]);;

let FORALL_VAL_GEN = prove
 (`!P. (!x:N word. P (val x) x) <=>
       !n. n < 2 EXP dimindex(:N) ==> P n (word n)`,
  MESON_TAC[VAL_WORD_EQ; WORD_VAL; VAL_BOUND]);;

let FORALL_VAL = prove
 (`!P. (!x:N word. P(val x)) <=> (!n. n < 2 EXP dimindex(:N) ==> P n)`,
  REWRITE_TAC[FORALL_VAL_GEN]);;

let VAL_CONG = prove
 (`!(v:N word) (w:N word).
        (val v == val w) (mod (2 EXP dimindex(:N))) <=> v = w`,
  REWRITE_TAC[GSYM VAL_EQ; CONG; MOD_MOD_REFL; VAL_MOD_REFL]);;

let WORD_MOD_SIZE = prove
 (`!n. word(n MOD (2 EXP dimindex(:N))):N word = word n`,
  REWRITE_TAC[WORD_EQ; CONG; MOD_MOD_REFL]);;

let VAL_WORD_CONG = prove
 (`!x. (val(word x:N word) == x) (mod (2 EXP (dimindex(:N))))`,
  REWRITE_TAC[VAL_WORD; CONG; MOD_MOD_REFL]);;

let VAL_WORD_GALOIS = prove
 (`!(w:N word) n. val w = n <=> n < 2 EXP dimindex(:N) /\ w = word n`,
  MESON_TAC[WORD_VAL; VAL_WORD_EQ; VAL_BOUND]);;

let WORD_VAL_GALOIS = prove
 (`!(w:N word) n. word n = w <=> n MOD 2 EXP dimindex(:N) = val w`,
  MESON_TAC[VAL_WORD; WORD_MOD_SIZE; WORD_VAL]);;

let BIT_VAL = prove
 (`!(x:N word) i. bit i x <=> ODD(val x DIV (2 EXP i))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[BIT_WORD; TAUT `(p /\ q <=> q) <=> (~p ==> ~q)`] THEN
  REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
  ASM_SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
  ASM_REWRITE_TAC[VAL_BOUND; LE_EXP; DIMINDEX_NONZERO; COND_ID]);;

let BIT_VAL_MOD = prove
 (`!(x:N word) k.
        bit k x <=> 2 EXP k <= val(x) MOD 2 EXP (k + 1)`,
  REWRITE_TAC[BIT_VAL; GSYM NOT_EVEN; EVEN_MOD; EXP_ADD; EXP_1; DIV_MOD] THEN
  SIMP_TAC[DIV_EQ_0; NOT_LT; EXP_EQ_0; ARITH_EQ]);;

let BIT_LSB = prove
 (`!x:N word. bit 0 x <=> ODD(val x)`,
  REWRITE_TAC[BIT_VAL; EXP; DIV_1]);;

let TWICE_MSB = prove
 (`2 EXP dimindex(:N) = 2 * 2 EXP (dimindex(:N) - 1) /\
   (&2:int) pow dimindex(:N) = &2 * &2 pow (dimindex(:N) - 1)`,
  REWRITE_TAC[GSYM(CONJUNCT2 EXP); GSYM(CONJUNCT2 INT_POW)] THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> SUC(n - 1) = n`]);;

let MSB_VAL = prove
 (`!w:N word. bit (dimindex(:N) - 1) w <=> 2 EXP (dimindex(:N) - 1) <= val w`,
  SIMP_TAC[BIT_VAL_MOD; SUB_ADD; DIMINDEX_GE_1; VAL_MOD_REFL]);;

let MSB_INT_VAL = prove
 (`!w:N word.
    bit (dimindex(:N) - 1) w <=> (&2 pow (dimindex(:N) - 1)):int <= &(val w)`,
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LE; MSB_VAL]);;

let VAL_WORD_OF_BITS = prove
 (`!s. val(word_of_bits s:N word) =
       nsum {i | i < dimindex(:N) /\ i IN s} (\i. 2 EXP i)`,
  GEN_TAC THEN SIMP_TAC[val_def; BIT_WORD_OF_BITS; bitval] THEN
  REWRITE_TAC[COND_RAND; MULT_CLAUSES; GSYM NSUM_RESTRICT_SET] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let WORD_OF_BITS_AS_WORD = prove
 (`!s. word_of_bits s:N word =
       word(nsum {i | i < dimindex(:N) /\ i IN s} (\i. 2 EXP i))`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_OF_BITS; VAL_WORD] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[GSYM VAL_WORD_OF_BITS; VAL_BOUND]);;

let WORD_OF_BITS_AS_WORD_FINITE = prove
 (`!s. FINITE s ==> word_of_bits s:N word = word(nsum s (\i. 2 EXP i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ; WORD_OF_BITS_AS_WORD] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[NSUM_RESTRICT_SET] THEN
  MATCH_MP_TAC CONG_NSUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[NUMBER_RULE `(n:num == n) (mod p)`] THEN
  REWRITE_TAC[NUMBER_RULE `(0 == n) (mod p) <=> p divides n`] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
  SIMP_TAC[LE_EXISTS; EXP_ADD; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUMBER_RULE);;

let WORD_OF_BITS_SING_AS_WORD = prove
 (`!s i. word_of_bits {i}:N word = word(2 EXP i)`,
  SIMP_TAC[WORD_OF_BITS_AS_WORD_FINITE; FINITE_SING; NSUM_SING]);;

let VAL_WORD_OF_BITS_SING = prove
 (`!i. val(word_of_bits {i}:N word) = if i < dimindex(:N) then 2 EXP i else 0`,
  GEN_TAC THEN SIMP_TAC[val_def; BIT_WORD_OF_BITS; IN_SING; bitval] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
  SIMP_TAC[MULT_CLAUSES; NSUM_DELTA; IN_ELIM_THM]);;

let WORD_OF_BITS_MASK = prove
 (`!n. word_of_bits {i | i < n}:N word = word(2 EXP n - 1)`,
  GEN_TAC THEN SIMP_TAC[WORD_OF_BITS_AS_WORD_FINITE; FINITE_NUMSEG_LT] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(ARITH_RULE `n + 1 = m ==> n = m - 1`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP] THEN
  ASM_ARITH_TAC);;

let BIT_WORD_POW2 = prove
 (`!k i. bit i (word (2 EXP k):N word) <=> i = k /\ k < dimindex(:N)`,
  REWRITE_TAC[GSYM WORD_OF_BITS_SING_AS_WORD; BIT_WORD_OF_BITS] THEN
  SET_TAC[]);;

let BIT_WORD_1 = prove
 (`!i. bit i (word 1:N word) <=> i = 0`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `1 = 2 EXP 0`] THEN
  SIMP_TAC[BIT_WORD_POW2; LE_1; DIMINDEX_GE_1]);;

let WORD_OF_BITS_SING_AS_WORD_1 = prove
 (`!s i. word_of_bits {0}:N word = word 1`,
  REWRITE_TAC[WORD_OF_BITS_SING_AS_WORD; EXP]);;

let BITS_OF_WORD_1 = prove
 (`bits_of_word (word 1:N word) = {0}`,
  REWRITE_TAC[bits_of_word; BIT_WORD_1] THEN SET_TAC[]);;

let BIT_WORD_OF_BITS_SING = prove
 (`!k i. bit i (word_of_bits {k}:N word) <=> k < dimindex(:N) /\ i = k`,
  REWRITE_TAC[BIT_WORD_OF_BITS; IN_SING] THEN MESON_TAC[]);;

let VAL_MOD = prove
 (`!(x:N word) k.
        val x MOD 2 EXP k = nsum {i | i < k} (\i. 2 EXP i * bitval(bit i x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[val_def] THEN
  SIMP_TAC[BINARY_DIGITSUM_MOD; FINITE_NUMSEG_LT] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; IMP_CONJ; MULT_EQ_0; BITVAL_EQ_0; NOT_LT] THEN
  MESON_TAC[BIT_TRIVIAL]);;

let VAL_MOD_STEP = prove
 (`!(x:N word) k.
      val x MOD 2 EXP (k + 1) = 2 EXP k * bitval(bit k x) + val x MOD 2 EXP k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_MOD; ARITH_RULE `i < k + 1 <=> i = k \/ i < k`] THEN
  REWRITE_TAC[SET_RULE `{x | x = a \/ P x} = a INSERT {x | P x}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Corresponding signed 2s-complement mappings to and from integers.         *)
(* ------------------------------------------------------------------------- *)

let ival = new_definition
 `(ival:N word->int) w =
    if val(w) < 2 EXP (dimindex(:N) - 1) then &(val w)
    else &(val w) - &2 pow dimindex(:N)`;;

let iword = new_definition
 `(iword:int->N word) x = word(num_of_int(x rem (&2 pow dimindex(:N))))`;;

let word_sgn = new_definition
 `word_sgn (x:N word) = int_sgn(ival x)`;;

let INT_IVAL = prove
 (`!w:N word.
        ival w =
        if &(val w):int < &2 pow (dimindex(:N) - 1) then &(val w)
        else &(val w) - &2 pow dimindex(:N)`,
  REWRITE_TAC[ival; INT_OF_NUM_POW; INT_OF_NUM_LT]);;

let WORD_IWORD = prove
 (`!n. word n:N word = iword(&n)`,
  GEN_TAC THEN REWRITE_TAC[iword; WORD_EQ] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
  REWRITE_TAC[CONG; MOD_MOD_REFL]);;

let IVAL_VAL = prove
 (`!w:N word.
    ival w =
    &(val w) - &2 pow dimindex(:N) * &(bitval(bit (dimindex(:N) - 1) w))`,
  GEN_TAC THEN REWRITE_TAC[ival; GSYM NOT_LE; GSYM MSB_VAL; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[bitval] THEN INT_ARITH_TAC);;

let VAL_IVAL = prove
 (`!w:N word.
    &(val w) =
    ival w + &2 pow dimindex(:N) * &(bitval (bit (dimindex (:N) - 1) w))`,
  REWRITE_TAC[IVAL_VAL] THEN CONV_TAC INT_ARITH);;

let MSB_IVAL = prove
 (`!(w:N word).
        bit (dimindex(:N) - 1) w <=> ival w < &0`,
  GEN_TAC THEN REWRITE_TAC[ival; MSB_VAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  REWRITE_TAC[INT_NOT_LT; INT_OF_NUM_LE; LE_0] THEN
  REWRITE_TAC[INT_ARITH `a - b:int < &0 <=> a < b`] THEN
  REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_POW; VAL_BOUND]);;

let IVAL_BOUND = prove
 (`!w:(N)word.
        --(&2 pow (dimindex(:N) - 1)) <= ival w /\
        ival w < &2 pow (dimindex(:N) - 1)`,
  GEN_TAC THEN MP_TAC(ISPEC `w:N word` VAL_BOUND) THEN
  REWRITE_TAC[ival; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN
  SUBGOAL_THEN `?n. dimindex(:N) = SUC n` (CHOOSE_THEN SUBST1_TAC) THENL
   [MESON_TAC[DIMINDEX_NONZERO; num_CASES]; ALL_TAC] THEN
  REWRITE_TAC[SUC_SUB1; INT_POW] THEN INT_ARITH_TAC);;

let IVAL_WORD_0 = prove
 (`ival(word 0) = &0`,
  REWRITE_TAC[ival; VAL_WORD_0; EXP_LT_0] THEN CONV_TAC NUM_REDUCE_CONV);;

let IVAL_WORD_1 = prove
 (`ival(word 1:N word) = if dimindex(:N) = 1 then -- &1 else &1`,
  REWRITE_TAC[ival; VAL_WORD_1] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 < x <=> 2 EXP 1 <= x`] THEN
  REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIMINDEX_NONZERO; ARITH_RULE
   `1 <= n - 1 <=> ~(n = 0 \/ n = 1)`] THEN
  ASM_CASES_TAC `dimindex(:N) = 1` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV);;

let IVAL_VAL_CONG = prove
 (`!(w:N word). (ival w == &(val w)) (mod (&2 pow (dimindex(:N))))`,
  GEN_TAC THEN REWRITE_TAC[ival] THEN COND_CASES_TAC THEN
  CONV_TAC INTEGER_RULE);;

let IVAL_CONG = prove
 (`!(v:N word) (w:N word).
      (ival v == ival w) (mod (&2 pow (dimindex(:N)))) <=> v = w`,
  REWRITE_TAC[GSYM VAL_CONG; num_congruent; GSYM INT_OF_NUM_POW] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(INTEGER_RULE
   `(x:int == x') (mod n) /\ (y == y') (mod n)
    ==> ((x == y) (mod n) <=> (x' == y') (mod n))`) THEN
  REWRITE_TAC[IVAL_VAL_CONG]);;

let IVAL_EQ = prove
 (`!(v:N word) (w:N word). ival v = ival w <=> v = w`,
  MESON_TAC[NUMBER_RULE `(x:int == x) (mod n)`; IVAL_CONG]);;

let IVAL_EQ_0 = prove
 (`!(v:N word). ival w = &0 <=> w = word 0`,
  REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_0]);;

let IVAL_EQ_1 = prove
 (`!w:N word. ival w = &1 <=> 2 <= dimindex(:N) /\ w = word 1`,
  GEN_TAC THEN REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_1] THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> (2 <= n <=> ~(n = 1))`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `w:N word` IVAL_BOUND) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

let IWORD_EQ = prove
 (`!x y. iword x:N word = iword y <=> (x == y) (mod (&2 pow (dimindex(:N))))`,
  REWRITE_TAC[iword; WORD_EQ; num_congruent; GSYM INT_OF_NUM_POW] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_DIVISION; INT_POW_EQ_0;
           INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]);;

let IWORD_REM_SIZE = prove
 (`!n. iword(n rem (&2 pow dimindex(:N))):N word = iword n`,
  REWRITE_TAC[IWORD_EQ; INT_REM_MOD_SELF]);;

let IVAL_IWORD_CONG = prove
 (`!x. (ival(iword x:N word) == x) (mod (&2 pow (dimindex(:N))))`,
  GEN_TAC THEN MP_TAC(SPEC `iword x:N word` IVAL_VAL_CONG) THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(y:int == z) (mod n) ==> (x == y) (mod n) ==> (x == z) (mod n)`) THEN
  REWRITE_TAC[iword] THEN MATCH_MP_TAC(INTEGER_RULE
   `(&(val(word w:N word)):int == &w) (mod n) /\ (&w:int == z) (mod n)
    ==> (&(val(word w:N word)) == z) (mod n)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_POW; GSYM num_congruent] THEN
    REWRITE_TAC[VAL_WORD; CONG; MOD_MOD_REFL];
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_DIVISION; INT_POW_EQ_0;
           INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]]);;

let IVAL_IWORD = prove
 (`!n. --(&2 pow (dimindex (:N) - 1)) <= n /\ n < &2 pow (dimindex (:N) - 1)
       ==> ival(iword n:N word) = n`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `n:int` IVAL_IWORD_CONG) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] INT_CONG_IMP_EQ) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
   `n:int < e1
    ==> --e1 <= n /\ --e1 <= n' /\ n' < e1 /\ &2 * e1 = e
        ==> abs(n' - n) < e`)) THEN
  ASM_REWRITE_TAC[IVAL_BOUND; GSYM(CONJUNCT2 INT_POW)] THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> SUC(n - 1) = n`]);;

let IWORD_IVAL = prove
 (`!w:N word. iword(ival w) = w`,
  REWRITE_TAC[GSYM IVAL_CONG; IVAL_IWORD_CONG]);;

let IVAL_IWORD_GALOIS = prove
 (`!(w:N word) n.
        ival w = n <=>
        --(&2 pow (dimindex(:N) - 1)) <= n /\
        n < &2 pow (dimindex(:N) - 1) /\
        w = iword n`,
  MESON_TAC[IVAL_IWORD; IWORD_IVAL; IVAL_BOUND]);;

let BIT_IVAL = prove
 (`!(x:N word) i.
    bit i x <=> i < dimindex(:N) /\ ~(&2 divides (ival x div &2 pow i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_VAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[GSYM NOT_EVEN; EVEN_EXISTS; GSYM divides] THEN
    AP_TERM_TAC THEN REWRITE_TAC[num_divides] THEN MATCH_MP_TAC(INTEGER_RULE
     `(x:int == y) (mod n) ==> (n divides x <=> n divides y)`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_POW] THEN
    MATCH_MP_TAC INT_CONG_DIV2 THEN SIMP_TAC[INT_POW_LE; INT_POS] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!m. (x:int == y) (mod m) /\ n divides m ==> (y == x) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN REWRITE_TAC[IVAL_VAL_CONG] THEN
    ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_POW_ADD; INT_POW] THEN
    CONV_TAC INTEGER_RULE;
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
    SIMP_TAC[DIV_EQ_0; ARITH_EQ; EXP_EQ_0] THEN
    TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
    ASM_REWRITE_TAC[VAL_BOUND; LE_EXP; DIMINDEX_NONZERO; COND_ID]]);;

let BIT_IWORD = prove
 (`!i x. bit i (iword x:N word) <=>
         i < dimindex(:N) /\ ~(&2 divides (x div (&2 pow i)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_IVAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(INTEGER_RULE
   `(x:int == y) (mod n) ==> (n divides x <=> n divides y)`) THEN
  MATCH_MP_TAC INT_CONG_DIV2 THEN SIMP_TAC[INT_POW_LE; INT_POS] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!m. (x:int == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN
  REWRITE_TAC[IVAL_IWORD_CONG] THEN
    ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_POW_ADD; INT_POW] THEN
    CONV_TAC INTEGER_RULE);;

let INT_REM_IVAL = prove
 (`!(w:N word) k.
        k <= dimindex(:N) ==> (ival w) rem (&2 pow k) = &(val w MOD 2 EXP k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!n:int. (x == y) (mod n) /\ m divides n ==> (x == y) (mod m)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN REWRITE_TAC[IVAL_VAL_CONG] THEN
  POP_ASSUM MP_TAC THEN
  SIMP_TAC[LE_EXISTS; INT_POW_ADD; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Some "limiting" values with names in the style of C's "limits.h" macros.  *)
(* ------------------------------------------------------------------------- *)

let word_UINT_MAX = new_definition
 `word_UINT_MAX:N word = word(2 EXP dimindex(:N) - 1)`;;

let word_INT_MIN = new_definition
 `word_INT_MIN:N word = iword(--(&2 pow (dimindex(:N) - 1)))`;;

let word_INT_MAX = new_definition
 `word_INT_MAX:N word = iword(&2 pow (dimindex(:N) - 1) - &1)`;;

let WORD_INT_MIN = prove
 (`word_INT_MIN:N word = word(2 EXP (dimindex(:N) - 1))`,
  REWRITE_TAC[word_INT_MIN; WORD_IWORD; IWORD_EQ; GSYM INT_OF_NUM_POW] THEN
  MATCH_MP_TAC(INTEGER_RULE `&2 * x:int = y ==> (--x == x) (mod y)`) THEN
  REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
  SIMP_TAC[DIMINDEX_NONZERO; ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`]);;

let WORD_INT_MAX = prove
 (`word_INT_MAX:N word = word(2 EXP (dimindex(:N) - 1) - 1)`,
  REWRITE_TAC[word_INT_MAX; WORD_IWORD] THEN AP_TERM_TAC THEN
  SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_POW; LE_1; EXP_EQ_0; ARITH_EQ]);;

let VAL_WORD_UINT_MAX = prove
 (`val(word_UINT_MAX:N word) = 2 EXP dimindex(:N) - 1`,
  REWRITE_TAC[word_UINT_MAX; VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`; EXP_EQ_0] THEN ARITH_TAC);;

let IVAL_WORD_INT_MIN = prove
 (`ival(word_INT_MIN:N word) = --(&2 pow (dimindex(:N) - 1))`,
  REWRITE_TAC[word_INT_MIN] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[INT_LE_REFL; INT_ARITH `--a:int < a <=> &0 < a`] THEN
  SIMP_TAC[INT_LT_POW2]);;

let IVAL_WORD_INT_MAX = prove
 (`ival(word_INT_MAX:N word) = &2 pow (dimindex(:N) - 1) - &1`,
  REWRITE_TAC[word_INT_MAX] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[INT_ARITH `x - &1:int < x`] THEN
  MATCH_MP_TAC(INT_ARITH `&0:int < x ==> --x <= x - &1`) THEN
  SIMP_TAC[INT_LT_POW2]);;

let VAL_BOUND_ALT = prove
 (`!w:N word. val w <= val(word_UINT_MAX:N word)`,
  GEN_TAC THEN MP_TAC(ISPEC `w:N word` VAL_BOUND) THEN
  REWRITE_TAC[VAL_WORD_UINT_MAX] THEN ARITH_TAC);;

let IVAL_BOUND_ALT = prove
 (`!w:N word. ival(word_INT_MIN:N word) <= ival w /\
              ival w <= ival(word_INT_MAX:N word)`,
  GEN_TAC THEN MP_TAC(ISPEC `w:N word` IVAL_BOUND) THEN
  REWRITE_TAC[IVAL_WORD_INT_MAX; IVAL_WORD_INT_MIN] THEN INT_ARITH_TAC);;

let VAL_WORD_INT_MIN = prove
 (`val(word_INT_MIN:N word) = 2 EXP (dimindex(:N) - 1)`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; VAL_IVAL; GSYM INT_OF_NUM_POW] THEN
  REWRITE_TAC[MSB_IVAL; IVAL_WORD_INT_MIN] THEN
  SIMP_TAC[INT_NEG_LT0; INT_LT_POW2; BITVAL_CLAUSES; INT_MUL_RID] THEN
  REWRITE_TAC[INT_ARITH `--x + y:int = x <=> &2 * x = y`] THEN
  SIMP_TAC[GSYM(CONJUNCT2 INT_POW)] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC(n - 1) = n <=> ~(n = 0)`; DIMINDEX_NONZERO]);;

let INT_VAL_WORD_INT_MIN = prove
 (`&(val(word_INT_MIN:N word)):int = &2 pow (dimindex(:N) - 1)`,
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_EQ; VAL_WORD_INT_MIN]);;

let WORD_INT_MIN_ALT = prove
 (`word_INT_MIN:N word = word_of_bits {dimindex (:N) - 1}`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_INT_MIN; VAL_WORD_OF_BITS_SING] THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> 1 <= n`; DIMINDEX_GE_1]);;

let BIT_WORD_INT_MIN = prove
 (`!i. bit i (word_INT_MIN:N word) <=> i = dimindex(:N) - 1`,
  REWRITE_TAC[WORD_INT_MIN_ALT; BIT_WORD_OF_BITS_SING] THEN
  REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `n - 1 < n <=> 1 <= n`]);;

(* ------------------------------------------------------------------------- *)
(* Population count (= number of 1s in a word), as a mathematical number.    *)
(* ------------------------------------------------------------------------- *)

let word_popcount = new_definition
 `word_popcount (x:N word) = CARD(bits_of_word x)`;;

let HAS_SIZE_BITS_OF_WORD_POPCOUNT = prove
 (`!x:N word. (bits_of_word x) HAS_SIZE word_popcount x`,
  REWRITE_TAC[word_popcount; HAS_SIZE; FINITE_BITS_OF_WORD]);;

let WORD_POPCOUNT_BOUND = prove
 (`!x:N word. word_popcount x <= dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[word_popcount; bits_of_word] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

let WORD_POPCOUNT_EQ_0 = prove
 (`!x:N word. word_popcount x = 0 <=> x = word 0`,
  SIMP_TAC[CARD_EQ_0; word_popcount; FINITE_BITS_OF_WORD] THEN
  REWRITE_TAC[BITS_OF_WORD_EQ_EMPTY]);;

let WORD_POPCOUNT_0 = prove
 (`word_popcount(word 0) = 0`,
  REWRITE_TAC[WORD_POPCOUNT_EQ_0]);;

let WORD_POPCOUNT_1 = prove
 (`word_popcount(word 1) = 1`,
  REWRITE_TAC[word_popcount; BITS_OF_WORD_1; CARD_SING]);;

(* ------------------------------------------------------------------------- *)
(* Parity (= evenness or oddity of the popcount).                            *)
(* ------------------------------------------------------------------------- *)

let word_evenparity = new_definition
 `word_evenparity (x:N word) <=> EVEN(word_popcount x)`;;

let word_oddparity = new_definition
 `word_oddparity (x:N word) <=> ODD(word_popcount x)`;;

let NOT_WORD_EVENPARITY = prove
 (`!x:N word. ~(word_evenparity x) <=> word_oddparity x`,
  REWRITE_TAC[word_evenparity; word_oddparity; NOT_EVEN]);;

let NOT_WORD_ODDPARITY = prove
 (`!x:N word. ~(word_oddparity x) <=> word_evenparity x`,
  REWRITE_TAC[word_evenparity; word_oddparity; NOT_ODD]);;

let WORD_EVENPARITY_0 = prove
 (`word_evenparity(word 0:N word)`,
  REWRITE_TAC[word_evenparity; WORD_POPCOUNT_0; EVEN]);;

let WORD_ODDPARITY_0 = prove
 (`~word_oddparity(word 0:N word)`,
  REWRITE_TAC[NOT_WORD_ODDPARITY; WORD_EVENPARITY_0]);;

let WORD_EVENPARITY_1 = prove
 (`~word_evenparity(word 1:N word)`,
  REWRITE_TAC[word_evenparity; WORD_POPCOUNT_1] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WORD_ODDPARITY_1 = prove
 (`word_oddparity(word 1:N word)`,
  REWRITE_TAC[GSYM NOT_WORD_EVENPARITY; WORD_EVENPARITY_1]);;

(* ------------------------------------------------------------------------- *)
(* Modular arithmetic operations in general, unsigned and signed.            *)
(* ------------------------------------------------------------------------- *)

let modular = new_definition
 `modular op (x:(N)word) (y:(N)word) = word(op (val x) (val y)):(N)word`;;

let VAL_MODULAR = prove
 (`!op x y:(N)word.
        val(modular op x y) = (op (val x) (val y)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[modular; VAL_WORD]);;

let CONG_MODULAR = prove
 (`!op x y:(N)word.
       (val(modular op x y) == op (val x) (val y))
       (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[VAL_MODULAR; CONG_LMOD] THEN CONV_TAC NUMBER_RULE);;

let imodular = new_definition
 `imodular op (x:(N)word) (y:(N)word) =
        iword(op (ival x) (ival y)):(N)word`;;

let CONG_IMODULAR = prove
 (`!op x y:(N)word.
       (ival(imodular op x y) == op (ival x) (ival y))
       (mod (&2 pow (dimindex(:N))))`,
  REWRITE_TAC[imodular; IVAL_IWORD_CONG]);;

(* ------------------------------------------------------------------------- *)
(* Relational operations in general w.r.t. unsigned or signed value.         *)
(* ------------------------------------------------------------------------- *)

let relational2 = new_definition
 `relational2 r (x:(N)word) (y:(N)word) :bool = r (val x) (val y)`;;

let irelational2 = new_definition
 `irelational2 r (x:(N)word) (y:(N)word) :bool = r (ival x) (ival y)`;;

(* ------------------------------------------------------------------------- *)
(* Bitwise operations in general.                                            *)
(* ------------------------------------------------------------------------- *)

let bitwise1 = new_definition
 `(bitwise1 op:N word->N word) x = mk_word(lambda i. op(bitvector x$i))`;;

let bitwise2 = new_definition
 `(bitwise2 op:N word->N word->N word) x y =
        mk_word(lambda i. op (bitvector x$i) (bitvector y$i))`;;

let BIT_BITWISE1 = prove
 (`!op (x:N word) k.
        bit k (bitwise1 op x) <=>
        k < dimindex(:N) /\ op(bit k x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[bitwise1; word_tybij] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC);;

let BIT_BITWISE2 = prove
 (`!op (x:N word) (y:N word) k.
        bit k (bitwise2 op x y) <=>
        k < dimindex(:N) /\ op (bit k x) (bit k y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[bitwise2; word_tybij] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main word operations. Where there is any meaningful difference        *)
(* between unsigned and signed we use a "u" or an "i" in the names.          *)
(* ------------------------------------------------------------------------- *)

let word_not = new_definition
 `word_not = bitwise1 (~)`;;

let BIT_WORD_NOT = prove
 (`!(x:N word) k. bit k (word_not x) <=> k < dimindex(:N) /\ ~bit k x`,
  REWRITE_TAC[word_not; BIT_BITWISE1]);;

let BITS_OF_WORD_NOT = prove
 (`!w:N word. bits_of_word(word_not w) =
              {i | i < dimindex(:N)} DIFF bits_of_word w`,
  REWRITE_TAC[bits_of_word; BIT_WORD_NOT] THEN SET_TAC[]);;

let WORD_OF_BITS_DIFF = prove
 (`!s t. {i | i < dimindex(:N)} SUBSET s
         ==> word_of_bits(s DIFF t):N word = word_not(word_of_bits t)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_NOT] THEN
  REWRITE_TAC[BITS_OF_WORD_OF_BITS] THEN SET_TAC[]);;

let VAL_WORD_NOT = prove
 (`!w:N word. val(word_not w) = 2 EXP dimindex(:N) - 1 - val w`,
  GEN_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `(m + n) + 1 = p ==> m = p - 1 - n`) THEN
  SIMP_TAC[val_def; GSYM NSUM_ADD; FINITE_NUMSEG_LT] THEN
  SIMP_TAC[GSYM LEFT_ADD_DISTRIB; BIT_WORD_NOT] THEN
  SIMP_TAC[BITVAL_NOT; BITVAL_BOUND; SUB_ADD; MULT_CLAUSES] THEN
  SPEC_TAC(`dimindex(:N)`,`k:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; ADD_CLAUSES; MULT_CLAUSES] THEN
  ASM_ARITH_TAC);;

let WORD_POPCOUNT_NOT = prove
 (`!x:N word. word_popcount(word_not x) = dimindex(:N) - word_popcount x`,
  GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE
   `x + y:num = z ==> x = z - y`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  REWRITE_TAC[word_popcount] THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; BITS_OF_WORD_NOT] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s DIFF t UNION t = s <=> t SUBSET s`] THEN
  REWRITE_TAC[bits_of_word; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

let word_and = new_definition
 `word_and = bitwise2 (/\)`;;

let BIT_WORD_AND = prove
 (`!op (x:N word) (y:N word) k.
        bit k (word_and x y) <=>
        k < dimindex(:N) /\ bit k x /\ bit k y`,
  REWRITE_TAC[word_and; BIT_BITWISE2]);;

let BIT_WORD_AND_ALT = prove
 (`!(x:N word) y k. bit k (word_and x y) <=> bit k x /\ bit k y`,
  MESON_TAC[BIT_WORD_AND; BIT_TRIVIAL; NOT_LT]);;

let BITS_OF_WORD_AND = prove
 (`!v w:N word.
        bits_of_word(word_and v w) = bits_of_word v INTER bits_of_word w`,
  REWRITE_TAC[bits_of_word; BIT_WORD_AND] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_AND_EQ_0 = prove
 (`!v w:N word.
        word_and v w = word 0 <=> DISJOINT (bits_of_word v) (bits_of_word w)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_AND; BITS_OF_WORD_0] THEN
  SET_TAC[]);;

let WORD_OF_BITS_INTER = prove
 (`!s t. word_of_bits(s INTER t):N word =
         word_and (word_of_bits s) (word_of_bits t)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_AND] THEN
  REWRITE_TAC[BITS_OF_WORD_OF_BITS] THEN SET_TAC[]);;

let WORD_AND_WORD_OF_BITS_SING = prove
 (`!(w:N word) k.
        word_and w (word_of_bits {k}) =
        if bit k w then word_of_bits {k} else word 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_OF_BITS; BIT_WORD_0] THEN
  ASM SET_TAC[]);;

let WORD_OF_BITS_SING_AND_WORD = prove
 (`!(w:N word) k.
        word_and (word_of_bits {k}) w =
        if bit k w then word_of_bits {k} else word 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_OF_BITS; BIT_WORD_0] THEN
  ASM SET_TAC[]);;

let word_or = new_definition
 `word_or = bitwise2 (\/)`;;

let BIT_WORD_OR = prove
 (`!op (x:N word) (y:N word) k.
        bit k (word_or x y) <=>
        k < dimindex(:N) /\ (bit k x \/ bit k y)`,
  REWRITE_TAC[word_or; BIT_BITWISE2]);;

let BIT_WORD_OR_ALT = prove
 (`!(x:N word) y k. bit k (word_or x y) <=> bit k x \/ bit k y`,
  MESON_TAC[BIT_WORD_OR; BIT_TRIVIAL; NOT_LT]);;

let BITS_OF_WORD_OR = prove
 (`!v w:N word.
        bits_of_word(word_or v w) = bits_of_word v UNION bits_of_word w`,
  REWRITE_TAC[bits_of_word; BIT_WORD_OR] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_OF_BITS_UNION = prove
 (`!s t. word_of_bits(s UNION t):N word =
         word_or (word_of_bits s) (word_of_bits t)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_OR] THEN
  REWRITE_TAC[BITS_OF_WORD_OF_BITS] THEN SET_TAC[]);;

let word_xor = new_definition
 `word_xor = bitwise2 (\x y. ~(x <=> y))`;;

let BIT_WORD_XOR = prove
 (`!op (x:N word) (y:N word) k.
        bit k (word_xor x y) <=>
        k < dimindex(:N) /\ ~(bit k x <=> bit k y)`,
  REWRITE_TAC[word_xor; BIT_BITWISE2]);;

let BIT_WORD_XOR_ALT = prove
 (`!(x:N word) y k. bit k (word_xor x y) <=> ~(bit k x <=> bit k y)`,
  MESON_TAC[BIT_WORD_XOR; BIT_TRIVIAL; NOT_LT]);;

let VAL_WORD_ADD_AND_XOR,VAL_WORD_ADD_AND_OR = (CONJ_PAIR o prove)
 (`(!x y:N word. val x + val y = 2 * val(word_and x y) + val(word_xor x y)) /\
   (!x y:N word. val x + val y = val(word_and x y) + val(word_or x y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[val_def; GSYM NSUM_LMUL] THEN
  SIMP_TAC[GSYM NSUM_ADD; FINITE_NUMSEG_LT] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; BIT_WORD_AND; BIT_WORD_XOR; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY ASM_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

let VAL_WORD_OR_DISJOINT = prove
 (`!x y:N word.
        word_and x y = word 0 ==> val(word_or x y) = val x + val y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[VAL_WORD_ADD_AND_OR] THEN
  ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES]);;

let VAL_WORD_OR_AND_XOR = prove
 (`!x y:N word. val(word_or x y) = val(word_and x y) + val(word_xor x y)`,
  ONCE_REWRITE_TAC[ARITH_RULE `a = b + c <=> b + a = 2 * b + c`] THEN
  MESON_TAC[VAL_WORD_ADD_AND_XOR; VAL_WORD_ADD_AND_OR]);;

let word_add = new_definition
 `word_add = modular (+)`;;

let VAL_WORD_ADD = prove
 (`!x y:(N) word.
        val(word_add x y) = (val(x) + val(y)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_add; VAL_MODULAR]);;

let VAL_WORD_ADD_CASES = prove
 (`!x y:(N) word.
        val(word_add x y) =
        if val x + val y < 2 EXP dimindex(:N) then val x + val y
        else (val x + val y) - 2 EXP dimindex(:N)`,
  SIMP_TAC[VAL_WORD_ADD; VAL_BOUND; MOD_ADD_CASES]);;

let VAL_WORD_ADC_CASES = prove
 (`!c x y:(N) word.
        val(c) < 2
        ==> val(word_add (word_add x y) c) =
            if val x + val y + val c < 2 EXP dimindex(:N)
            then val x + val y + val c
            else (val x + val y + val c) - 2 EXP dimindex(:N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
  MATCH_MP_TAC MOD_CASES THEN MATCH_MP_TAC(ARITH_RULE
   `x < n /\ y < n /\ c < 2 ==> x + y + c < 2 * n`) THEN
  ASM_REWRITE_TAC[VAL_BOUND]);;

let INT_VAL_WORD_ADD_CASES = prove
 (`!x y:(N) word.
      &(val(word_add x y)):int =
      if &(val x) + &(val y):int < &2 pow dimindex(:N) then &(val x) + &(val y)
      else (&(val x) + &(val y)) - &2 pow dimindex(:N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_ADD_CASES] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NOT_LT; INT_OF_NUM_SUB]);;

let CONG_WORD_ADD = prove
 (`!x y:(N)word.
        (val(word_add x y) == val x + val y) (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[word_add; CONG_MODULAR]);;

let WORD_ADD = prove
 (`!x y. word(x + y):N word = word_add (word x) (word y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_CONG] THEN
  MP_TAC(ISPECL [`word x:N word`; `word y:N word`] CONG_WORD_ADD) THEN
  MAP_EVERY (MP_TAC o C ISPEC VAL_WORD_CONG)
   [`x + y:num`; `y:num`; `x:num`] THEN
  CONV_TAC NUMBER_RULE);;

let ICONG_WORD_ADD = prove
 (`!x y:(N)word.
        (ival(word_add x y) == ival x + ival y) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `y:N word`; `word_add x y:N word`] THEN
  MP_TAC(ISPECL [`x:N word`; `y:N word`] CONG_WORD_ADD) THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD] THEN
  CONV_TAC INTEGER_RULE);;

let IWORD_INT_ADD = prove
 (`!x y. iword(x + y):N word = word_add (iword x) (iword y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IVAL_CONG] THEN
  MP_TAC(ISPECL [`iword x:N word`; `iword y:N word`] ICONG_WORD_ADD) THEN
  MAP_EVERY (MP_TAC o C ISPEC IVAL_IWORD_CONG)
   [`x + y:int`; `y:int`; `x:int`] THEN
  CONV_TAC INTEGER_RULE);;

let WORD_ADD_IMODULAR = prove
 (`(word_add:N word->N word->N word) = imodular ( + )`,
  REWRITE_TAC[FUN_EQ_THM; GSYM IVAL_CONG] THEN
  ASM_MESON_TAC[ICONG_WORD_ADD; CONG_IMODULAR; INTEGER_RULE
   `(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)`]);;

let word_sub = new_definition
 `(word_sub:(N)word->(N)word->(N)word) =
        modular (\x y. x + (2 EXP dimindex(:N) - y))`;;

let VAL_WORD_SUB = prove
 (`!x y:(N) word.
        val(word_sub x y) =
        (val(x) + (2 EXP dimindex(:N) - val(y))) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_sub; VAL_MODULAR]);;

let VAL_WORD_SUB_CASES = prove
 (`!x y:(N) word.
        val(word_sub x y) =
        if val y <= val x then val(x) - val(y)
        else val(x) + (2 EXP dimindex(:N) - val(y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT] THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1`;
    MATCH_MP_TAC MOD_LT] THEN
  MAP_EVERY (MP_TAC o C ISPEC VAL_BOUND) [`x:N word`; `y:N word`] THEN
  ASM_ARITH_TAC);;

let INT_VAL_WORD_SUB_CASES = prove
 (`!x y:(N) word.
        &(val(word_sub x y)):int =
        if &(val y):int <= &(val x) then &(val x) - &(val y)
        else &(val x) + (&2 pow dimindex(:N) - &(val y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_POW; INT_OF_NUM_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INT_OF_NUM_ADD; INT_OF_NUM_SUB; VAL_BOUND; LT_IMP_LE]);;

let CONG_WORD_SUB = prove
 (`!x y:(N)word.
        (val(word_sub x y) + val y == val x) (mod (2 EXP dimindex(:N)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONG; VAL_MODULAR; word_sub] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  SIMP_TAC[VAL_BOUND; ARITH_RULE `y:num < n ==> (x + n - y) + y = x + n`] THEN
  REWRITE_TAC[GSYM CONG] THEN CONV_TAC NUMBER_RULE);;

let ICONG_WORD_SUB = prove
 (`!x y:N word.
        (ival(word_sub x y) == ival x - ival y) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `y:N word`; `word_sub x y:N word`] THEN
  MP_TAC(ISPECL [`x:N word`; `y:N word`] CONG_WORD_SUB) THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD] THEN
  CONV_TAC INTEGER_RULE);;

let IWORD_INT_SUB = prove
 (`!x y. iword(x - y):N word = word_sub (iword x) (iword y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IVAL_CONG] THEN
  MP_TAC(ISPECL [`iword x:N word`; `iword y:N word`] ICONG_WORD_SUB) THEN
  MAP_EVERY (MP_TAC o C ISPEC IVAL_IWORD_CONG)
   [`x - y:int`; `y:int`; `x:int`] THEN
  CONV_TAC INTEGER_RULE);;

let WORD_SUB_IMODULAR = prove
 (`(word_sub:N word->N word->N word) = imodular ( - )`,
  REWRITE_TAC[FUN_EQ_THM; GSYM IVAL_CONG] THEN
  ASM_MESON_TAC[ICONG_WORD_SUB; CONG_IMODULAR; INTEGER_RULE
   `(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)`]);;

let WORD_SUB = prove
 (`!x y. word(x - y):N word =
         if y <= x then word_sub (word x) (word y) else word 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[WORD_IWORD; GSYM INT_OF_NUM_SUB; IWORD_INT_SUB];
    ASM_MESON_TAC[SUB_EQ_0; LE_CASES]]);;

let word_neg = new_definition
 `word_neg (a:N word) = word_sub (word 0) a`;;

let VAL_WORD_NEG = prove
 (`!x:(N) word.
        val(word_neg x) =
        (2 EXP dimindex(:N) - val(x)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_neg; VAL_WORD_SUB; VAL_WORD_0; ADD_CLAUSES]);;

let VAL_WORD_NEG_CASES = prove
 (`!x:(N) word.
        val(word_neg x) =
        if val x = 0 then 0 else 2 EXP dimindex(:N) - val(x)`,
  REWRITE_TAC[word_neg; VAL_WORD_SUB_CASES; VAL_WORD_0] THEN
  SIMP_TAC[LE; ADD_CLAUSES; SUB_REFL]);;

let INT_VAL_WORD_NEG_CASES = prove
 (`!x:N word.
        &(val(word_neg x)):int =
        if &(val x):int = &0 then &0 else &2 pow dimindex(:N) - &(val x)`,
  SIMP_TAC[INT_OF_NUM_POW; INT_OF_NUM_SUB; LT_IMP_LE; VAL_BOUND] THEN
  REWRITE_TAC[VAL_WORD_NEG_CASES; INT_OF_NUM_EQ] THEN MESON_TAC[]);;

let CONG_WORD_NEG = prove
 (`!x:(N)word.
        (val(word_neg x) + val x == 0) (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[word_neg] THEN MESON_TAC[CONG_WORD_SUB; VAL_WORD_0]);;

let ICONG_WORD_NEG = prove
 (`!x:(N)word.
        (ival(word_neg x) == --(ival x)) (mod (&2 pow dimindex(:N)))`,
  REWRITE_TAC[word_neg] THEN
  MESON_TAC[ICONG_WORD_SUB; INT_SUB_LZERO; IVAL_WORD_0]);;

let IWORD_INT_NEG = prove
 (`!x. iword(--x):N word = word_neg (iword x)`,
  REWRITE_TAC[GSYM INT_SUB_LZERO; word_neg] THEN
  REWRITE_TAC[IWORD_INT_SUB; GSYM WORD_IWORD]);;

let WORD_NEG_AS_ADD = prove
 (`!x:N word. word_neg x = word_add (word_not x) (word 1)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_NEG] THEN
  REWRITE_TAC[MOD_MOD_REFL; VAL_WORD_ADD; VAL_WORD_1; VAL_WORD_NOT] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  SIMP_TAC[VAL_BOUND; ARITH_RULE `n < e ==> (e - 1 - n) + 1 = e - n`]);;

let WORD_NOT_AS_SUB = prove
 (`!x:N word. word_not x = word_sub (word_neg x) (word 1)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_SUB; VAL_WORD_NEG] THEN
  REWRITE_TAC[MOD_MOD_REFL; VAL_WORD_SUB; VAL_WORD_1; VAL_WORD_NOT] THEN
  CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC[VAL_BOUND; ARITH_RULE
   `x < e ==> (e - x) + (e - 1) = e + (e - 1 - x)`] THEN
  REWRITE_TAC[GSYM CONG] THEN CONV_TAC NUMBER_RULE);;

let VAL_WORD_NEG_1 = prove
 (`val(word_neg(word 1:N word)) = 2 EXP dimindex(:N) - 1`,
  REWRITE_TAC[VAL_WORD_NEG_CASES; VAL_WORD_1; ARITH_EQ]);;

let IVAL_WORD_NEG_1 = prove
 (`ival(word_neg(word 1:N word)) = -- &1`,
  REWRITE_TAC[ival; VAL_WORD_NEG_1] THEN
  REWRITE_TAC[ARITH_RULE `m - 1 < n <=> ~(n = 0) /\ m <= n`] THEN
  SIMP_TAC[LE_EXP; EXP_EQ_0; ARITH_EQ; DIMINDEX_NONZERO;
           ARITH_RULE `n <= n - 1 <=> n = 0`;
           GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_POW; LE_1] THEN
  INT_ARITH_TAC);;

let IVAL_EQ_MINUS1 = prove
 (`!w:N word. ival w = -- &1 <=> w = word_neg(word 1)`,
  REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_NEG_1]);;

let WORD_NEG_1 = prove
 (`word_neg(word 1:N word) = word_not(word 0)`,
  REWRITE_TAC[WORD_NOT_AS_SUB; word_neg] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD_SUB_CASES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let word_mul = new_definition
 `word_mul = modular ( * )`;;

let VAL_WORD_MUL = prove
 (`!x y:(N)word.
        val(word_mul x y) = (val(x) * val(y)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_mul; VAL_MODULAR]);;

let CONG_WORD_MUL = prove
 (`!x y:(N)word.
        (val(word_mul x y) == val x * val y) (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[word_mul; CONG_MODULAR]);;

let WORD_MUL = prove
 (`!x y. word(x * y):N word = word_mul (word x) (word y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_CONG] THEN
  MP_TAC(ISPECL [`word x:N word`; `word y:N word`] CONG_WORD_MUL) THEN
  MAP_EVERY (MP_TAC o C ISPEC VAL_WORD_CONG)
   [`x * y:num`; `y:num`; `x:num`] THEN
  CONV_TAC NUMBER_RULE);;

let ICONG_WORD_MUL = prove
 (`!x y:(N)word.
        (ival(word_mul x y) == ival x * ival y) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`x:N word`; `y:N word`] CONG_WORD_MUL) THEN
  MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `y:N word`; `word_mul x y:N word`] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL] THEN
  CONV_TAC INTEGER_RULE);;

let IWORD_INT_MUL = prove
 (`!x y. iword(x * y):N word = word_mul (iword x) (iword y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IVAL_CONG] THEN
  MP_TAC(ISPECL [`iword x:N word`; `iword y:N word`] ICONG_WORD_MUL) THEN
  MAP_EVERY (MP_TAC o C ISPEC IVAL_IWORD_CONG)
   [`x * y:int`; `y:int`; `x:int`] THEN
  CONV_TAC INTEGER_RULE);;

let WORD_MUL_IMODULAR = prove
 (`(word_mul:N word->N word->N word) = imodular ( * )`,
  REWRITE_TAC[FUN_EQ_THM; GSYM IVAL_CONG] THEN
  ASM_MESON_TAC[ICONG_WORD_MUL; CONG_IMODULAR; INTEGER_RULE
   `(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)`]);;

let word_udiv = new_definition
 `word_udiv = modular (DIV)`;;

let VAL_WORD_UDIV = prove
 (`!x y:(N)word.
        val(word_udiv x y) = val(x) DIV val(y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_udiv; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
   `m DIV n <= m /\ m < p ==> m DIV n < p`) THEN
  REWRITE_TAC[VAL_BOUND; DIV_LE]);;

let word_umod = new_definition
 `word_umod = modular (MOD)`;;

let VAL_WORD_UMOD = prove
 (`!x y:(N)word.
        val(word_umod x y) = val(x) MOD val(y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_umod; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
   `m MOD n <= m /\ m < p ==> m MOD n < p`) THEN
  REWRITE_TAC[VAL_BOUND; MOD_LE]);;

let word_umax = new_definition
 `word_umax = modular (MAX)`;;

let word_imax = new_definition
 `word_imax = imodular (max)`;;

let VAL_WORD_UMAX = prove
 (`!x y:(N)word.
        val(word_umax x y) = MAX (val x) (val y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_umax; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[ARITH_RULE `MAX x y < n <=> x < n /\ y < n`] THEN
  REWRITE_TAC[VAL_BOUND]);;

let IVAL_WORD_IMAX = prove
 (`!x y:(N)word.
        ival(word_imax x y) = max (ival x) (ival y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_imax; imodular] THEN
  REWRITE_TAC[INT_MAX] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IWORD_IVAL]);;

let word_umin = new_definition
 `word_umin = modular (MIN)`;;

let word_imin = new_definition
 `word_imin = imodular (min)`;;

let VAL_WORD_UMIN = prove
 (`!x y:(N)word.
        val(word_umin x y) = MIN (val x) (val y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_umin; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[ARITH_RULE `MIN x y < n <=> x < n \/ y < n`] THEN
  REWRITE_TAC[VAL_BOUND]);;

let IVAL_WORD_IMIN = prove
 (`!x y:(N)word.
        ival(word_imin x y) = min (ival x) (ival y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_imin; imodular] THEN
  REWRITE_TAC[INT_MIN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IWORD_IVAL]);;

let word_shl = new_definition
  `word_shl (x:(N)word) n = word((val x) * 2 EXP n):(N)word`;;

let VAL_WORD_SHL = prove
 (`!(x:N word) n.
        val(word_shl x n) = (2 EXP n * val x) MOD (2 EXP dimindex(:N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; MULT_SYM]);;

let CONG_WORD_SHL = prove
 (`!(x:N word) n.
        (val(word_shl x n) == 2 EXP n * val x) (mod (2 EXP dimindex(:N)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SHL; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REFL_TAC);;

let ICONG_WORD_SHL = prove
 (`!(x:N word) n.
        (ival(word_shl x n) == &2 pow n * ival x) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`x:N word`; `n:num`] CONG_WORD_SHL) THEN
  MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `word_shl x n:N word`] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL] THEN
  CONV_TAC INTEGER_RULE);;

let BIT_WORD_SHL = prove
 (`!(x:N word) m i.
        bit i (word_shl x n) <=>
        n <= i /\ i < dimindex(:N) /\ bit (i - n) x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i < dimindex(:N)` THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[bit]] THEN
  REWRITE_TAC[word_shl; BIT_VAL; VAL_WORD] THEN
  SUBGOAL_THEN `dimindex(:N) = i + (dimindex(:N) - i)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD; GSYM DIV_MOD]] THEN
  ASM_SIMP_TAC[ODD_MOD_POW2; ARITH_RULE `i < n ==> ~(n - i = 0)`] THEN
  ASM_CASES_TAC `n:num <= i` THEN ASM_REWRITE_TAC[] THENL
   [AP_TERM_TAC THEN
    SUBGOAL_THEN `i:num = (i - n) + n`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD]] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC DIV_MULT2 THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    SUBGOAL_THEN `n:num = i + (n - i)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ONCE_REWRITE_TAC[MULT_SYM]] THEN
    REWRITE_TAC[EXP_ADD; GSYM MULT_ASSOC] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ; EXP_EQ_0] THEN
    REWRITE_TAC[ODD_MULT; ODD_EXP] THEN ASM_ARITH_TAC]);;

let WORD_SHL_WORD_OF_BITS = prove
 (`!(x:N word) n.
        word_shl x n =
        word_of_bits {i | n <= i /\ i < dimindex(:N) /\ bit (i - n) x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[BIT_WORD_SHL] THEN SET_TAC[]);;

let WORD_SHL_ZERO = prove
 (`!x:N word. word_shl x 0 = x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; EXP; MULT_CLAUSES] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND]);;

let WORD_SHL_COMPOSE = prove
 (`!(x:N word) m n. word_shl (word_shl x m) n = word_shl x (m + n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; EXP_ADD] THEN
  REWRITE_TAC[WORD_EQ; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[MULT_ASSOC]);;

let word_ushr = new_definition
  `word_ushr (x:(N)word) n =
        word((val x) DIV (2 EXP n)):(N)word`;;

let VAL_WORD_USHR = prove
 (`!(x:N word) n.
        val(word_ushr x n) = val x DIV (2 EXP n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
   `m DIV n <= m /\ m < p ==> m DIV n < p`) THEN
  REWRITE_TAC[VAL_BOUND; DIV_LE]);;

let WORD_USHR_EQ_0 = prove
 (`!(x:N word) n. word_ushr x n = word 0 <=> val x < 2 EXP n`,
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_USHR] THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let BIT_WORD_USHR = prove
 (`!(x:N word) n i.
        bit i (word_ushr x n) <=> bit (i + n) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ushr; BIT_VAL; VAL_WORD] THEN
  REWRITE_TAC[DIV_MOD; DIV_DIV] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
  ASM_REWRITE_TAC[VAL_BOUND; LE_EXP; DIMINDEX_NONZERO] THEN
  ARITH_TAC);;

let WORD_USHR_WORD_OF_BITS = prove
 (`!(x:N word) n.
        word_ushr x n =
        word_of_bits {i | i < dimindex(:N) /\ bit (i + n) x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[BIT_WORD_USHR] THEN SET_TAC[]);;

let WORD_USHR_ZERO = prove
 (`!x:N word. word_ushr x 0 = x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; EXP; DIV_1] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND]);;

let WORD_USHR_COMPOSE = prove
 (`!(x:N word) m n. word_ushr (word_ushr x m) n = word_ushr x (m + n)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_ushr] THEN
  REWRITE_TAC[VAL_WORD_USHR] THEN REWRITE_TAC[EXP_ADD; DIV_DIV]);;

let WORD_USHR_MSB = prove
 (`!x:N word. word_ushr x (dimindex(:N) - 1) =
              if bit (dimindex(:N) - 1) x then word 1 else word 0`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD_0; BIT_WORD_1] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  MATCH_MP_TAC(REWRITE_RULE[] BIT_TRIVIAL) THEN ASM_ARITH_TAC);;

let WORD_USHR_MSB_EQ = prove
 (`(!x:N word. word_ushr x (dimindex(:N) - 1) = word 1 <=>
               bit (dimindex(:N) - 1) x) /\
   (!x:N word. word_ushr x (dimindex(:N) - 1) = word 0 <=>
               ~bit (dimindex(:N) - 1) x) /\
   (!P (x:N word).
        (word_ushr x (dimindex(:N) - 1) = if P then word 1 else word 0) <=>
        (bit (dimindex(:N) - 1) x <=> P)) /\
   (!P (x:N word).
        (word_ushr x (dimindex(:N) - 1) = if P then word 0 else word 1) <=>
        (bit (dimindex(:N) - 1) x <=> ~P))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_USHR_MSB] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_NE_10]));;

let word_ishr = new_definition
  `(word_ishr:N word ->num->N word) x n = iword((ival x) div (&2 pow n))`;;

let IVAL_WORD_ISHR = prove
 (`!(x:N word) n. ival(word_ishr x n) = (ival x) div (&2 pow n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ishr] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  SIMP_TAC[INT_LE_DIV_EQ; INT_DIV_LT_EQ; INT_LT_POW2] THEN
  MP_TAC(ISPEC `x:N word` IVAL_BOUND) THEN
  MATCH_MP_TAC(INT_ARITH
   `&1 * a:int <= t * a
    ==> --a <= x /\ x < a ==> t * --a <= x /\ x < t * a`) THEN
  MATCH_MP_TAC INT_LE_RMUL THEN
  SIMP_TAC[INT_LE_POW2; INT_LT_IMP_LE; INT_LT_POW2]);;

let WORD_ISHR_EQ_0 = prove
 (`!(x:N word) n.
        word_ishr x n = word 0 <=> &0 <= ival x /\ ival x < &2 pow n`,
  REWRITE_TAC[GSYM IVAL_EQ_0; IVAL_WORD_ISHR] THEN
  SIMP_TAC[INT_DIV_EQ_0; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM]);;

let BIT_WORD_ISHR = prove
 (`!(w:N word) n i.
        bit i (word_ishr w n) <=>
        if i + n < dimindex(:N) then bit (i + n) w
        else i < dimindex(:N) /\ bit (dimindex(:N) - 1) w`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i < dimindex(:N)` THENL
   [ALL_TAC; ASM_REWRITE_TAC[BIT_IVAL] THEN ASM_ARITH_TAC] THEN
  ASM_REWRITE_TAC[word_ishr; BIT_IWORD] THEN
  SIMP_TAC[INT_DIV_DIV; INT_POW_LE; INT_POS] THEN
  ONCE_REWRITE_TAC[INT_MUL_SYM] THEN REWRITE_TAC[GSYM INT_POW_ADD] THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC[BIT_IVAL]; ALL_TAC] THEN
  REWRITE_TAC[MSB_IVAL; GSYM INT_NOT_LE] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `--(&2 pow (i + n)) <= ival(w:N word) /\ ival w < &2 pow (i + n)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `w:N word` IVAL_BOUND) THEN MATCH_MP_TAC(INT_ARITH
     `a:int <= b ==> --a <= x /\ x < a ==> --b <= x /\ x < b`) THEN
    MATCH_MP_TAC INT_POW_MONO THEN REWRITE_TAC[INT_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ival(w:N word)`; `(&2:int) pow (i + n)`]
        INT_DIV_EQ_0) THEN
  ASM_REWRITE_TAC[INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ; INT_ABS_POW;
                  INT_ABS_NUM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `-- &1 <= ival(w:N word) div &2 pow (i + n) /\
    ival(w:N word) div &2 pow (i + n) < &1`
  MP_TAC THENL
   [ASM_SIMP_TAC[INT_DIV_LT_EQ; INT_LE_DIV_EQ; INT_LT_POW2] THEN
    ASM_REWRITE_TAC[INT_MUL_RNEG; INT_MUL_RID];
    REWRITE_TAC[INT_ARITH
     `-- &1:int <= x /\ x < &1 <=> x = -- &1 \/ x = &0`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[INTEGER_RULE `(p:int) divides &0`] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INTEGER_RULE `(x:int) divides --y <=> x divides y`] THEN
    REWRITE_TAC[GSYM num_divides; divides; GSYM EVEN_EXISTS] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let WORD_ISHR_WORD_OF_BITS = prove
 (`!(x:N word) n.
        word_ishr x n =
        word_of_bits {i | if i < dimindex(:N) - n then bit (i + n) x
                          else bit (dimindex(:N) - 1) x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
  REWRITE_TAC[WORD_OF_BITS_EQ] THEN X_GEN_TAC `i:num` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; BIT_WORD_ISHR] THEN
  REWRITE_TAC[ARITH_RULE `i + n:num < m <=> i < m - n`]);;

let WORD_ISHR_ZERO = prove
 (`!x:N word. word_ishr x 0 = x`,
  REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_ISHR; INT_POW; INT_DIV_1]);;

let WORD_ISHR_COMPOSE = prove
 (`!(x:N word) m n. word_ishr (word_ishr x m) n = word_ishr x (m + n)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_ishr] THEN
  REWRITE_TAC[IVAL_WORD_ISHR; INT_POW_ADD] THEN
  SIMP_TAC[INT_DIV_DIV; INT_POW_LE; INT_POS]);;

let word_ror = new_definition
 `(word_ror:N word->num->N word) w n =
        word_of_bits {i | bit ((i + n) MOD dimindex(:N)) w}`;;

let word_rol = new_definition
 `(word_rol:N word->num->N word) w n =
        word_of_bits {i | bit (num_of_int((&i - &n) rem &(dimindex(:N)))) w}`;;

let WORD_ROR_ROL_GEN = prove
 (`!(w:N word) n.
        word_ror w n = word_rol w (dimindex(:N) - n MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror; word_rol; WORD_OF_BITS_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o rand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[INT_DIVISION; DIMINDEX_NONZERO; INT_OF_NUM_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; DIVISION; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_ADD; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(k:int == n) (mod d)
    ==> (i + n == i - (d - k)) (mod d)`) THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let WORD_ROL_ROR_GEN = prove
 (`!(w:N word) n.
        word_rol w n = word_ror w (dimindex(:N) - n MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror; word_rol; WORD_OF_BITS_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[INT_DIVISION; DIMINDEX_NONZERO; INT_OF_NUM_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; DIVISION; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_REM_EQ; GSYM INT_OF_NUM_ADD] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; DIVISION; DIMINDEX_NONZERO] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(k:int == n) (mod d)
    ==> (i - n == i + (d - k)) (mod d)`) THEN
  REWRITE_TAC[CONG_LMOD; INT_OF_NUM_REM; GSYM num_congruent] THEN
  CONV_TAC NUMBER_RULE);;

let WORD_ROR_PERIODIC = prove
 (`!(w:N word) m n.
        (m == n) (mod dimindex(:N)) ==> word_ror w m = word_ror w n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
   `(m == n) (mod d) ==> !i:num. (i + m == i + n) (mod d)`)) THEN
  SIMP_TAC[CONG]);;

let WORD_ROR_MOD = prove
 (`!(w:N word) n. word_ror w n = word_ror w (n MOD dimindex(:N))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
  REWRITE_TAC[CONG_RMOD] THEN CONV_TAC NUMBER_RULE);;

let WORD_ROR_EQ_SELF = prove
 (`!(w:N word) n. dimindex(:N) divides n ==> word_ror w n = w`,
  SIMP_TAC[divides; LEFT_IMP_EXISTS_THM; word_ror] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `i + d * n:num = n * d + i`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOD_MULT_ADD] THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_SIMP_TAC[MOD_LT; IN_ELIM_THM] THEN
  ASM_MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_ROR_ZERO = prove
 (`!w:N word. word_ror w 0 = w`,
  GEN_TAC THEN MATCH_MP_TAC WORD_ROR_EQ_SELF THEN CONV_TAC NUMBER_RULE);;

let WORD_ROL_PERIODIC = prove
 (`!(w:N word) m n.
        (m == n) (mod dimindex(:N)) ==> word_rol w m = word_rol w n`,
  SIMP_TAC[CONG; WORD_ROL_ROR_GEN]);;

let WORD_ROL_MOD = prove
 (`!(w:N word) n. word_rol w n = word_rol w (n MOD dimindex(:N))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROL_PERIODIC THEN
  REWRITE_TAC[CONG_RMOD] THEN CONV_TAC NUMBER_RULE);;

let WORD_ROL_EQ_SELF = prove
 (`!(w:N word) n. dimindex(:N) divides n ==> word_rol w n = w`,
  REWRITE_TAC[divides] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[GSYM MOD_EQ_0; WORD_ROL_ROR_GEN; SUB_0] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WORD_ROR_EQ_SELF THEN
  CONV_TAC NUMBER_RULE);;

let WORD_ROL_ZERO = prove
 (`!w:N word. word_rol w 0 = w`,
  GEN_TAC THEN MATCH_MP_TAC WORD_ROL_EQ_SELF THEN CONV_TAC NUMBER_RULE);;

let WORD_ROR_ROL = prove
 (`!(w:N word) n.
        n <= dimindex(:N) ==> word_ror w n = word_rol w (dimindex(:N) - n)`,
  REWRITE_TAC[LE_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_ROR_ROL_GEN; MOD_LT; MOD_REFL; SUB_0; SUB_REFL] THEN
  MATCH_MP_TAC WORD_ROL_PERIODIC THEN CONV_TAC NUMBER_RULE);;

let WORD_ROL_ROR = prove
 (`!(w:N word) n.
        n <= dimindex(:N) ==> word_rol w n = word_ror w (dimindex(:N) - n)`,
  REWRITE_TAC[LE_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_ROL_ROR_GEN; MOD_LT; MOD_REFL; SUB_0; SUB_REFL] THEN
  MATCH_MP_TAC WORD_ROR_PERIODIC THEN CONV_TAC NUMBER_RULE);;

let WORD_ROR_SHIFTS = prove
 (`!(w:N word) n.
        n <= dimindex(:N)
        ==> word_ror w n =
            word_or (word_ushr w n) (word_shl w (dimindex(:N) - n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror] THEN
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < dimindex(:N)` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; BIT_WORD_USHR; BIT_WORD_SHL] THEN
  REWRITE_TAC[ARITH_RULE `d - n <= i <=> ~(i + n:num < d)`] THEN
  ASM_CASES_TAC `i + n < dimindex(:N)` THEN ASM_SIMP_TAC[MOD_LT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

let WORD_ROL_SHIFTS = prove
 (`!(w:N word) n.
        n <= dimindex(:N)
        ==> word_rol w n =
            word_or (word_shl w n) (word_ushr w (dimindex(:N) - n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_ROL_ROR] THEN
  ASM_SIMP_TAC[WORD_ROR_SHIFTS; ARITH_RULE `n - m:num <= n`] THEN
  ASM_SIMP_TAC[ARITH_RULE `m:num <= n ==> n - (n - m) = m`] THEN
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OR; DISJ_SYM]);;

let BIT_WORD_ROR = prove
 (`!(w:N word) n i.
        bit i (word_ror w n) =
        if i + n MOD dimindex(:N) < dimindex(:N)
        then bit (i + n MOD dimindex(:N)) w
        else i < dimindex(:N) /\
             bit ((i + n MOD dimindex(:N)) - dimindex(:N)) w`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ROR_MOD] THEN
  SIMP_TAC[WORD_ROR_SHIFTS; MOD_LT_EQ; LT_IMP_LE; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_USHR] THEN
  COND_CASES_TAC THENL
   [ASM_CASES_TAC `bit (i + n MOD dimindex(:N)) (w:N word)` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p /\ q /\ (r <=> r') ==> (p \/ q /\ r <=> r')`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[BIT_TRIVIAL; GSYM NOT_LT];
      ASM_ARITH_TAC;
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]]);;

let BIT_WORD_ROL = prove
 (`!(w:N word) n i.
        bit i (word_rol w n) =
        if i < n MOD dimindex(:N)
        then bit (i + (dimindex(:N) - n MOD dimindex(:N))) w
        else i < dimindex(:N) /\ bit (i - n MOD dimindex(:N)) w`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ROL_MOD] THEN
  SIMP_TAC[WORD_ROL_SHIFTS; MOD_LT_EQ; LT_IMP_LE; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_USHR] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT] THENL
   [MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN
    TRANS_TAC LT_TRANS `n MOD dimindex(:N)` THEN
    ASM_REWRITE_TAC[MOD_LT_EQ; DIMINDEX_NONZERO];
    ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(q <=> F) ==> (p \/ q <=> p)`) THEN
    MATCH_MP_TAC BIT_TRIVIAL THEN ASM_ARITH_TAC]);;

let WORD_ROR_COMPOSE = prove
 (`!(x:N word) m n. word_ror (word_ror x m) n = word_ror x (m + n)`,
  REWRITE_TAC[word_ror; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  SIMP_TAC[MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_AC]);;

let WORD_ROL_COMPOSE = prove
 (`!(x:N word) m n. word_rol (word_rol x m) n = word_rol x (m + n)`,
  REWRITE_TAC[WORD_ROL_ROR_GEN; WORD_ROR_COMPOSE] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[INTEGER_RULE
   `((n - a) + (n - b):int == (n - c)) (mod n) <=> (a + b == c) (mod n)`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; GSYM num_congruent; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REFL_TAC);;

let VAL_WORD_ROR = prove
 (`!(w:N word) k.
     k <= dimindex(:N)
     ==> val(word_ror w k) =
         2 EXP (dimindex(:N) - k) * val w MOD 2 EXP k + val w DIV 2 EXP k`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
  ASM_SIMP_TAC[WORD_ROR_SHIFTS] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    SIMP_TAC[BIT_WORD_AND; BIT_WORD_USHR; BIT_WORD_SHL; BIT_WORD_0] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP(MESON[BIT_TRIVIAL; NOT_LE]
     `bit i (w:N word) ==> i < dimindex(:N)`))) THEN
    ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_SHL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MOD_MULT2; GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let VAL_WORD_ROL = prove
 (`!(w:N word) k.
        k <= dimindex(:N)
        ==> val(word_rol w k) =
            2 EXP k * val w MOD 2 EXP (dimindex(:N) - k) +
            val w DIV 2 EXP (dimindex(:N) - k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_ROL_ROR] THEN
  SIMP_TAC[VAL_WORD_ROR; ARITH_RULE `n - m:num <= n`] THEN
  ASM_SIMP_TAC[ARITH_RULE `k:num <= n ==> n - (n - k) = k`]);;

let word_ule = new_definition `word_ule = relational2 (<=)`;;
let word_uge = new_definition `word_uge = relational2 (>=)`;;
let word_ult = new_definition `word_ult = relational2 (<)`;;
let word_ugt = new_definition `word_ugt = relational2 (>)`;;

let word_ile = new_definition `word_ile = irelational2 (<=)`;;
let word_ige = new_definition `word_ige = irelational2 (>=)`;;
let word_ilt = new_definition `word_ilt = irelational2 (<)`;;
let word_igt = new_definition `word_igt = irelational2 (>)`;;

let WORD_ULT = prove
 (`!x y:N word. word_ult x y <=> val x < val y`,
  REWRITE_TAC[word_ult; relational2]);;

let WORD_ULE = prove
 (`!x y:N word. word_ule x y <=> val x <= val y`,
  REWRITE_TAC[word_ule; relational2]);;

let WORD_UGT = prove
 (`!x y:N word. word_ugt x y <=> val x > val y`,
  REWRITE_TAC[word_ugt; relational2]);;

let WORD_UGE = prove
 (`!x y:N word. word_uge x y <=> val x >= val y`,
  REWRITE_TAC[word_uge; relational2]);;

let WORD_ILT = prove
 (`!x y:N word. word_ilt x y <=> ival x < ival y`,
  REWRITE_TAC[word_ilt; irelational2]);;

let WORD_ILE = prove
 (`!x y:N word. word_ile x y <=> ival x <= ival y`,
  REWRITE_TAC[word_ile; irelational2]);;

let WORD_IGT = prove
 (`!x y:N word. word_igt x y <=> ival x > ival y`,
  REWRITE_TAC[word_igt; irelational2]);;

let WORD_IGE = prove
 (`!x y:N word. word_ige x y <=> ival x >= ival y`,
  REWRITE_TAC[word_ige; irelational2]);;

(* ------------------------------------------------------------------------- *)
(* Simple "propagate signed value modulo" decision procedure.                *)
(* ------------------------------------------------------------------------- *)

let WORD_RULE =
  let IVAL_WORD_ADD_REM = prove
   (`!x y:N word.
          ival(word_add x y) rem (&2 pow dimindex(:N)) =
          ((ival x rem (&2 pow dimindex(:N))) +
           (ival y rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_ADD_REM] THEN REWRITE_TAC[INT_REM_EQ; ICONG_WORD_ADD])
  and IVAL_WORD_SUB_REM = prove
   (`!x y:N word.
          ival(word_sub x y) rem (&2 pow dimindex(:N)) =
          ((ival x rem (&2 pow dimindex(:N))) -
           (ival y rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_SUB_REM] THEN REWRITE_TAC[INT_REM_EQ; ICONG_WORD_SUB])
  and IVAL_WORD_NEG_REM = prove
   (`!x:N word.
          ival(word_neg x) rem (&2 pow dimindex(:N)) =
          (--(ival x rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_NEG_REM] THEN REWRITE_TAC[INT_REM_EQ; ICONG_WORD_NEG])
  and IVAL_WORD_MUL_REM = prove
   (`!x y:N word.
          ival(word_mul x y) rem (&2 pow dimindex(:N)) =
          ((ival x rem (&2 pow dimindex(:N))) *
           (ival y rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_MUL_REM] THEN REWRITE_TAC[INT_REM_EQ; ICONG_WORD_MUL])
  and IVAL_IWORD_REM = prove
   (`!x. ival(iword x:N word) rem (&2 pow dimindex(:N)) =
         x rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_REM_EQ; IVAL_IWORD_CONG])
  and IVAL_WORD_REM = prove
   (`!n. ival(word n:N word) rem (&2 pow dimindex(:N)) =
         &n rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[WORD_IWORD; INT_REM_EQ; IVAL_IWORD_CONG])
  and IVAL_WORD_SHL_REM = prove
   (`!(x:N word) n.
      ival(word_shl x n) rem (&2 pow dimindex(:N)) =
      (&2 pow n * ival x rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N))`,
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ; ICONG_WORD_SHL])
  and INT_OF_NUM_REM = prove
   (`&(x + y) rem (&2 pow dimindex(:N)) =
     (&x rem (&2 pow dimindex(:N)) +
      &y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N)) /\
     &(x * y) rem (&2 pow dimindex(:N)) =
     (&x rem (&2 pow dimindex(:N)) *
      &y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[])
  and INT_OF_NUM_VAL_REM = prove
   (`!x:N word. &(val x) rem (&2 pow dimindex(:N)) =
                ival x rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG])
  and pth = prove
   (`!v w:N word.
          v = w <=>
          ival v rem (&2 pow dimindex(:N)) = ival w rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_REM_EQ; IVAL_CONG]) in
  let WORD_VAL_EQ_CONV =
    GEN_REWRITE_CONV I [pth] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_NOT_AS_SUB] THENC
    GEN_REWRITE_CONV (BINOP_CONV o TOP_DEPTH_CONV)
     [IVAL_WORD_NEG_REM; IVAL_WORD_ADD_REM; IVAL_WORD_SUB_REM;
      IVAL_WORD_MUL_REM; IVAL_IWORD_REM; IVAL_WORD_REM;
      IVAL_WORD_SHL_REM; INT_OF_NUM_REM; INT_OF_NUM_VAL_REM] THENC
    INT_REM_DOWN_CONV THENC
    GEN_REWRITE_CONV I [INT_REM_EQ] in
  fun tm ->
    let avs,bod = strip_forall tm in
    let th = ONCE_DEPTH_CONV WORD_VAL_EQ_CONV bod in
    GENL avs (EQT_ELIM(TRANS th (EQT_INTRO(NUMBER_RULE (rand(concl th))))));;

(* ------------------------------------------------------------------------- *)
(* A somewhat complementary purely bitwise decision procedure.               *)
(* ------------------------------------------------------------------------- *)

let WORD_BITWISE_TAC =
  let WORD_BITWISE_CONV =
    GEN_REWRITE_CONV I [WORD_EQ_BITS_ALT] THENC
    GEN_REWRITE_CONV (BINDER_CONV o RAND_CONV o BINOP_CONV o TOP_DEPTH_CONV)
     [BIT_WORD_NOT; BIT_WORD_AND; BIT_WORD_OR;
      BIT_WORD_XOR; BIT_WORD_OF_BITS; BIT_WORD_0;
      IN_INSERT; NOT_IN_EMPTY; IN_UNIV] in
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_BITWISE_CONV) THEN
  GEN_REWRITE_TAC DEPTH_CONV
   [MESON[] `(!i. i < dimindex(:N) ==> P i) /\
             (!i. i < dimindex(:N) ==> Q i) <=>
             (!i. i < dimindex(:N) ==> P i /\ Q i)`] THEN
  TRY(MATCH_MP_TAC(MESON[]
       `(!i. i < dimindex(:N) ==> P i ==> Q i)
        ==> (!i. i < dimindex(:N) ==> P i)
             ==> (!i. i < dimindex(:N) ==> Q i)`) ORELSE
      MATCH_MP_TAC(MESON[]
       `(!i. i < dimindex(:N) ==> (P i <=> Q i))
        ==> ((!i. i < dimindex(:N) ==> P i) <=>
             (!i. i < dimindex(:N) ==> Q i))`)) THEN
  TRY(GEN_TAC THEN DISCH_TAC) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC TAUT;;

let WORD_BITWISE_RULE tm = prove(tm,WORD_BITWISE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Slightly ad hoc but useful reduction to linear arithmetic.                *)
(* ------------------------------------------------------------------------- *)

let WORD_ARITH_TAC =
  let msb_pth = prove
   (`dimindex (:N) - 1 < dimindex(:N)`,
    REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `n - 1 < n <=> 1 <= n`])
  and wordy tm =
    match tm with Var(_,Tyapp("word",[_])) -> true | _ -> false in
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_USHR_MSB_EQ] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_NOT; BIT_WORD_XOR;
              BIT_WORD_INT_MIN; BIT_WORD_1; BIT_WORD_0; msb_pth] THEN
  REWRITE_TAC[MSB_INT_VAL; WORD_NOT_AS_SUB; WORD_RULE
   `word_shl (x:N word) 1 = word_add x x`] THEN
  REWRITE_TAC[WORD_ULT; WORD_ULE; WORD_UGT; WORD_UGE;
              WORD_ILT; WORD_ILE; WORD_IGT; WORD_IGE] THEN
  REWRITE_TAC[irelational2; relational2; GSYM VAL_EQ; INT_IVAL] THEN
  REWRITE_TAC[INT_GT; INT_GE; GT; GE] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_EQ] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL;
              GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_VAL_WORD_NEG_CASES; INT_VAL_WORD_ADD_CASES;
              INT_VAL_WORD_INT_MIN;
              INT_VAL_WORD_SUB_CASES; INT_IVAL; VAL_WORD_0; VAL_WORD_1] THEN
  W(MAP_EVERY (MP_TAC o C ISPEC INT_VAL_BOUND) o find_terms wordy o snd) THEN
  REWRITE_TAC[CONJUNCT2 TWICE_MSB] THEN INT_ARITH_TAC;;

let WORD_ARITH tm = prove(tm,WORD_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Zero extension and sign extension (also works for shortening modulo).     *)
(* ------------------------------------------------------------------------- *)

let word_zx = new_definition
 `(word_zx:(M)word->(N)word) w = word(val w)`;;

let VAL_WORD_ZX_GEN = prove
 (`!x. val((word_zx:(M)word->(N)word) x) = val x MOD 2 EXP dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[word_zx; VAL_WORD]);;

let VAL_WORD_ZX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> val((word_zx:(M)word->(N)word) x) = val x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN] THEN
  MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:M)` THEN
  ASM_REWRITE_TAC[LE_EXP; VAL_BOUND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WORD_ZX_ZX = prove
 (`!w. dimindex(:M) <= dimindex(:N)
       ==> (word_zx:N word->M word) ((word_zx:M word->N word) x) = x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> MIN n m = m`] THEN
  REWRITE_TAC[VAL_MOD_REFL]);;

let WORD_ZX_0 = prove
 (`(word_zx:M word->N word) (word 0) = word 0`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_0; MOD_0]);;

let WORD_ZX_TRIVIAL = prove
 (`!x:N word. word_zx x = x`,
  SIMP_TAC[GSYM VAL_EQ; VAL_WORD_ZX; LE_REFL]);;

let WORD_ZX_WORD = prove
 (`!n. (word_zx:M word->N word) (word n) = word (n MOD 2 EXP dimindex(:M))`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_ZX_GEN]);;

let WORD_ZX_1 = prove
 (`(word_zx:M word->N word) (word 1) = word 1`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_1; MOD_EQ_SELF] THEN
  DISJ2_TAC THEN REWRITE_TAC[ARITH_RULE `1 < n <=> 2 EXP 1 <= n`] THEN
  REWRITE_TAC[LE_EXP; DIMINDEX_GE_1; DIMINDEX_NONZERO] THEN ARITH_TAC);;

let word_sx = new_definition
 `(word_sx:(M)word->(N)word) w = iword(ival w)`;;

let IVAL_WORD_SX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> ival((word_sx:(M)word->(N)word) x) = ival x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IVAL_IWORD; word_sx] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  MP_TAC(ISPEC `x:M word` IVAL_BOUND) THEN
  MATCH_MP_TAC(INT_ARITH
   `m:int <= n ==> --m <= x /\ x < m ==> --n <= x /\ x < n`) THEN
  MATCH_MP_TAC INT_POW_MONO THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

let WORD_SX_SX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> (word_sx:N word->M word) ((word_sx:M word->N word) x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IVAL_EQ] THEN
  ONCE_REWRITE_TAC[word_sx] THEN ASM_SIMP_TAC[IVAL_WORD_SX; IWORD_IVAL]);;

let WORD_SX_0 = prove
 (`(word_sx:M word->N word) (word 0) = word 0`,
  REWRITE_TAC[GSYM IVAL_EQ; word_sx; IVAL_WORD_0; GSYM WORD_IWORD]);;

let WORD_SX_TRIVIAL = prove
 (`!x:N word. word_sx x = x`,
  SIMP_TAC[GSYM IVAL_EQ; IVAL_WORD_SX; LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Conditional AND and OR, with semantics of C's "&&" and "||"               *)
(* ------------------------------------------------------------------------- *)

let word_cand = new_definition
 `(word_cand:N word->N word->N word) x y =
        if ~(x = word 0) /\ ~(y = word 0) then word 1 else word 0`;;

let word_cor = new_definition
 `(word_cor:N word->N word->N word) x y =
        if ~(x = word 0) \/ ~(y = word 0) then word 1 else word 0`;;

let WORD_CAND = prove
 (`!x y:N word.
        word_cand x y = if x = word 0 \/ y = word 0 then word 0 else word 1`,
  REWRITE_TAC[word_cand] THEN MESON_TAC[]);;

let WORD_COR = prove
 (`!x y:N word.
        word_cor x y = if x = word 0 /\ y = word 0 then word 0 else word 1`,
  REWRITE_TAC[word_cor] THEN MESON_TAC[]);;

let WORD_CAND_NE_0 = prove
 (`!x y:N word.
        ~(word_cand x y = word 0) <=> ~(x = word 0) /\ ~(y = word 0)`,
  REWRITE_TAC[word_cand] THEN MESON_TAC[WORD_NE_10]);;

let WORD_COR_NE_0 = prove
 (`!x y:N word.
        ~(word_cor x y = word 0) <=> ~(x = word 0) \/ ~(y = word 0)`,
  REWRITE_TAC[word_cor] THEN MESON_TAC[WORD_NE_10]);;

let WORD_CAND_EQ_0 = prove
 (`!x y:N word.
        word_cand x y = word 0 <=> x = word 0 \/ y = word 0`,
  REWRITE_TAC[word_cand] THEN MESON_TAC[WORD_NE_10]);;

let WORD_COR_EQ_0 = prove
 (`!x y:N word.
        word_cor x y = word 0 <=> x = word 0 /\ y = word 0`,
  REWRITE_TAC[word_cor] THEN MESON_TAC[WORD_NE_10]);;

let VAL_WORD_CAND = prove
 (`!x y:N word.
        val(word_cand x y) =
        if ~(val x = 0) /\ ~(val y = 0) then 1 else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cand; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; VAL_WORD_1]);;

let VAL_WORD_COR = prove
 (`!x y:N word.
        val(word_cor x y) =
        if ~(val x = 0) \/ ~(val y = 0) then 1 else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cor; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; VAL_WORD_1]);;

let BIT_WORD_CAND = prove
 (`!i x y:N word.
        bit i (word_cand x y) <=> i = 0 /\ ~(x = word 0) /\ ~(y = word 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cand] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD_0; BIT_WORD_1]);;

let BIT_WORD_COR = prove
 (`!i x y:N word.
        bit i (word_cor x y) <=> i = 0 /\ (~(x = word 0) \/ ~(y = word 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cor] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD_0; BIT_WORD_1]);;

(* ------------------------------------------------------------------------- *)
(* Joining, in a somewhat (over?) general sense; v is the high part, w low.  *)
(* ------------------------------------------------------------------------- *)

let word_join = new_definition
 `(word_join:(M)word->(N)word->(P)word) v w =
        word(2 EXP dimindex(:N) * val v + val w)`;;

let VAL_WORD_JOIN = prove
 (`!v w. val((word_join:(M)word->(N)word->(P)word) v w) =
         (2 EXP dimindex(:N) * val v + val w) MOD 2 EXP dimindex(:P)`,
  REWRITE_TAC[word_join; VAL_WORD]);;

let BIT_WORD_JOIN = prove
 (`!v w i.
        bit i ((word_join:(M)word->(N)word->(P)word) v w) <=>
        i < dimindex(:P) /\
        (if i < dimindex(:N) then bit i w else bit (i - dimindex(:N)) v)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i < dimindex(:P)` THEN
  ASM_SIMP_TAC[BIT_TRIVIAL; GSYM NOT_LT] THEN
  REWRITE_TAC[word_join; BIT_WORD] THEN ASM_REWRITE_TAC[BIT_VAL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [REWRITE_TAC[ODD_MOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[DIV_MOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `d divides e ==> (e * v + w:num == w) (mod d)`) THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    UNDISCH_TAC `i < dimindex(:N)` THEN
    SIMP_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[ARITH_RULE `i + SUC d = SUC i + d`] THEN
    REWRITE_TAC[EXP_ADD; NUMBER_RULE `(a:num) divides a * b`];
    AP_TERM_TAC THEN
    SUBGOAL_THEN `2 EXP i = 2 EXP (dimindex(:N) + i - dimindex(:N))`
    SUBST1_TAC THENL [AP_TERM_TAC THEN ASM_ARITH_TAC; SIMP_TAC[EXP_ADD]] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]]);;

let VAL_WORD_JOIN_SIMPLE = prove
 (`!v w.
        dimindex(:M) + dimindex(:N) = dimindex(:P)
        ==> val((word_join:(M)word->(N)word->(P)word) v w) =
            2 EXP dimindex(:N) * val v + val w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_JOIN] THEN
  MATCH_MP_TAC MOD_LT THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  TRANS_TAC LTE_TRANS
   `2 EXP dimindex(:N) * (2 EXP dimindex(:M) - 1) + 2 EXP dimindex(:N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LET_ADD2 THEN REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN
    DISJ2_TAC THEN MATCH_MP_TAC(ARITH_RULE `a < b ==> a <= b - 1`) THEN
    REWRITE_TAC[VAL_BOUND];
    REWRITE_TAC[LEFT_SUB_DISTRIB; EXP_ADD] THEN MATCH_MP_TAC(ARITH_RULE
     `n * 1 <= n * m ==> n * m - n * 1 + n <= m * n`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Subwords, where the (pos,len) argument is (lsb_position,length)           *)
(* ------------------------------------------------------------------------- *)

let word_subword = new_definition
 `word_subword (w:M word) (pos,len):N word =
        word((val w DIV (2 EXP pos)) MOD (2 EXP len))`;;

let VAL_WORD_SUBWORD = prove
 (`!pos len w:M word.
        val(word_subword w (pos,len):N word) =
        (val w DIV (2 EXP pos)) MOD (2 EXP (MIN len (dimindex(:N))))`,
  REWRITE_TAC[word_subword; VAL_WORD; MOD_MOD_EXP_MIN]);;

let BIT_WORD_SUBWORD = prove
 (`!pos len (w:M word) i.
        bit i (word_subword w (pos,len):N word) <=>
        i < MIN len (dimindex(:N)) /\ bit (pos + i) w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `m < MIN p q <=> m < p /\ m < q`] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN
  ASM_SIMP_TAC[GSYM NOT_LT; BIT_TRIVIAL] THEN
  ASM_REWRITE_TAC[word_subword; BIT_WORD] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; BIT_VAL; DIV_DIV] THEN
  ASM_CASES_TAC `i:num < len` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `i:num < len` THEN
    SIMP_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:num` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ADD_ASSOC] THEN
    SPEC_TAC(`pos + i:num`,`j:num`) THEN REWRITE_TAC[EXP_ADD] THEN
    REWRITE_TAC[GSYM DIV_MOD; ODD_MOD_POW2; NOT_SUC];
    MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP (pos + len)` THEN
    SIMP_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN
    ASM_ARITH_TAC]);;

let WORD_SUBWORD_0 = prove
 (`!pos len. word_subword (word 0) (pos,len) = word 0`,
  REWRITE_TAC[word_subword; VAL_WORD_0; DIV_0; MOD_0]);;

let WORD_SUBWORD_JOIN_SELF = prove
 (`!(w:N word) k.
        k <= dimindex(:N)
        ==> word_subword (word_join w w:(N tybit0)word) (k,dimindex(:N)) =
            word_ror w k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_ROR;
              DIMINDEX_TYBIT0; ARITH_RULE `MIN n n = n`] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC o MATCH_MP (ARITH_RULE
   `k:num <= n ==> k = n \/ k < n`)) THEN
  ASM_SIMP_TAC[MOD_REFL; MOD_LT; ADD_CLAUSES;
               ARITH_RULE `(n + i) - n:num = i`;
               ARITH_RULE `~(n + i:num < n)`;
               ARITH_RULE `i < n ==> n + i < 2 * n`] THEN
  REWRITE_TAC[ADD_SYM; TAUT `(p /\ q <=> q) <=> q ==> p`] THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bit recursion equations for "linear" operations.                          *)
(* ------------------------------------------------------------------------- *)

let BIT_WORD_ADD = prove
 (`!x (y:N word) i.
        bit i (word_add x y) <=>
        i < dimindex(:N) /\
        ((bit i x <=> bit i y) <=>
         ~(i = 0) /\
         (bit (i - 1) x /\ bit (i - 1) y \/
          (bit (i - 1) x \/ bit (i - 1) y) /\
          ~(bit (i - 1) (word_add x y))))`,
  let lemma = prove
   (`2 EXP i <= (2 EXP i * b + x) MOD 2 EXP (i + 1) <=>
     (EVEN b <=> 2 EXP i <= x MOD (2 EXP (i + 1)))`,
    SIMP_TAC[EXP_ADD; EXP_1; MOD_MULT_MOD; EXP_EQ_0; ARITH_EQ;
             DIV_MULT_ADD; MOD_MULT_ADD] THEN
    REWRITE_TAC[MOD_2_CASES; EVEN_ADD] THEN
    MAP_EVERY ASM_CASES_TAC [`EVEN b`; `EVEN(x DIV 2 EXP i)`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; LE_ADD; NOT_LE] THEN
    SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `i < dimindex(:N)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[NOT_LT; BIT_TRIVIAL]] THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_VAL_MOD] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [BIT_VAL_MOD] THEN
  ASM_REWRITE_TAC[VAL_WORD_ADD; MOD_MOD_EXP_MIN] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [TAUT `~p /\ q <=> ~(~p ==> ~q)`] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; ARITH_RULE
    `~(k = 0) /\ k < n ==> MIN n (k - 1 + 1) = k`] THEN
  ASM_SIMP_TAC[NOT_IMP; ARITH_RULE `k < n ==> MIN n (k + 1) = k + 1`] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[VAL_MOD_STEP; lemma; ARITH_RULE
   `(k * b + x) + (k * c + y):num = k * (b + c) + x + y`] THEN
  BINOP_TAC THENL
   [MAP_EVERY ASM_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    SIMP_TAC[EXP_ADD; EXP_1; MOD_LT; DIVISION; EXP_EQ_0; ARITH_EQ;
             ARITH_RULE `x < n /\ y < n ==> x + y < n * 2`]] THEN
  ASM_CASES_TAC `i = 0` THEN
  ASM_SIMP_TAC[EXP; MOD_1; ADD_CLAUSES; CONJUNCT1 LE;
               EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[MOD_ADD_CASES; DIVISION; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[GSYM NOT_LE] THEN
  MAP_EVERY ABBREV_TAC
   [`m = val(x:N word) MOD 2 EXP i`; `n = val(y:N word) MOD 2 EXP i`] THEN
  SUBGOAL_THEN `m < 2 EXP i /\ n < 2 EXP i` MP_TAC THENL
   [ASM_MESON_TAC[DIVISION; EXP_EQ_0; ARITH_RULE `~(2 = 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP i = 2 * 2 EXP(i - 1)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM(CONJUNCT2 EXP); ADD1; SUB_ADD; LE_1];
    ABBREV_TAC `j = i - 1` THEN
    REWRITE_TAC[COND_SWAP; NOT_LE] THEN ASM_ARITH_TAC]);;

let BIT_WORD_SUB = prove
 (`!x (y:N word) i.
        bit i (word_sub x y) <=>
        i < dimindex(:N) /\
        ((bit i x <=> bit i y) <=>
         ~(i = 0) /\
         (~bit (i - 1) x /\ bit (i - 1) y \/
          (~bit (i - 1) x \/ bit (i - 1) y) /\
          bit (i - 1) (word_sub x y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_RULE
   `word_sub x y:N word = word_not(word_add (word_not x) y)`] THEN
  REWRITE_TAC[BIT_WORD_NOT] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [BIT_WORD_ADD] THEN
  ASM_SIMP_TAC[BIT_WORD_NOT; ARITH_RULE `i < n ==> i - 1 < n`] THEN
  REWRITE_TAC[TAUT `~((~p <=> q) <=> r) <=> ((p <=> q) <=> r)`]);;

let BIT_WORD_NEG = prove
 (`!(x:N word) i.
        bit i (word_neg x) <=>
        i < dimindex(:N) /\
        (bit i x <=> i = 0 \/ ~bit (i - 1) x /\ ~bit (i - 1) (word_neg x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_RULE `word_neg x:N word = word_sub (word 0) x`] THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_SUB] THEN
  REWRITE_TAC[BIT_WORD_0] THEN CONV_TAC TAUT);;

let BIT_WORD_ADD_CLAUSES = prove
 (`(!x (y:N word).
        bit 0 (word_add x y) <=> ~(bit 0 x <=> bit 0 y)) /\
   (!x (y:N word) i.
        bit (i + 1) (word_add x y) <=>
        i + 1 < dimindex(:N) /\
        ((bit (i + 1) x <=> bit (i + 1) y) <=>
         (bit i x /\ bit i y \/
          (bit i x \/ bit i y) /\ ~(bit i (word_add x y)))))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_ADD] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1; ADD_SUB; ADD_EQ_0; ARITH_EQ]);;

let BIT_WORD_SUB_CLAUSES = prove
 (`(!x (y:N word).
        bit 0 (word_sub x y) <=> ~(bit 0 x <=> bit 0 y)) /\
   (!x (y:N word) i.
        bit (i + 1) (word_sub x y) <=>
        i + 1 < dimindex(:N) /\
        ((bit (i + 1) x <=> bit (i + 1) y) <=>
         (~bit i x /\ bit i y \/
          (~bit i x \/ bit i y) /\ bit i (word_sub x y))))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_SUB] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1; ADD_SUB; ADD_EQ_0; ARITH_EQ]);;

let BIT_WORD_NEG_CLAUSES = prove
 (`(!(x:N word).
        bit 0 (word_neg x) = bit 0 x) /\
   (!(x:N word) i.
        bit (i + 1) (word_neg x) <=>
        i + 1 < dimindex(:N) /\
        (bit (i + 1) x <=> ~bit i x /\ ~bit i (word_neg x)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_NEG] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1; ADD_SUB; ADD_EQ_0; ARITH_EQ]);;

let LE_VAL_MOD_STEP = prove
 (`!(x:N word) (y:N word) i.
        (val x MOD 2 EXP (i + 1)) <= (val y MOD 2 EXP (i + 1)) <=>
        ~bit i x /\ bit i y \/
        (bit i x <=> bit i y) /\ val x MOD 2 EXP i <= val y MOD 2 EXP i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_MOD_STEP] THEN
  MAP_EVERY BOOL_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[LE_ADD_LCANCEL; NOT_LE] THEN TRY(MATCH_MP_TAC LT_IMP_LE) THEN
  MATCH_MP_TAC(ARITH_RULE `x:num < y ==> x < y + z`) THEN
  SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]);;

let LT_VAL_MOD_STEP = prove
 (`!(x:N word) (y:N word) i.
        (val x MOD 2 EXP (i + 1)) < (val y MOD 2 EXP (i + 1)) <=>
        ~bit i x /\ bit i y \/
        (bit i x <=> bit i y) /\ val x MOD 2 EXP i < val y MOD 2 EXP i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_MOD_STEP] THEN
  MAP_EVERY BOOL_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[LT_ADD_LCANCEL; NOT_LT] THEN TRY(MATCH_MP_TAC LT_IMP_LE) THEN
  MATCH_MP_TAC(ARITH_RULE `x:num < y ==> x < y + z`) THEN
  SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Miscellaneous lemmas we don't want to keep regenerating. Many of them in  *)
(* any case need a little bit of manual effort.                              *)
(* ------------------------------------------------------------------------- *)

let WORD_ADD_0 = prove
 (`(!x:N word. word_add x (word 0) = x) /\
   (!x:N word. word_add (word 0) x = x)`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_SYM = prove
 (`!x y:N word. word_add x y = word_add y x`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_ASSOC = prove
 (`!x y z:N word. word_add x (word_add y z) =
                  word_add (word_add x y) z`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_AC = prove
 (`word_add x y = word_add y x /\
   word_add (word_add x y) z = word_add x (word_add y z) /\
   word_add x (word_add y z) = word_add y (word_add x z)`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_0 = prove
 (`(!x:N word. word_mul x (word 0) = word 0) /\
   (!x:N word. word_mul (word 0) x = word 0)`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_SYM = prove
 (`!x y:N word. word_mul x y = word_mul y x`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_ASSOC = prove
 (`!x y z:N word. word_mul x (word_mul y z) =
                  word_mul (word_mul x y) z`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_AC = prove
 (`word_mul x y = word_mul y x /\
   word_mul (word_mul x y) z = word_mul x (word_mul y z) /\
   word_mul x (word_mul y z) = word_mul y (word_mul x z)`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_0 = prove
 (`!x:N word. word_sub x (word 0) = x`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_LZERO = prove
 (`!x:N word. word_sub (word 0) x = word_neg x`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_EQ_0 = prove
 (`!x y:N word. word_sub x y = word 0 <=> x = y`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_REFL = prove
 (`!x:N word. word_sub x x = word 0`,
  CONV_TAC WORD_RULE);;

let WORD_NEG_NEG = prove
 (`!x:N word. word_neg(word_neg x) = x`,
  CONV_TAC WORD_RULE);;

let WORD_NEG_0 = prove
 (`word_neg (word 0) = word 0`,
  CONV_TAC WORD_RULE);;

let WORD_NEG_EQ_0 = prove
 (`!x:N word. word_neg x = word 0 <=> x = word 0`,
  CONV_TAC WORD_RULE);;

let WORD_AND_REFL = prove
 (`!x:N word. word_and x x = x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_0 = prove
 (`(!x:N word. word_and x (word 0) = word 0) /\
   (!x:N word. word_and (word 0) x = word 0)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_NOT0 = prove
 (`(!x:N word. word_and x (word_not(word 0)) = x) /\
   (!x:N word. word_and (word_not(word 0)) x = x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_SYM = prove
 (`!x y:N word. word_and x y = word_and y x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_REFL = prove
 (`!x:N word. word_or x x = x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_0 = prove
 (`(!x:N word. word_or x (word 0) = x) /\
   (!x:N word. word_or (word 0) x = x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_NOT0 = prove
 (`(!x:N word. word_or x (word_not(word 0)) = word_not(word 0)) /\
   (!x:N word. word_or (word_not(word 0)) x = word_not(word 0))`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_SYM = prove
 (`!x y:N word. word_or x y = word_or y x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_EQ_0 = prove
 (`!x y:N word. word_or x y = word 0 <=> x = word 0 /\ y = word 0`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_EQ_0 = prove
 (`!x y:N word. word_xor x y = word 0 <=> x = y`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_0 = prove
 (`(!x:N word. word_xor x (word 0) = x) /\
   (!x:N word. word_xor (word 0) x = x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_NOT0 = prove
 (`(!x:N word. word_xor x (word_not(word 0)) = word_not x) /\
   (!x:N word. word_xor (word_not(word 0)) x = word_not x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_REFL = prove
 (`!x:N word. word_xor x x = word 0`,
  REWRITE_TAC[WORD_XOR_EQ_0]);;

let WORD_XOR_SYM = prove
 (`!x y:N word. word_xor x y = word_xor y x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_1 = prove
 (`(!x:N word. word_and x (word 1) = if bit 0 x then word 1 else word 0) /\
   (!x:N word. word_and (word 1) x = if bit 0 x then word 1 else word 0)`,
  REWRITE_TAC[WORD_BITWISE_RULE
   `word_and (word 1:N word) x = word_and x (word 1)`] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_1; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THEN
  ASM_REWRITE_TAC[BIT_WORD_0] THEN SIMP_TAC[DIMINDEX_GE_1; LE_1]);;

let WORD_NOT_NEG = prove
 (`!x:N word. word_not(word_neg x) = word_sub x (word 1)`,
  GEN_TAC THEN REWRITE_TAC[WORD_NOT_AS_SUB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let WORD_NOT_SUB = prove
 (`!x y:N word.
        word_not(word_sub x y) = word_add (word_not x) y`,
  REWRITE_TAC[WORD_NOT_AS_SUB] THEN CONV_TAC WORD_RULE);;

let WORD_NOT_ADD = prove
 (`!x y:N word.
        word_not(word_add x y) = word_add (word_not x) (word_neg y)`,
  REWRITE_TAC[WORD_NOT_AS_SUB] THEN CONV_TAC WORD_RULE);;

let WORD_SHL_AND = prove
 (`!(v:N word) w n.
        word_shl (word_and v w) n =
        word_and (word_shl v n) (word_shl w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_SHL; BIT_WORD_AND] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `bit (i - n) (v:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i - n) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let WORD_USHR_AND = prove
 (`!(v:N word) w n.
        word_ushr (word_and v w) n =
        word_and (word_ushr v n) (word_ushr w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_USHR; BIT_WORD_AND] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i + n < dimindex(:N)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_SHL_OR = prove
 (`!(v:N word) w n.
        word_shl (word_or v w) n =
        word_or (word_shl v n) (word_shl w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_SHL; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `bit (i - n) (v:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i - n) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let WORD_USHR_OR = prove
 (`!(v:N word) w n.
        word_ushr (word_or v w) n =
        word_or (word_ushr v n) (word_ushr w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_USHR; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i + n < dimindex(:N)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_SHL_XOR = prove
 (`!(v:N word) w n.
        word_shl (word_xor v w) n =
        word_xor (word_shl v n) (word_shl w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_SHL; BIT_WORD_XOR] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `bit (i - n) (v:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i - n) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let WORD_USHR_XOR = prove
 (`!(v:N word) w n.
        word_ushr (word_xor v w) n =
        word_xor (word_ushr v n) (word_ushr w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_USHR; BIT_WORD_XOR] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i + n < dimindex(:N)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_ADD_XOR_GEN = prove
 (`!x y:N word.
        word_add x y = word_add (word_shl (word_and x y) 1) (word_xor x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_ADD; VAL_WORD_SHL] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXP_1; VAL_WORD_ADD_AND_XOR]);;

let WORD_ADD_OR_GEN = prove
 (`!x y:N word. word_add x y = word_add (word_and x y) (word_or x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_ADD; VAL_WORD_SHL] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_WORD_ADD_AND_OR]);;

let WORD_OR_XOR_GEN = prove
 (`!x y:N word. word_or x y = word_add (word_and x y) (word_xor x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_ADD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[VAL_WORD_OR_AND_XOR]);;

let WORD_ADD_XOR = prove
 (`!x y:N word. word_and x y = word 0 ==> word_add x y = word_xor x y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_ADD_XOR_GEN] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

let WORD_OR_XOR = prove
 (`!x y:N word. word_and x y = word 0 ==> word_or x y = word_xor x y`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[WORD_OR_XOR_GEN] THEN CONV_TAC WORD_RULE);;

let WORD_ADD_OR = prove
 (`!x y:N word. word_and x y = word 0 ==> word_add x y = word_or x y`,
  SIMP_TAC[WORD_OR_XOR; WORD_ADD_XOR]);;

let WORD_XOR_INT_MIN = prove
 (`!w:N word. word_xor word_INT_MIN w = word_add word_INT_MIN w`,
  GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ADD_XOR_GEN] THEN
  REWRITE_TAC[WORD_RULE `w:N word = word_add x w <=> x = word 0`] THEN
  REWRITE_TAC[WORD_SHL_AND] THEN
  MATCH_MP_TAC(WORD_BITWISE_RULE `x = word 0 ==> word_and x y = word 0`) THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_0; BIT_WORD_SHL; BIT_WORD_INT_MIN] THEN
  ARITH_TAC);;

let WORD_BITVAL_NOT = prove
 (`!b. word(bitval(~b)) = word_sub (word 1) (word(bitval b))`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_RULE);;

let IVAL_WORD_NOT = prove
 (`!x:N word. ival(word_not x) = --(ival x + &1)`,
  REWRITE_TAC[IVAL_IWORD_GALOIS] THEN
  REWRITE_TAC[INT_ARITH `--x:int <= --(y + &1) <=> y < x`] THEN
  REWRITE_TAC[INT_ARITH `--(x + &1):int < y <=> --y <= x`] THEN
  REWRITE_TAC[IVAL_BOUND] THEN
  REWRITE_TAC[IWORD_INT_NEG; IWORD_INT_ADD; IWORD_IVAL; GSYM WORD_IWORD] THEN
  CONV_TAC WORD_RULE);;

let [BIT_WORD_NEG_CASES; BIT_WORD_ADD_1_CASES; BIT_WORD_SUB_1_CASES] =
  (CONJUNCTS o prove)
 (`(!(x:N word) i.
        bit i (word_neg x) <=>
        i < dimindex(:N) /\
        (if ?j. j < i /\ bit j x then ~(bit i x) else bit i x)) /\
   (!(x:N word) i.
        bit i (word_add x (word 1)) <=>
        i < dimindex(:N) /\
        (if ?j. j < i /\ ~(bit j x) then bit i x else ~(bit i x))) /\
   (!(x:N word) i.
        bit i (word_sub x (word 1)) <=>
        i < dimindex(:N) /\
        (if ?j. j < i /\ bit j x then bit i x else ~(bit i x)))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[LT; BIT_WORD_NEG_CLAUSES; BIT_WORD_ADD_CLAUSES;
              BIT_WORD_SUB_CLAUSES; ADD1; BIT_WORD_1] THEN
  SIMP_TAC[ADD_EQ_0; LE_1; DIMINDEX_GE_1; ARITH_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `i + 1 < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  (ASM_CASES_TAC `i = 0` THEN ASM_SIMP_TAC[LT; LE_1; DIMINDEX_GE_1] THENL
   [CONV_TAC TAUT; ALL_TAC]) THEN
  ASM_CASES_TAC `bit i (x:N word)` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i + 1) (x:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* An idiom for describing a mask duplicating a bit throughout a word.       *)
(* ------------------------------------------------------------------------- *)

let WORD_MASK_ALT = prove
 (`!p. word_neg(word(bitval p)) = if p then word_neg(word 1) else word 0`,
  MATCH_MP_TAC bool_INDUCT THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0]);;

let WORD_MASK = prove
 (`!p. word_neg(word(bitval p)) = if p then word_not(word 0) else word 0`,
  REWRITE_TAC[WORD_MASK_ALT; WORD_NEG_1]);;

let BIT_WORD_MASK = prove
 (`!p i. bit i (word_neg(word(bitval p)):N word) <=> i < dimindex(:N) /\ p`,
  MATCH_MP_TAC bool_INDUCT THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; BIT_WORD_0] THEN
  REWRITE_TAC[WORD_NEG_1; BIT_WORD_NOT; BIT_WORD_0]);;

let WORD_NOT_MASK = prove
 (`!p. word_not(word_neg(word(bitval p))) = word_neg(word(bitval(~p)))`,
  MATCH_MP_TAC bool_INDUCT THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_RULE);;

let WORD_AND_MASK = prove
 (`(!p x. word_and (word_neg(word(bitval p))) x =
          if p then x else word 0) /\
   (!p x. word_and x (word_neg(word(bitval p))) =
          if p then x else word 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_MASK = prove
 (`(!p x. word_or (word_neg(word(bitval p))) x =
          if p then word_neg(word(bitval p)) else x) /\
   (!p x. word_or x (word_neg(word(bitval p))) =
          if p then word_neg(word(bitval p)) else x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_MASK = prove
 (`(!p x. word_xor (word_neg(word(bitval p))) x =
          if p then word_not x else x) /\
   (!p x. word_xor x (word_neg(word(bitval p))) =
          if p then word_not x else x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_MASKS = prove
 (`!p q. word_and (word_neg(word(bitval p))) (word_neg(word(bitval q))) =
         word_neg(word(bitval(p /\ q)))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_AND_0; WORD_AND_REFL]);;

let WORD_OR_MASKS = prove
 (`!p q. word_or (word_neg(word(bitval p))) (word_neg(word(bitval q))) =
         word_neg(word(bitval(p \/ q)))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_OR_0; WORD_OR_REFL]);;

let WORD_XOR_MASKS = prove
 (`!p q. word_xor (word_neg(word(bitval p))) (word_neg(word(bitval q))) =
         word_neg(word(bitval(~(p <=> q))))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_XOR_0; WORD_XOR_REFL]);;

let WORD_AND_CONDITIONS = prove
 (`!p q. word_and (word(bitval p)) (word(bitval q)) =
         word(bitval(p /\ q))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_AND_0; WORD_AND_REFL]);;

let WORD_OR_CONDITIONS = prove
 (`!p q. word_or (word(bitval p)) (word(bitval q)) =
         word(bitval(p \/ q))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_OR_0; WORD_OR_REFL]);;

let WORD_XOR_CONDITIONS = prove
 (`!p q. word_xor (word(bitval p)) (word(bitval q)) =
         word(bitval(~(p <=> q)))`,
  REPEAT(MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_XOR_0; WORD_XOR_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Some lemmas about masks 000..001111..1111 and their values.               *)
(* ------------------------------------------------------------------------- *)

let VAL_WORD_AND_MASK = prove
 (`!(x:N word) k.
        val(word_and x (word_of_bits {i | i < k})) = val x MOD (2 EXP k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[val_def] THEN
  SIMP_TAC[BINARY_DIGITSUM_MOD; FINITE_NUMSEG_LT; NSUM_RESTRICT_SET] THEN
  MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; BIT_WORD_AND; IN_ELIM_THM; BIT_WORD_OF_BITS] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bitval] THEN ARITH_TAC);;

let IVAL_WORD_AND_MASK = prove
 (`!(x:N word) k.
        k < dimindex(:N)
        ==> ival(word_and x (word_of_bits {i | i < k})) =
            ival x rem (&2 pow k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INT_REM_IVAL; LT_IMP_LE] THEN
  REWRITE_TAC[GSYM VAL_WORD_AND_MASK; ival] THEN
  MATCH_MP_TAC(MESON[] `p ==> (if p then x else y) = x`) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK] THEN TRANS_TAC LTE_TRANS `2 EXP k` THEN
  SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC);;

let VAL_WORD_AND_MASK_WORD = prove
 (`!x k. val(word_and x (word(2 EXP k - 1))) = val x MOD 2 EXP k`,
  REWRITE_TAC[GSYM WORD_OF_BITS_MASK; VAL_WORD_AND_MASK]);;

let WORD_BITMASK = prove
 (`!k. word_of_bits {i | i < k}:N word =
       word_sub (word_of_bits {k}) (word 1)`,
  REWRITE_TAC[WORD_OF_BITS_MASK; WORD_OF_BITS_SING_AS_WORD] THEN
  REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* JVM-specific word operations, though they may well work in other places.  *)
(*                                                                           *)
(* All shift operations mask out the lower bits as the unsigned shift count. *)
(*                                                                           *)
(* Division does truncation towards zero; at this level there is no concept  *)
(* of an exception on division by zero. Note that the JVM is defined anyway  *)
(* so INT_MIN / -1 doesn't generate any exception, just returning the        *)
(* correct modular result as per the usual pattern.                          *)
(*                                                                           *)
(* Remainder is then defined by the usual Euclidean identity.                *)
(* ------------------------------------------------------------------------- *)

let word_jshl = new_definition
 `word_jshl (x:N word) (y:N word) =
        word_shl x (val y MOD dimindex(:N))`;;

let word_jshr = new_definition
 `word_jshr (x:N word) (y:N word) =
        word_ishr x (val y MOD dimindex(:N))`;;

let word_jushr = new_definition
 `word_jushr (x:N word) (y:N word) =
        word_ushr x (val y MOD dimindex(:N))`;;

let word_jdiv = new_definition
 `word_jdiv:N word->N word->N word =
   imodular (\a b. int_sgn a * int_sgn b * (abs(a) div abs(b)))`;;

let word_jrem = new_definition
 `word_jrem (x:N word) (y:N word) =
    word_sub x (word_mul (word_jdiv x y) y)`;;

(* ------------------------------------------------------------------------- *)
(* The JVM doesn't include rotates as primitive, but here is what they       *)
(* obviously would be like, and proof that some emulations work. Note that   *)
(* emulation using negative shifts relies not only on the Java               *)
(* masking treatment of shift counts but also on the word size being a       *)
(* power of 2 (of course for the JVM it is 2^5 = 32 or 2^6 = 64).            *)
(* ------------------------------------------------------------------------- *)

let word_jror = new_definition
 `word_jror (w:N word) (k:N word) = word_ror w (val k)`;;

let word_jrol = new_definition
 `word_jrol (w:N word) (k:N word) = word_rol w (val k)`;;

let VAL_WORD_NEG_MOD_DIMINDEX = prove
 (`!k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> (val(word_neg k) == dimindex (:N) - val k MOD dimindex(:N))
            (mod dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_NEG; CONG] THEN
  MATCH_MP_TAC(MESON[]
   `x MOD n MOD m = x MOD m /\ x MOD m = y ==> x MOD n MOD m = y`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[divides; MOD_MOD]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; VAL_BOUND; DIVISION;
           DIMINDEX_NONZERO; GSYM INT_OF_NUM_REM] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `n divides e /\ (k':int == k) (mod n) ==> (e - k == n - k') (mod n)`) THEN
  ASM_REWRITE_TAC[GSYM num_divides; INT_REM_MOD_SELF]);;

let WORD_JROL_JROR = prove
 (`!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jrol w k = word_jror w (word_neg k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jrol; word_jror] THEN
  REWRITE_TAC[WORD_ROL_ROR_GEN] THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
  ONCE_REWRITE_TAC[NUMBER_RULE
   `(x:num == y) (mod n) <=> (y == x) (mod n)`] THEN
  MATCH_MP_TAC VAL_WORD_NEG_MOD_DIMINDEX THEN ASM_REWRITE_TAC[]);;

let WORD_JROR_JROL = prove
 (`!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jror w k = word_jrol w (word_neg k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jrol; word_jror] THEN
  REWRITE_TAC[WORD_ROR_ROL_GEN] THEN MATCH_MP_TAC WORD_ROL_PERIODIC THEN
  ONCE_REWRITE_TAC[NUMBER_RULE
   `(x:num == y) (mod n) <=> (y == x) (mod n)`] THEN
  MATCH_MP_TAC VAL_WORD_NEG_MOD_DIMINDEX THEN ASM_REWRITE_TAC[]);;

let WORD_JROR = prove
 (`!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jror w k =
            word_or (word_jushr w k) (word_jshl w (word_neg k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jror; word_jushr; word_jshl] THEN
  ONCE_REWRITE_TAC[WORD_ROR_MOD] THEN
  SIMP_TAC[WORD_ROR_SHIFTS; DIVISION; DIMINDEX_NONZERO; LT_IMP_LE] THEN
  FIRST_X_ASSUM(MP_TAC o ISPEC `k:N word` o
    MATCH_MP VAL_WORD_NEG_MOD_DIMINDEX) THEN
  REWRITE_TAC[CONG] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `val(k:N word) MOD dimindex(:N) = 0` THENL
   [ASM_REWRITE_TAC[SUB_0; MOD_REFL; WORD_USHR_ZERO; WORD_SHL_ZERO] THEN
    MATCH_MP_TAC(WORD_BITWISE_RULE
     `y = word 0 ==> word_or x y = word_or x x`) THEN
    REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_SHL; MOD_MULT];
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[ARITH_RULE `n - k < n <=> ~(k = 0) /\ ~(n = 0)`] THEN
    ASM_REWRITE_TAC[DIMINDEX_NONZERO]]);;

let WORD_JROL = prove
 (`!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jrol w k =
            word_or (word_jshl w k) (word_jushr w (word_neg k))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_JROL_JROR; WORD_JROR] THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_neg(word_neg x):N word = x`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* Conversion for "j" forms applied to numeral shift/rotate word.            *)
(* ------------------------------------------------------------------------- *)

let WORD_WORD_OPERATION_CONV =
  let pth = prove
   (`word_jshl (x:N word) (word n) =
     word_shl x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jshr x (word n) =
     word_ishr x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jushr x (word n) =
     word_ushr x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jrol x (word n) =
     word_rol x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jror x (word n) =
     word_ror x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N))`,
    REWRITE_TAC[word_jshl; word_jshr; word_jushr; word_jrol; word_jror] THEN
    REWRITE_TAC[VAL_WORD; GSYM WORD_ROL_MOD; GSYM WORD_ROR_MOD]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV (RAND_CONV (!word_POW2SIZE_CONV) THENC NUM_MOD_CONV)
                (!word_SIZE_CONV) THENC
    NUM_MOD_CONV);;

(* ------------------------------------------------------------------------- *)
(* Emulation of unsigned comparisons using signed (useful for the JVM).      *)
(* ------------------------------------------------------------------------- *)

let IVAL_TOPFLIP_VAL = prove
 (`!w:N word.
        ival(word_xor word_INT_MIN w) =
        &(val w) - &2 pow (dimindex(:N) - 1)`,
  REWRITE_TAC[INT_IVAL; WORD_XOR_INT_MIN] THEN
  REWRITE_TAC[INT_VAL_WORD_ADD_CASES; INT_VAL_WORD_INT_MIN; MSB_INT_VAL] THEN
  WORD_ARITH_TAC);;

let WORD_ULE_TOPFLIP = prove
 (`!v w:N word.
        word_ule v w <=>
        word_ile (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)`,
  REWRITE_TAC[word_ule; word_ile; relational2; irelational2] THEN
  REWRITE_TAC[IVAL_TOPFLIP_VAL; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let WORD_ULT_TOPFLIP = prove
 (`!v w:N word.
        word_ult v w <=>
        word_ilt (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)`,
  REWRITE_TAC[word_ult; word_ilt; relational2; irelational2] THEN
  REWRITE_TAC[IVAL_TOPFLIP_VAL; GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let WORD_UGE_TOPFLIP = prove
 (`!v w:N word.
        word_uge v w <=>
        word_ige (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)`,
  REWRITE_TAC[word_uge; word_ige; relational2; irelational2] THEN
  REWRITE_TAC[IVAL_TOPFLIP_VAL; INT_GE; GE; GSYM INT_OF_NUM_LE] THEN
  INT_ARITH_TAC);;

let WORD_UGT_TOPFLIP = prove
 (`!v w:N word.
        word_ugt v w <=>
        word_igt (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)`,
  REWRITE_TAC[word_ugt; word_igt; relational2; irelational2] THEN
  REWRITE_TAC[IVAL_TOPFLIP_VAL; INT_GT; GT; GSYM INT_OF_NUM_LT] THEN
  INT_ARITH_TAC);;

let WORD_ILT_TOPFLIP = prove
 (`!v w:N word.
        word_ilt v w <=>
        word_ult (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)`,
  REWRITE_TAC[WORD_ULT_TOPFLIP] THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor m (word_xor m x) = x`]);;

let WORD_ILE_TOPFLIP = prove
 (`!v w:N word.
        word_ile v w <=>
        word_ule (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)`,
  REWRITE_TAC[WORD_ULE_TOPFLIP] THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor m (word_xor m x) = x`]);;

let WORD_IGT_TOPFLIP = prove
 (`!v w:N word.
        word_igt v w <=>
        word_ugt (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)`,
  REWRITE_TAC[WORD_UGT_TOPFLIP] THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor m (word_xor m x) = x`]);;

let WORD_IGE_TOPFLIP = prove
 (`!v w:N word.
        word_ige v w <=>
        word_uge (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)`,
  REWRITE_TAC[WORD_UGE_TOPFLIP] THEN
  REWRITE_TAC[WORD_BITWISE_RULE `word_xor m (word_xor m x) = x`]);;

(* ------------------------------------------------------------------------- *)
(* Conversion for explicit numeric bits of word operations, one level.       *)
(* For example BIT_WORD_CONV `bit 7 (word_sub x y:int16)`                    *)
(* ------------------------------------------------------------------------- *)

let BIT_WORD_CONV =
  let pth_ror = prove
   (`bit i (word_ror (w:N word) n) <=>
          (\m. (\s. if s < dimindex(:N) then bit s w
                    else i < dimindex(:N) /\ bit (s - dimindex(:N)) w)
               (i + m))
          (n MOD dimindex(:N))`,
    REWRITE_TAC[BIT_WORD_ROR])
  and pth_rol = prove
   (`bit i (word_rol (w:N word) n) <=>
          (\m. if i < m then bit (i + dimindex(:N) - m) w
               else i < dimindex(:N) /\ bit (i - m) w)
          (n MOD dimindex(:N))`,
    REWRITE_TAC[BIT_WORD_ROL]) in
  let rule_add = (MATCH_MP o prove)
   (`n = SUC m
     ==> (bit n (word_add x y:N word) <=>
          n < dimindex(:N) /\
          ((bit n x <=> bit n y) <=>
           bit m x /\ bit m y \/
           (bit m x \/ bit m y) /\ ~bit m (word_add x y)))`,
    SIMP_TAC[REWRITE_RULE[GSYM ADD1] BIT_WORD_ADD_CLAUSES])
  and rule_sub = (MATCH_MP o prove)
   (`n = SUC m
     ==> (bit n (word_sub x y:N word) <=>
          n < dimindex(:N) /\
          ((bit n x <=> bit n y) <=>
           ~bit m x /\ bit m y \/
           (~bit m x \/ bit m y) /\ bit m (word_sub x y)))`,
    SIMP_TAC[REWRITE_RULE[GSYM ADD1] BIT_WORD_SUB_CLAUSES])
  and rule_neg = (MATCH_MP o prove)
   (`n = SUC m
     ==> (bit n (word_neg x:N word) <=>
          n < dimindex(:N) /\
          (bit n x <=> ~bit m x /\ ~bit m (word_neg x)))`,
    SIMP_TAC[REWRITE_RULE[GSYM ADD1] BIT_WORD_NEG_CLAUSES])
  and conv_shl = GEN_REWRITE_CONV I [REWRITE_RULE[CONJ_ASSOC] BIT_WORD_SHL]
  and conv_ror = GEN_REWRITE_CONV I [pth_ror]
  and conv_rol = GEN_REWRITE_CONV I [pth_rol]
  and conv_cond_t = GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)]
  and conv_cond_f = GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)]
  and conv_and = GEN_REWRITE_CONV I [AND_CLAUSES]
  and conv_and_t = GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL AND_CLAUSES)]
  and conv_and_f = GEN_REWRITE_CONV I [el 2 (CONJUNCTS(SPEC_ALL AND_CLAUSES))]
  and zero_tm = `0` and one_tm = `1` in
  fun tm ->
    match tm with
      Comb(Comb(Const("bit",_),n),Comb(Const("word",_),m))
      when is_numeral n && is_numeral m ->
          if m = zero_tm then
            GEN_REWRITE_CONV I [BIT_WORD_0] tm
          else if m = one_tm then
            (GEN_REWRITE_CONV I [BIT_WORD_1] THENC NUM_EQ_CONV) tm
          else
            (GEN_REWRITE_CONV I [BIT_WORD] THENC
             BINOP2_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV)
                         (RAND_CONV (RAND_CONV NUM_EXP_CONV THENC
                                     NUM_DIV_CONV) THENC
                          NUM_ODD_CONV) THENC
             conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Const("word",_),m))
      when is_numeral n && m = one_tm ->
          (GEN_REWRITE_CONV I [BIT_WORD_1] THENC NUM_EQ_CONV) tm
    | Comb(Comb(Const("bit",_),n),Comb(Const("word_not",_),_))
      when is_numeral n ->
       (GEN_REWRITE_CONV I [BIT_WORD_NOT] THENC
        LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
        conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_and",_),_),_))
      when is_numeral n ->
        GEN_REWRITE_CONV I [BIT_WORD_AND_ALT] tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_or",_),_),_))
      when is_numeral n ->
        GEN_REWRITE_CONV I [BIT_WORD_OR_ALT] tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_xor",_),_),_))
      when is_numeral n ->
        GEN_REWRITE_CONV I [BIT_WORD_XOR_ALT] tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_add",_),_),_))
      when is_numeral n ->
        if n = zero_tm then
         (GEN_REWRITE_CONV I [CONJUNCT1 BIT_WORD_ADD_CLAUSES]) tm
        else
         (GEN_REWRITE_CONV I [rule_add (num_CONV n)] THENC
          LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
          conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_sub",_),_),_))
      when is_numeral n ->
        if n = zero_tm then
         (GEN_REWRITE_CONV I [CONJUNCT1 BIT_WORD_SUB_CLAUSES]) tm
        else
         (GEN_REWRITE_CONV I [rule_sub (num_CONV n)] THENC
          LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
          conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Const("word_neg",_),_))
      when is_numeral n ->
        if n = zero_tm then
         (GEN_REWRITE_CONV I [CONJUNCT1 BIT_WORD_NEG_CLAUSES]) tm
        else
         (GEN_REWRITE_CONV I [rule_neg (num_CONV n)] THENC
          LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
          conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_shl",_),_),m))
      when is_numeral n && is_numeral m ->
        (conv_shl THENC
         BINOP2_CONV (BINOP2_CONV NUM_LE_CONV
                       (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
                         conv_and)
                     (LAND_CONV NUM_SUB_CONV) THENC
         conv_and) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_ushr",_),_),m))
      when is_numeral n && is_numeral m ->
        (GEN_REWRITE_CONV I [BIT_WORD_USHR] THENC LAND_CONV NUM_ADD_CONV) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_ishr",_),_),m))
      when is_numeral n && is_numeral m ->
        (GEN_REWRITE_CONV I [BIT_WORD_ISHR] THENC
         RATOR_CONV(LAND_CONV
           (BINOP2_CONV NUM_ADD_CONV (!word_SIZE_CONV) THENC
            NUM_LT_CONV)) THENC
         ((conv_cond_t THENC
           LAND_CONV NUM_ADD_CONV) ORELSEC
          (conv_cond_f THENC
           COMB2_CONV
              (RAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV))
              (LAND_CONV(LAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV)) THENC
           conv_and))) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_ror",_),_),m))
      when is_numeral n && is_numeral m ->
        (conv_ror THENC
         RAND_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_MOD_CONV) THENC
         BETA_CONV THENC RAND_CONV NUM_ADD_CONV THENC BETA_CONV THENC
         RATOR_CONV(LAND_CONV
          (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV)) THENC
         (conv_cond_t ORELSEC
          (conv_cond_f THENC
           LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
           ((conv_and_t THENC
             LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV)) ORELSEC
            conv_and_f
           ))))
        tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_rol",_),_),m))
      when is_numeral n && is_numeral m ->
        (conv_rol THENC
         RAND_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_MOD_CONV) THENC
         BETA_CONV THENC
         RATOR_CONV(LAND_CONV NUM_LT_CONV) THENC
         ((conv_cond_t THENC
           LAND_CONV(RAND_CONV
            (LAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV) THENC
           NUM_ADD_CONV)) ORELSEC
          (conv_cond_f THENC
           LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
           ((conv_and_t THENC
             LAND_CONV NUM_SUB_CONV) ORELSEC
            conv_and_f)
         ))) tm
    | Comb(Comb(Const("bit",_),n),Comb(Comb(Const("word_join",_),_),_))
      when is_numeral n ->
        (GEN_REWRITE_CONV I [BIT_WORD_JOIN] THENC
         LAND_CONV (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV) THENC
         (conv_and_f ORELSEC
          (conv_and_t THENC
           RATOR_CONV(LAND_CONV
            (RAND_CONV(!word_SIZE_CONV) THENC NUM_LT_CONV)) THENC
           (conv_cond_t ORELSEC
            (conv_cond_f THENC
             LAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_SUB_CONV))
          ))))
        tm
    | Comb(Comb(Const("bit",_),n),
           Comb(Comb(Const("word_subword",_),_),
                Comb(Comb(Const(",",_),p),q)))
        when is_numeral n && is_numeral p && is_numeral q ->
         (GEN_REWRITE_CONV I [BIT_WORD_SUBWORD] THENC
          LAND_CONV
           (RAND_CONV(RAND_CONV(!word_SIZE_CONV) THENC NUM_MIN_CONV) THENC
            NUM_LT_CONV) THENC
          ((conv_and_t THENC
             LAND_CONV NUM_ADD_CONV) ORELSEC
            conv_and_f)) tm
    | _ -> failwith "BIT_WORD_CONV";;

(* ------------------------------------------------------------------------- *)
(* Conversions for explicit calculations with terms of the form "word n"     *)
(* where n is a numeral. They all work for arbitrary n and whenever they     *)
(* return "word m", then that will be canonical, i.e. m < 2^wordsize.        *)
(* ------------------------------------------------------------------------- *)

let WORD_WORD_CONV =
  let pth = prove
   (`word n:N word = word(n MOD (2 EXP dimindex(:N)))`,
    REWRITE_TAC[WORD_MOD_SIZE]) in
  fun tm ->
    match tm with
      Comb(Const("word",_),t) when is_numeral t ->
        (GEN_REWRITE_CONV I [pth] THENC
         funpow 2 RAND_CONV (!word_POW2SIZE_CONV) THENC
         RAND_CONV NUM_MOD_CONV) tm
    | _ -> failwith "WORD_WORD_CONV";;

let WORD_IWORD_CONV tm =
  match tm with
   Comb(Const("iword",_),t) when is_intconst t ->
     (REWR_CONV iword THENC
      funpow 4 RAND_CONV (!word_SIZE_CONV) THENC
      funpow 3 RAND_CONV INT_POW_CONV THENC
      funpow 2 RAND_CONV INT_REM_CONV THENC
      GEN_REWRITE_CONV RAND_CONV [NUM_OF_INT_OF_NUM]) tm
  | _ -> failwith "WORD_IWORD_CONV";;

let WORD_VAL_CONV tm =
  match tm with
    Comb(Const("val",_),Comb(Const("word",_),n)) when is_numeral n ->
     (GEN_REWRITE_CONV I [VAL_WORD] THENC
      funpow 2 RAND_CONV (!word_SIZE_CONV) THENC
      RAND_CONV NUM_EXP_CONV THENC NUM_MOD_CONV) tm
  | _ -> failwith "WORD_VAL_CONV";;

let WORD_IVAL_CONV =
  let pth = prove
   (`ival(word n:N word) =
        (\v. if v < 2 EXP (dimindex (:N) - 1)
             then &v else &v - &2 pow dimindex(:N))
        (val(word n:N word))`,
    REWRITE_TAC[ival])
  and cth1,cth2 = CONJ_PAIR
   (MESON[] `(if T then x:int else y:int) = x /\
             (if F then x:int else y:int) = y`) in
  fun tm ->
   (match tm with
      Comb(Const("ival",_),Comb(Const("word",_),n)) when is_numeral n ->
     (GEN_REWRITE_CONV I [pth] THENC
      RAND_CONV WORD_VAL_CONV THENC
      BETA_CONV THENC
      RATOR_CONV(LAND_CONV
       (RAND_CONV (RAND_CONV
           (LAND_CONV (!word_SIZE_CONV) THENC NUM_SUB_CONV) THENC
         NUM_EXP_CONV) THENC
        NUM_LT_CONV)) THENC
      (GEN_REWRITE_CONV I [cth1] ORELSEC
       (GEN_REWRITE_CONV I [cth2] THENC
        (RAND_CONV o RAND_CONV) (!word_SIZE_CONV) THENC
        RAND_CONV INT_POW_CONV THENC INT_SUB_CONV))) tm
    | _ -> failwith "WORD_IVAL_CONV");;

let WORD_BIT_CONV =
  let pth0 = prove
   (`(ODD(0 DIV 2 EXP k) <=> F) /\
     (ODD(NUMERAL(BIT0 n) DIV 2 EXP 0) <=> F) /\
     (ODD(NUMERAL(BIT1 n) DIV 2 EXP 0) <=> T)`,
    REWRITE_TAC[DIV_0; ODD; EXP; DIV_1] THEN
    REWRITE_TAC[NUMERAL; BIT0; BIT1] THEN
    REWRITE_TAC[ODD; ODD_ADD])
  and pth1 = prove
   (`(ODD(NUMERAL(BIT0 n) DIV 2 EXP SUC k) <=> ODD(NUMERAL n DIV (2 EXP k))) /\
     (ODD(NUMERAL(BIT1 n) DIV 2 EXP SUC k) <=> ODD(NUMERAL n DIV (2 EXP k)))`,
    CONJ_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [NUMERAL] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [BIT0; BIT1] THEN
    REWRITE_TAC[EXP; GSYM DIV_DIV] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
  let conv0 = GEN_REWRITE_CONV I [pth0]
  and conv1 = GEN_REWRITE_CONV I [pth1]
  and conva = GEN_REWRITE_CONV I [AND_CLAUSES] in
  let rec conv tm =
    (conv0 ORELSEC
     (funpow 3 RAND_CONV num_CONV THENC
      conv1 THENC
      conv)) tm in
  fun tm ->
    match tm with
       Comb(Comb(Const("bit",_),k),Comb(Const("word",_),n))
       when is_numeral k && is_numeral n ->
     (GEN_REWRITE_CONV I [BIT_WORD] THENC
      BINOP2_CONV (RAND_CONV (!word_SIZE_CONV) THENC NUM_LT_CONV) conv THENC
      conva) tm
    | _ -> failwith "WORD_BIT_CONV";;

let WORD_EQ_CONV =
   let pth = prove
   (`word(NUMERAL m):N word = (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) = val(word(NUMERAL n):N word)`,
    REWRITE_TAC[VAL_EQ]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_VAL_CONV THENC NUM_EQ_CONV;;

let WORD_ULT_CONV =
  let pth = prove
   (`word_ult (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) < val(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ult; relational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_VAL_CONV THENC NUM_LT_CONV;;

let WORD_ULE_CONV =
  let pth = prove
   (`word_ule (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) <= val(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ule; relational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_VAL_CONV THENC NUM_LE_CONV;;

let WORD_UGT_CONV =
  let pth = prove
   (`word_ugt (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) > val(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ugt; relational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_VAL_CONV THENC NUM_GT_CONV;;

let WORD_UGE_CONV =
  let pth = prove
   (`word_uge (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) >= val(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_uge; relational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_VAL_CONV THENC NUM_GE_CONV;;

let WORD_ILT_CONV =
  let pth = prove
   (`word_ilt (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) < ival(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ilt; irelational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_IVAL_CONV THENC INT_LT_CONV;;

let WORD_ILE_CONV =
  let pth = prove
   (`word_ile (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) <= ival(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ile; irelational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_IVAL_CONV THENC INT_LE_CONV;;

let WORD_IGT_CONV =
  let pth = prove
   (`word_igt (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) > ival(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_igt; irelational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_IVAL_CONV THENC INT_GT_CONV;;

let WORD_IGE_CONV =
  let pth = prove
   (`word_ige (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) >= ival(word(NUMERAL n):N word)`,
    REWRITE_TAC[word_ige; irelational2]) in
  GEN_REWRITE_CONV I [pth] THENC BINOP_CONV WORD_IVAL_CONV THENC INT_GE_CONV;;

let WORD_ADD_CONV =
  let pth = prove
   (`word_add (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word((NUMERAL m + NUMERAL n) MOD (2 EXP dimindex(:N)))`,
    REWRITE_TAC[word_add; modular; VAL_WORD; WORD_EQ; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV NUM_ADD_CONV (!word_POW2SIZE_CONV) THENC NUM_MOD_CONV);;

let WORD_MUL_CONV =
  let pth = prove
   (`word_mul (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word((NUMERAL m * NUMERAL n) MOD (2 EXP dimindex(:N)))`,
    REWRITE_TAC[word_mul; modular; VAL_WORD; WORD_EQ; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV NUM_MULT_CONV (!word_POW2SIZE_CONV) THENC NUM_MOD_CONV);;

let WORD_SUB_CONV =
  let pth = prove
   (`word_sub (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word((NUMERAL m + (p - NUMERAL n MOD p)) MOD p))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[word_sub; modular; VAL_WORD; WORD_EQ; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV
   (LAND_CONV
    (RAND_CONV(RAND_CONV NUM_MOD_CONV THENC NUM_SUB_CONV) THENC
     NUM_ADD_CONV) THENC
    NUM_MOD_CONV);;

let WORD_NEG_CONV =
  let pth = prove
   (`word_neg (word(NUMERAL n):N word) =
     (\p. word((p - NUMERAL n MOD p) MOD p))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[word_neg; word_sub; modular; VAL_WORD; WORD_EQ; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_CLAUSES]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV
   (LAND_CONV
    (RAND_CONV NUM_MOD_CONV THENC NUM_SUB_CONV) THENC
    NUM_MOD_CONV);;

let WORD_UDIV_CONV =
  let pth = prove
   (`word_udiv (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word((NUMERAL m MOD p) DIV (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UDIV; VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
     `m DIV n <= m /\ m < p ==> m DIV n < p`) THEN
    SIMP_TAC[DIV_LE; DIVISION; EXP_EQ_0; ARITH_EQ]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV(BINOP_CONV NUM_MOD_CONV THENC NUM_DIV_CONV);;

let WORD_UMOD_CONV =
  let pth = prove
   (`word_umod (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word((NUMERAL m MOD p) MOD (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMOD; VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
     `m MOD n <= m /\ m < p ==> m MOD n < p`) THEN
    SIMP_TAC[MOD_LE; DIVISION; EXP_EQ_0; ARITH_EQ]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV(BINOP_CONV NUM_MOD_CONV THENC NUM_MOD_CONV);;

let WORD_UMAX_CONV =
  let pth = prove
   (`word_umax (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word(MAX (NUMERAL m MOD p) (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMAX; VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[ARITH_RULE `MAX a b < n <=> a < n /\ b < n`] THEN
    SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV(BINOP_CONV NUM_MOD_CONV THENC NUM_MAX_CONV);;

let WORD_UMIN_CONV =
  let pth = prove
   (`word_umin (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word(MIN (NUMERAL m MOD p) (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMIN; VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[ARITH_RULE `MIN a b < n <=> a < n \/ b < n`] THEN
    SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV(BINOP_CONV NUM_MOD_CONV THENC NUM_MIN_CONV);;

let WORD_IMAX_CONV =
  let pth = prove
   (`word_imax (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     if ival(word(NUMERAL m):N word) <= ival(word(NUMERAL n):N word)
     then word((NUMERAL n) MOD (2 EXP dimindex(:N)))
     else word((NUMERAL m) MOD (2 EXP dimindex(:N)))`,
    COND_CASES_TAC THEN
    REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_IMAX; WORD_MOD_SIZE] THEN
    ASM_REWRITE_TAC[INT_MAX]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(LAND_CONV(BINOP_CONV WORD_IVAL_CONV THENC INT_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES] THENC
  funpow 2 RAND_CONV (!word_POW2SIZE_CONV) THENC RAND_CONV NUM_MOD_CONV;;

let WORD_IMIN_CONV =
  let pth = prove
   (`word_imin (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     if ival(word(NUMERAL m):N word) <= ival(word(NUMERAL n):N word)
     then word((NUMERAL m) MOD (2 EXP dimindex(:N)))
     else word((NUMERAL n) MOD (2 EXP dimindex(:N)))`,
    COND_CASES_TAC THEN
    REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_IMIN; WORD_MOD_SIZE] THEN
    ASM_REWRITE_TAC[INT_MIN]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(LAND_CONV(BINOP_CONV WORD_IVAL_CONV THENC INT_LE_CONV)) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES] THENC
  funpow 2 RAND_CONV (!word_POW2SIZE_CONV) THENC RAND_CONV NUM_MOD_CONV;;

let WORD_SHL_CONV =
  let pth = prove
   (`word_shl (word(NUMERAL m):N word) (NUMERAL n) =
     (\p. word((NUMERAL m * 2 EXP (NUMERAL n)) MOD p))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[word_shl; WORD_EQ; VAL_WORD; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV (!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV
   (LAND_CONV
     (RAND_CONV NUM_EXP_CONV THENC
      NUM_MULT_CONV) THENC
    NUM_MOD_CONV);;

let WORD_USHR_CONV =
  let pth = prove
   (`word_ushr (word(NUMERAL m):N word) (NUMERAL n) =
     (\p. word((NUMERAL m MOD p) DIV (2 EXP NUMERAL n) MOD p))
     (2 EXP dimindex(:N))`,
    REWRITE_TAC[word_ushr; WORD_EQ; VAL_WORD; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV (!word_POW2SIZE_CONV) THENC BETA_CONV THENC
  RAND_CONV
   (LAND_CONV
     (BINOP2_CONV NUM_MOD_CONV NUM_EXP_CONV THENC NUM_DIV_CONV) THENC
    NUM_MOD_CONV);;

let WORD_ISHR_CONV =
  let pth = prove
   (`word_ishr (word(NUMERAL m):N word) (NUMERAL n) =
     iword (ival(word(NUMERAL m):N word) div &2 pow (NUMERAL n))`,
    REWRITE_TAC[word_ishr]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(BINOP2_CONV WORD_IVAL_CONV INT_POW_CONV THENC INT_DIV_CONV) THENC
  WORD_IWORD_CONV;;

let WORD_NOT_CONV =
  let pth = prove
   (`word_not(word n:N word) =
     (\p. word(p - 1 - n MOD p)) (2 EXP dimindex(:N))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_NOT; VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC(ARITH_RULE `~(p = 0) ==> p - 1 - n < p`) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ]) in
  fun tm ->
   (match tm with
      Comb(Const("word_not",_),Comb(Const("word",_),n)) when is_numeral n ->
     (GEN_REWRITE_CONV I [pth] THENC
      RAND_CONV (!word_POW2SIZE_CONV) THENC BETA_CONV THENC
      RAND_CONV(BINOP2_CONV NUM_SUB_CONV NUM_MOD_CONV THENC
                NUM_SUB_CONV)) tm
    | _ -> failwith "WORD_NOT_CONV");;

let WORD_AND_CONV =
  let pth = prove
   (`?f. ((!n. f _0 n = _0) /\ (!m. f m _0 = _0)) /\
         ((!m n. f (BIT0 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT0 m) (BIT1 n) = BIT0(f m n)) /\
          (!m n. f (BIT1 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT1 m) (BIT1 n) = BIT1(f m n))) /\
         (!m n. word_and (word(NUMERAL m):N word) (word(NUMERAL n)) =
                word(NUMERAL(f m n)))`,
    MP_TAC(prove_general_recursive_function_exists
     `?f. !m n. f m n =
                if m = 0 then 0 else if n = 0 then 0
                else (if m MOD 2 = 1 /\ n MOD 2 = 1 then 1 else 0) +
                     2 * f (m DIV 2) (n DIV 2)`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->num->num` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(!n. f 0 n = 0) /\ (!m. f m 0 = 0) /\
      (!m n. f (2 * m) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m) (2 * n + 1) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n + 1) = 2 * f m n + 1)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                  ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD;
                 MOD_MULT; ADD_EQ_0; MULT_EQ_0] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `1 + 2 * n = 2 * n + 1`] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
      REWRITE_TAC[ARITH_RULE `0 = 2 * n <=> n = 0`] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      ASM_REWRITE_TAC[COND_ID];
      FIRST_X_ASSUM(K ALL_TAC) THEN STRIP_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NUMERAL]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[BIT0; BIT1] THEN ASM_REWRITE_TAC[GSYM MULT_2; ADD1];
      REWRITE_TAC[NUMERAL]] THEN
    REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD] THEN
    SIMP_TAC[TAUT `(p /\ q <=> p /\ r) <=> (p ==> (q <=> r))`] THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC[EXP; DIV_1; ODD_MULT; ARITH; ODD_ADD] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM DIV_DIV] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                MOD_MULT; ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)
  and qth = prove
   (`BIT0 _0 = _0`,
    REWRITE_TAC[ARITH_ZERO])
  and nty = `:N` in
  fun tm ->
    (match tm with
      Comb(Comb(Const("word_and",_),
                Comb(Const("word",_),m)),
           Comb(Const("word",_),n))
          when is_numeral m && is_numeral n ->
       let th1 = INST_TYPE
          [hd(snd(dest_type(type_of(rand tm)))),nty] pth in
       let f,bod = dest_exists(concl th1) in
       let pth_base,th2 = CONJ_PAIR(ASSUME bod) in
       let pth_step,pth_trans = CONJ_PAIR th2 in
       let base_conv = GEN_REWRITE_CONV I [pth_base]
       and step_conv = GEN_REWRITE_CONV I [pth_step]
       and fix_conv = GEN_REWRITE_CONV TRY_CONV [qth] in
       let rec conv t =
         (base_conv ORELSEC
          (step_conv THENC RAND_CONV conv THENC fix_conv)) t in
       let th3 = REWR_CONV pth_trans tm in
       let th4 = CONV_RULE(funpow 3 RAND_CONV conv) th3 in
       let th5 = PROVE_HYP th1 (SIMPLE_CHOOSE f th4) in
       CONV_RULE(RAND_CONV WORD_WORD_CONV) th5
     | _ -> failwith "WORD_AND_CONV");;

let WORD_OR_CONV =
  let pth = prove
   (`?f. ((!n. f _0 n = n) /\ (!m. f m _0 = m)) /\
         ((!m n. f (BIT0 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT0 m) (BIT1 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT0 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT1 n) = BIT1(f m n))) /\
         (!m n. word_or (word(NUMERAL m):N word) (word(NUMERAL n)) =
                word(NUMERAL(f m n)))`,
    MP_TAC(prove_general_recursive_function_exists
     `?f. !m n. f m n =
                if m = 0 then n else if n = 0 then m
                else (if m MOD 2 = 1 \/ n MOD 2 = 1 then 1 else 0) +
                     2 * f (m DIV 2) (n DIV 2)`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->num->num` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(!n. f 0 n = n) /\ (!m. f m 0 = m) /\
      (!m n. f (2 * m) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n) = 2 * f m n + 1) /\
      (!m n. f (2 * m) (2 * n + 1) = 2 * f m n + 1) /\
      (!m n. f (2 * m + 1) (2 * n + 1) = 2 * f m n + 1)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                  ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD;
                 MOD_MULT; ADD_EQ_0; MULT_EQ_0] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `1 + 2 * n = 2 * n + 1`] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      ASM_REWRITE_TAC[COND_ID] THEN MESON_TAC[];
      FIRST_X_ASSUM(K ALL_TAC) THEN STRIP_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NUMERAL]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[BIT0; BIT1] THEN ASM_REWRITE_TAC[GSYM MULT_2; ADD1];
      REWRITE_TAC[NUMERAL]] THEN
    REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_OR; BIT_WORD] THEN
    SIMP_TAC[TAUT `(p /\ q <=> p /\ r) <=> (p ==> (q <=> r))`] THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC[EXP; DIV_1; ODD_MULT; ARITH; ODD_ADD] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM DIV_DIV] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                MOD_MULT; ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)
  and qth = prove
   (`BIT0 _0 = _0`,
    REWRITE_TAC[ARITH_ZERO])
  and nty = `:N` in
  fun tm ->
    (match tm with
      Comb(Comb(Const("word_or",_),
                Comb(Const("word",_),m)),
           Comb(Const("word",_),n))
          when is_numeral m && is_numeral n ->
       let th1 = INST_TYPE
          [hd(snd(dest_type(type_of(rand tm)))),nty] pth in
       let f,bod = dest_exists(concl th1) in
       let pth_base,th2 = CONJ_PAIR(ASSUME bod) in
       let pth_step,pth_trans = CONJ_PAIR th2 in
       let base_conv = GEN_REWRITE_CONV I [pth_base]
       and step_conv = GEN_REWRITE_CONV I [pth_step]
       and fix_conv = GEN_REWRITE_CONV TRY_CONV [qth] in
       let rec conv t =
         (base_conv ORELSEC
          (step_conv THENC RAND_CONV conv THENC fix_conv)) t in
       let th3 = REWR_CONV pth_trans tm in
       let th4 = CONV_RULE(funpow 3 RAND_CONV conv) th3 in
       let th5 = PROVE_HYP th1 (SIMPLE_CHOOSE f th4) in
       CONV_RULE(RAND_CONV WORD_WORD_CONV) th5
     | _ -> failwith "WORD_OR_CONV");;

let WORD_XOR_CONV =
  let pth = prove
   (`?f. ((!n. f _0 n = n) /\ (!m. f m _0 = m)) /\
         ((!m n. f (BIT0 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT0 m) (BIT1 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT0 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT1 n) = BIT0(f m n))) /\
         (!m n. word_xor (word(NUMERAL m):N word) (word(NUMERAL n)) =
                word(NUMERAL(f m n)))`,
    MP_TAC(prove_general_recursive_function_exists
     `?f. !m n. f m n =
                if m = 0 then n else if n = 0 then m
                else (if m MOD 2 = 1 <=> n MOD 2 = 1 then 0 else 1) +
                     2 * f (m DIV 2) (n DIV 2)`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->num->num` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(!n. f 0 n = n) /\ (!m. f m 0 = m) /\
      (!m n. f (2 * m) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n) = 2 * f m n + 1) /\
      (!m n. f (2 * m) (2 * n + 1) = 2 * f m n + 1) /\
      (!m n. f (2 * m + 1) (2 * n + 1) = 2 * f m n)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                  ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD;
                 MOD_MULT; ADD_EQ_0; MULT_EQ_0] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `1 + 2 * n = 2 * n + 1`] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      ASM_REWRITE_TAC[COND_ID] THEN MESON_TAC[];
      FIRST_X_ASSUM(K ALL_TAC) THEN STRIP_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NUMERAL]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[BIT0; BIT1] THEN ASM_REWRITE_TAC[GSYM MULT_2; ADD1];
      REWRITE_TAC[NUMERAL]] THEN
    REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_XOR; BIT_WORD] THEN
    SIMP_TAC[TAUT `(p /\ q <=> p /\ r) <=> (p ==> (q <=> r))`] THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[DIV_0; ODD] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC[EXP; DIV_1; ODD_MULT; ARITH; ODD_ADD] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM DIV_DIV] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`;
                MOD_MULT; ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)
  and qth = prove
   (`BIT0 _0 = _0`,
    REWRITE_TAC[ARITH_ZERO])
  and nty = `:N` in
  fun tm ->
    (match tm with
      Comb(Comb(Const("word_xor",_),
                Comb(Const("word",_),m)),
           Comb(Const("word",_),n))
          when is_numeral m && is_numeral n ->
       let th1 = INST_TYPE
          [hd(snd(dest_type(type_of(rand tm)))),nty] pth in
       let f,bod = dest_exists(concl th1) in
       let pth_base,th2 = CONJ_PAIR(ASSUME bod) in
       let pth_step,pth_trans = CONJ_PAIR th2 in
       let base_conv = GEN_REWRITE_CONV I [pth_base]
       and step_conv = GEN_REWRITE_CONV I [pth_step]
       and fix_conv = GEN_REWRITE_CONV TRY_CONV [qth] in
       let rec conv t =
         (base_conv ORELSEC
          (step_conv THENC RAND_CONV conv THENC fix_conv)) t in
       let th3 = REWR_CONV pth_trans tm in
       let th4 = CONV_RULE(funpow 3 RAND_CONV conv) th3 in
       let th5 = PROVE_HYP th1 (SIMPLE_CHOOSE f th4) in
       CONV_RULE(RAND_CONV WORD_WORD_CONV) th5
     | _ -> failwith "WORD_XOR_CONV");;

let WORD_ROL_CONV =
  let pth = prove
   (`word_rol (word(NUMERAL m):N word) n =
     (\n. word_or (word_shl (word(NUMERAL m):N word) n)
                  (word_ushr (word(NUMERAL m):N word) (dimindex (:N) - n)))
     (n MOD dimindex(:N))`,
    REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ROL_MOD] THEN
    SIMP_TAC[WORD_ROL_SHIFTS; DIMINDEX_NONZERO; DIVISION; LT_IMP_LE]) in
  GEN_REWRITE_CONV I [pth] THENC
  (RAND_CONV o RAND_CONV) (!word_SIZE_CONV) THENC
  RAND_CONV NUM_MOD_CONV THENC NUM_REDUCE_CONV THENC
  BINOP2_CONV WORD_SHL_CONV
              ((RAND_CONV o LAND_CONV) (!word_SIZE_CONV) THENC
               RAND_CONV NUM_SUB_CONV THENC WORD_USHR_CONV) THENC
  WORD_OR_CONV;;

let WORD_ROR_CONV =
  let pth = prove
   (`word_ror (word(NUMERAL m):N word) n =
     (\n. word_or (word_ushr (word(NUMERAL m):N word) n)
                  (word_shl (word(NUMERAL m):N word) (dimindex (:N) - n)))
     (n MOD dimindex(:N))`,
    REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ROR_MOD] THEN
    SIMP_TAC[WORD_ROR_SHIFTS; DIMINDEX_NONZERO; DIVISION; LT_IMP_LE]) in
  GEN_REWRITE_CONV I [pth] THENC
  (RAND_CONV o RAND_CONV) (!word_SIZE_CONV) THENC
  RAND_CONV NUM_MOD_CONV THENC NUM_REDUCE_CONV THENC
  BINOP2_CONV WORD_USHR_CONV
              ((RAND_CONV o LAND_CONV) (!word_SIZE_CONV) THENC
               RAND_CONV NUM_SUB_CONV THENC WORD_SHL_CONV) THENC
  WORD_OR_CONV;;

let WORD_ZX_CONV =
  let pth = prove
   (`(word_zx:M word->N word) (word (NUMERAL n)) =
     word (NUMERAL n MOD (2 EXP (MIN (dimindex(:M)) (dimindex(:N)))))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
    MESON_TAC[MOD_MOD_EXP_MIN; MOD_MOD_REFL]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (RAND_CONV
     (RAND_CONV(BINOP_CONV (!word_SIZE_CONV) THENC
                NUM_MIN_CONV) THENC
      NUM_EXP_CONV) THENC
    NUM_MOD_CONV);;

let WORD_SX_CONV =
  let pth = prove
   (`(word_sx:M word->N word) (word (NUMERAL n)) =
     iword(ival(word(NUMERAL n):M word))`,
    REWRITE_TAC[word_sx]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV WORD_IVAL_CONV THENC
  WORD_IWORD_CONV;;

let WORD_CAND_CONV =
 let pth = prove
  (`word_cand (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
    if word(NUMERAL m):N word = word 0 \/
       word(NUMERAL n):N word = word 0
    then word 0 else word 1`,
   REWRITE_TAC[WORD_CAND]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(LAND_CONV
   (BINOP_CONV WORD_EQ_CONV THENC
    GEN_REWRITE_CONV I [OR_CLAUSES])) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

let WORD_COR_CONV =
 let pth = prove
  (`word_cor (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
    if word(NUMERAL m):N word = word 0 /\
       word(NUMERAL n):N word = word 0
    then word 0 else word 1`,
   REWRITE_TAC[WORD_COR]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(LAND_CONV
   (BINOP_CONV WORD_EQ_CONV THENC
    GEN_REWRITE_CONV I [AND_CLAUSES])) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES];;

let WORD_JOIN_CONV =
 let pth = prove
   (`(word_join:(M)word->(N)word->(P)word)
     (word(NUMERAL m)) (word(NUMERAL n)) =
     word((2 EXP dimindex(:N) * NUMERAL m MOD 2 EXP dimindex(:M) +
           NUMERAL n MOD 2 EXP dimindex(:N)) MOD
          2 EXP dimindex(:P))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; VAL_WORD; MOD_MOD_REFL]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV
      (BINOP2_CONV
         (BINOP2_CONV
           (!word_POW2SIZE_CONV)
           (RAND_CONV(!word_POW2SIZE_CONV) THENC NUM_MOD_CONV) THENC
          NUM_MULT_CONV)
         (RAND_CONV(!word_POW2SIZE_CONV) THENC NUM_MOD_CONV)  THENC
       NUM_ADD_CONV)
      (!word_POW2SIZE_CONV) THENC
    NUM_MOD_CONV);;

let WORD_SUBWORD_CONV =
  let pth = prove
   (`word_subword (word(NUMERAL m):M word) (NUMERAL p,NUMERAL q):N word =
     word((val(word(NUMERAL m):M word) DIV 2 EXP NUMERAL p) MOD
           2 EXP MIN (NUMERAL q) (dimindex (:N)))`,
    REWRITE_TAC[word_subword; GSYM MOD_MOD_EXP_MIN] THEN
    REWRITE_TAC[WORD_EQ; CONG; MOD_MOD_REFL]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV
   (BINOP2_CONV
     (BINOP2_CONV WORD_VAL_CONV NUM_EXP_CONV THENC NUM_DIV_CONV)
     (RAND_CONV (RAND_CONV (!word_SIZE_CONV) THENC NUM_MIN_CONV) THENC
      NUM_EXP_CONV) THENC
    NUM_MOD_CONV);;

let WORD_BITS_OF_WORD_CONV =
  let pth = prove
   (`?f. (!i. f i _0 = {} /\
              (!n. f i (BIT0 n) = f (i + 1) n) /\
              (!n. f i (BIT1 n) = i INSERT f (i + 1) n)) /\
         (!w:N word. bits_of_word w = f 0 (val w))`,
    MP_TAC(prove_general_recursive_function_exists
     `?f. !i n. f i n =
                  if n = 0 then {}
             else if n MOD 2 = 1 then i INSERT f (i + 1) (n DIV 2)
             else f (i + 1) (n DIV 2)`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->num->num->bool` THEN
    DISCH_TAC THEN
    GEN_REWRITE_TAC
     (LAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
     [GSYM NUMERAL] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV o BINOP_CONV o
                     BINDER_CONV o LAND_CONV o RAND_CONV)
     [BIT0; BIT1] THEN
    REWRITE_TAC[ADD1; GSYM MULT_2] THEN MATCH_MP_TAC(TAUT
     `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
        GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; ARITH_EQ; ARITH_RULE
       `(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n`] THEN
      REWRITE_TAC[MOD_MULT] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
      POP_ASSUM(K ALL_TAC) THEN
      REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
    X_GEN_TAC `w:N word` THEN REWRITE_TAC[EXTENSION] THEN
    SUBGOAL_THEN
     `!k i. i IN f k (val w) <=> k <= i /\ (i - k) IN bits_of_word(w:N word)`
    MP_TAC THENL [ALL_TAC; MESON_TAC[SUB_0; LE_0]] THEN
    REWRITE_TAC[bits_of_word; BIT_VAL] THEN
    SPEC_TAC(`val(w:N word)`,`n:num`) THEN
    MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[DIV_0; NOT_IN_EMPTY; ARITH] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT; AND_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `i:num`] THEN
    ASM_CASES_TAC `i:num = k` THEN
    ASM_REWRITE_TAC[LE_REFL; SUB_REFL; ARITH_RULE `~(k + 1 <= k)`] THEN
    REWRITE_TAC[EXP; DIV_1; ODD_ADD; ODD_MULT; ARITH] THEN
    ASM_CASES_TAC `k:num <= i` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC; ASM_ARITH_TAC] THEN
    ASM_CASES_TAC `k + 1 <= i` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC; ASM_ARITH_TAC] THEN
    SUBGOAL_THEN `i - k = SUC(i - (k + 1))` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[EXP; GSYM DIV_DIV]] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n`])
  and nty = `:N` in
  fun tm ->
    (match tm with
      Comb(Const("bits_of_word",_),Comb(Const("word",_),n))
          when is_numeral n ->
       let th1 = INST_TYPE
          [hd(snd(dest_type(type_of(rand tm)))),nty] pth in
       let f,bod = dest_exists(concl th1) in
       let pth_clauses,th2 = CONJ_PAIR(ASSUME bod) in
       let pth_z,pth_o = CONJ_PAIR(SPEC_ALL pth_clauses) in
       let pth_0,pth_1 = CONJ_PAIR pth_o in
       let conv_z = GEN_REWRITE_CONV I [pth_z]
       and conv_0 = GEN_REWRITE_CONV I [pth_0]
       and conv_1 = GEN_REWRITE_CONV I [pth_1] in
       let rec conv t =
        (conv_z ORELSEC
         (conv_0 THENC LAND_CONV NUM_ADD_CONV THENC conv) ORELSEC
         (conv_1 THENC RAND_CONV(LAND_CONV NUM_ADD_CONV THENC conv))) t in
       let th3 = REWR_CONV th2 tm in
       let th4 = CONV_RULE(RAND_CONV(RAND_CONV WORD_VAL_CONV)) th3 in
       let th5 = GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [NUMERAL] th4 in
       let th6 = CONV_RULE(RAND_CONV conv) th5 in
       PROVE_HYP th1 (SIMPLE_CHOOSE f th6)
     | _ -> failwith "WORD_BITS_OF_WORD_CONV");;

let WORD_POPCOUNT_CONV =
  let pth = prove
   (`?f. (f _0 = 0 /\
          (!n. f (BIT0 n) = f n) /\
          (!n. f (BIT1 n) = SUC(f n))) /\
         (!w:N word. word_popcount w = f (val w))`,
    MP_TAC(prove_general_recursive_function_exists
     `?f. !n. f n =
                  if n = 0 then 0
             else if n MOD 2 = 1 then SUC(f (n DIV 2))
             else f (n DIV 2)`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->num` THEN
    DISCH_TAC THEN
    GEN_REWRITE_TAC
     (LAND_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
     [GSYM NUMERAL] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINOP_CONV o
                     BINDER_CONV o LAND_CONV o RAND_CONV)
     [BIT0; BIT1] THEN
    REWRITE_TAC[ADD1; GSYM MULT_2] THEN MATCH_MP_TAC(TAUT
     `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
        GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; ARITH_EQ; ARITH_RULE
       `(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n`] THEN
      REWRITE_TAC[MOD_MULT] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[ADD1];
      POP_ASSUM(K ALL_TAC) THEN
      REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
    X_GEN_TAC `w:N word` THEN REWRITE_TAC[word_popcount] THEN
    REWRITE_TAC[bits_of_word; BIT_VAL] THEN
    SUBGOAL_THEN `!n. {i | ODD(n DIV 2 EXP i)} HAS_SIZE f n` MP_TAC THENL
     [ALL_TAC; SIMP_TAC[HAS_SIZE]] THEN
    MATCH_MP_TAC BINARY_INDUCT THEN
    ASM_REWRITE_TAC[HAS_SIZE; DIV_0; ODD; EMPTY_GSPEC;
                    FINITE_EMPTY; CARD_CLAUSES] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!P. {i | P i} = {i | i = 0 /\ P 0} UNION IMAGE SUC {i | P(SUC i)}`
     (fun th -> ONCE_REWRITE_TAC[th])
    THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN
      MESON_TAC[num_CASES];
      REWRITE_TAC[EXP; DIV_1; ODD_ADD; ODD_MULT; ARITH]] THEN
    REWRITE_TAC[EMPTY_GSPEC; SING_GSPEC; GSYM DIV_DIV] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n`] THEN
    REWRITE_TAC[UNION_EMPTY; INSERT_UNION_EQ] THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; CARD_CLAUSES] THEN
    REWRITE_TAC[IN_IMAGE; NOT_SUC; ADD1; EQ_ADD_RCANCEL] THEN
    ASM_SIMP_TAC[CARD_IMAGE_INJ; SUC_INJ])
  and nty = `:N` in
  fun tm ->
    (match tm with
      Comb(Const("word_popcount",_),Comb(Const("word",_),n))
          when is_numeral n ->
       let th1 = INST_TYPE
          [hd(snd(dest_type(type_of(rand tm)))),nty] pth in
       let f,bod = dest_exists(concl th1) in
       let pth_clauses,th2 = CONJ_PAIR(ASSUME bod) in
       let pth_z,pth_o = CONJ_PAIR(SPEC_ALL pth_clauses) in
       let pth_0,pth_1 = CONJ_PAIR pth_o in
       let conv_z = GEN_REWRITE_CONV I [pth_z]
       and conv_0 = GEN_REWRITE_CONV I [pth_0]
       and conv_1 = GEN_REWRITE_CONV I [pth_1] in
       let rec conv t =
        (conv_z ORELSEC
         (conv_0 THENC conv) ORELSEC
         (conv_1 THENC RAND_CONV conv THENC NUM_SUC_CONV)) t in
       let th3 = REWR_CONV th2 tm in
       let th4 = CONV_RULE(RAND_CONV(RAND_CONV WORD_VAL_CONV)) th3 in
       let th5 = GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [NUMERAL] th4 in
       let th6 = CONV_RULE(RAND_CONV conv) th5 in
       PROVE_HYP th1 (SIMPLE_CHOOSE f th6)
     | _ -> failwith "WORD_POPCOUNT_CONV");;

let WORD_EVENPARITY_CONV =
  let conv =
    GEN_REWRITE_CONV I [word_evenparity] THENC
    RAND_CONV WORD_POPCOUNT_CONV THENC
    NUM_EVEN_CONV in
  fun tm ->
   (match tm with
     Comb(Const("word_evenparity",_),Comb(Const("word",_),n))
      when is_numeral n -> conv tm
    | _ -> failwith "WORD_EVENPARITY_CONV");;

let WORD_ODDPARITY_CONV =
  let conv =
    GEN_REWRITE_CONV I [word_oddparity] THENC
    RAND_CONV WORD_POPCOUNT_CONV THENC
    NUM_ODD_CONV in
  fun tm ->
   (match tm with
     Comb(Const("word_oddparity",_),Comb(Const("word",_),n))
      when is_numeral n -> conv tm
    | _ -> failwith "WORD_ODDPARITY_CONV");;

let WORD_JSHL_CONV =
  let pth = prove
   (`word_jshl (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_shl (word(NUMERAL m):N word)
              (val(word(NUMERAL n):N word) MOD dimindex (:N))`,
    REWRITE_TAC[word_jshl]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(BINOP2_CONV WORD_VAL_CONV (!word_SIZE_CONV) THENC
            NUM_MOD_CONV) THENC
  WORD_SHL_CONV;;

let WORD_JSHR_CONV =
  let pth = prove
   (`word_jshr (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_ishr (word(NUMERAL m):N word)
               (val(word(NUMERAL n):N word) MOD dimindex (:N))`,
    REWRITE_TAC[word_jshr]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(BINOP2_CONV WORD_VAL_CONV (!word_SIZE_CONV) THENC
            NUM_MOD_CONV) THENC
  WORD_ISHR_CONV;;

let WORD_JUSHR_CONV =
  let pth = prove
   (`word_jushr (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_ushr (word(NUMERAL m):N word)
               (val(word(NUMERAL n):N word) MOD dimindex (:N))`,
    REWRITE_TAC[word_jushr]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(BINOP2_CONV WORD_VAL_CONV (!word_SIZE_CONV) THENC
            NUM_MOD_CONV) THENC
  WORD_USHR_CONV;;

let WORD_JDIV_CONV =
  let pth = prove
   (`word_jdiv (word(NUMERAL m):N word) (word(NUMERAL n)) =
     (\a b. iword((int_sgn a * int_sgn b) * (abs a div abs b)))
     (ival(word(NUMERAL m):N word)) (ival(word(NUMERAL n):N word))`,
    REWRITE_TAC[word_jdiv; imodular; GSYM INT_MUL_ASSOC]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(RAND_CONV WORD_IVAL_CONV THENC BETA_CONV) THENC
  RAND_CONV WORD_IVAL_CONV THENC BETA_CONV THENC
  RAND_CONV(COMB2_CONV
             (RAND_CONV (BINOP_CONV INT_SGN_CONV THENC INT_MUL_CONV))
             (BINOP_CONV INT_ABS_CONV THENC INT_DIV_CONV) THENC
            INT_MUL_CONV) THENC
  WORD_IWORD_CONV;;

let WORD_JREM_CONV =
  let pth = prove
   (`word_jrem (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_sub (word (NUMERAL m))
              (word_mul (word_jdiv (word (NUMERAL m)) (word (NUMERAL n)))
                        (word (NUMERAL n)))`,
    REWRITE_TAC[word_jrem]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV (LAND_CONV WORD_JDIV_CONV THENC WORD_MUL_CONV) THENC
  WORD_SUB_CONV;;

let WORD_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv)
   [`word(NUMERAL n):N word`,CHANGED_CONV WORD_WORD_CONV;
    `iword i:N word`,WORD_IWORD_CONV;
    `val(w:N word)`,WORD_VAL_CONV;
    `ival(w:N word)`,WORD_IVAL_CONV;
    `bit (NUMERAL k) (word(NUMERAL n):N word)`,WORD_BIT_CONV;
    `word(NUMERAL m):N word = word(NUMERAL n)`,WORD_EQ_CONV;
    `word_ult (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_ULT_CONV;
    `word_ule (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_ULE_CONV;
    `word_ugt (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UGT_CONV;
    `word_uge (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UGE_CONV;
    `word_ilt (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_ILT_CONV;
    `word_ile (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_ILE_CONV;
    `word_igt (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_IGT_CONV;
    `word_ige (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_IGE_CONV;
    `word_neg (word(NUMERAL n):N word)`,WORD_NEG_CONV;
    `word_add (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_ADD_CONV;
    `word_mul (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_MUL_CONV;
    `word_sub (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_SUB_CONV;
    `word_udiv (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UDIV_CONV;
    `word_umod (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UMOD_CONV;
    `word_umax (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UMAX_CONV;
    `word_umin (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_UMIN_CONV;
    `word_imax (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_IMAX_CONV;
    `word_imin (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_IMIN_CONV;
    `word_shl (word(NUMERAL m):N word) (NUMERAL n)`,WORD_SHL_CONV;
    `word_ushr (word(NUMERAL m):N word) (NUMERAL n)`,WORD_USHR_CONV;
    `word_ishr (word(NUMERAL m):N word) (NUMERAL n)`,WORD_ISHR_CONV;
    `word_not (word(NUMERAL n):N word)`,WORD_NOT_CONV;
    `word_and (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_AND_CONV;
    `word_or (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_OR_CONV;
    `word_xor (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_XOR_CONV;
    `word_rol (word(NUMERAL m):N word) (NUMERAL n)`,WORD_ROL_CONV;
    `word_ror (word(NUMERAL m):N word) (NUMERAL n)`,WORD_ROR_CONV;
    `word_zx (word(NUMERAL n):N word)`,WORD_ZX_CONV;
    `word_sx (word(NUMERAL n):N word)`,WORD_SX_CONV;
    `word_cand (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_CAND_CONV;
    `word_cor (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_COR_CONV;
    `word_join (word(NUMERAL m):M word) (word(NUMERAL n):N word)`,
                WORD_JOIN_CONV;
    `word_subword (word(NUMERAL m):M word) (NUMERAL p,NUMERAL q):N word`,
                WORD_SUBWORD_CONV;
    `bits_of_word (word(NUMERAL n):N word)`,WORD_BITS_OF_WORD_CONV;
    `word_popcount (word(NUMERAL n):N word)`,WORD_POPCOUNT_CONV;
    `word_evenparity (word(NUMERAL n):N word)`,WORD_EVENPARITY_CONV;
    `word_oddparity (word(NUMERAL n):N word)`,WORD_ODDPARITY_CONV;
    `word_jshl (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JSHL_CONV;
    `word_jshr (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JSHR_CONV;
    `word_jushr (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JUSHR_CONV;
    `word_jdiv (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JDIV_CONV;
    `word_jrem (word(NUMERAL m):N word) (word(NUMERAL n))`,WORD_JREM_CONV]
  (basic_net()) in
  REWRITES_CONV gconv_net;;

let WORD_REDUCE_CONV = DEPTH_CONV WORD_RED_CONV;;

(* ------------------------------------------------------------------------- *)
(* Alternative returning signed words.                                       *)
(* ------------------------------------------------------------------------- *)

let WORD_TO_IWORD_CONV =
  let pth = prove
   (`word(NUMERAL n):N word = iword(ival(word(NUMERAL n):N word))`,
    REWRITE_TAC[IWORD_IVAL]) in
  GEN_REWRITE_CONV I [pth] THENC RAND_CONV WORD_IVAL_CONV;;

let WORD_IREDUCE_CONV =
  WORD_REDUCE_CONV THENC ONCE_DEPTH_CONV WORD_TO_IWORD_CONV;;
