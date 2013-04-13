(* ========================================================================= *)
(* THE HASKELL BASE                                                          *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for the Haskell base.                                     *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/haskell/haskell.int";;

(* ------------------------------------------------------------------------- *)
(* Proof tools for the Haskell base.                                         *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/haskell/haskell-tactics.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of the Haskell base.                                           *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-def";;

(* Functions *)

let map_domain_def = new_definition
  `!(f : A -> B) (g : B -> C).
     map_domain f g = g o f`;;

add_haskell_thm map_domain_def;;
export_thm map_domain_def;;

let map_range_def = new_definition
  `!(f : A -> B) (g : C -> A).
     map_range f g = f o g`;;

add_haskell_thm map_range_def;;
export_thm map_range_def;;

(* Products *)

let map_fst_def = new_definition
  `!(f : A -> B) (x : A) (y : C).
     map_fst f (x,y) = (f x, y)`;;

add_haskell_thm map_fst_def;;
export_thm map_fst_def;;

let map_snd_def = new_definition
  `!(f : A -> B) (x : C) (y : A).
     map_snd f (x,y) = (x, f y)`;;

add_haskell_thm map_snd_def;;
export_thm map_snd_def;;

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

add_haskell_thm lengthH_def;;
export_thm lengthH_def;;

let rdecode_vectorH_def = define_haskell_const
  `rdecode_vector :
   (random -> A # random) -> num -> random -> A list # random`;;

export_thm rdecode_vectorH_def;;

let rdecode_listH_def = define_haskell_const
  `rdecode_list : (random -> A # random) -> random -> A list # random`;;

export_thm rdecode_listH_def;;

(* Natural numbers *)

let rdecode_fib_destH_def = define_haskell_const
  `rdecode_fib_dest : bool -> num -> num -> num -> random -> num`;;

export_thm rdecode_fib_destH_def;;

let rdecode_fibH_def = define_haskell_const
  `rdecode_fib : random -> num # random`;;

export_thm rdecode_fibH_def;;

let rdecode_geometric_loopH_def = define_haskell_const
  `rdecode_geometric_loop : num -> random -> num`;;

export_thm rdecode_geometric_loopH_def;;

let rdecode_geometricH_def = define_haskell_const
  `rdecode_geometric : random -> num # random`;;

export_thm rdecode_geometricH_def;;

let bit_to_numH_def = define_haskell_const
  `bit_to_num : bool -> num`;;

export_thm bit_to_numH_def;;

let bit_tlH_def = define_haskell_const
  `bit_tl : num -> num`;;

export_thm bit_tlH_def;;

let bit_consH_def = define_haskell_const
  `bit_cons : bool -> num -> num`;;

export_thm bit_consH_def;;

let bitwidthH_def = define_haskell_const
  `bitwidth : num -> num`;;

export_thm bitwidthH_def;;

let bits_to_numH_def = define_haskell_const
  `bits_to_num : bool list -> num`;;

export_thm bits_to_numH_def;;

let dividesH_def = define_haskell_const
  `divides : num -> num -> bool`;;

export_thm dividesH_def;;

let rdecode_uniform_loopH_def = define_haskell_const
  `rdecode_uniform_loop : num -> num -> random -> num`;;

export_thm rdecode_uniform_loopH_def;;

let rdecode_uniformH_def = define_haskell_const
  `rdecode_uniform : num -> random -> num # random`;;

export_thm rdecode_uniformH_def;;

(* Streams *)

let snthH_def = define_haskell_const
  `snth : A stream -> num -> A`;;

export_thm snthH_def;;

let stakeH_def = define_haskell_const
  `stake : A stream -> num -> A list`;;

export_thm stakeH_def;;

let sunfoldH_def = define_haskell_const
  `sunfold : (A -> B # A) -> A -> B stream`;;

export_thm sunfoldH_def;;

(* Random streams *)

let rbitsH_def = define_haskell_const
  `rbits : num -> random -> bool list # random`;;

export_thm rbitsH_def;;

(* Bytes *)

let list_to_byteH_def = define_haskell_const
  `list_to_byte : bool list -> byte`;;

export_thm list_to_byteH_def;;

let rdecode_byteH_def = define_haskell_const
  `rdecode_byte : random -> byte # random`;;

export_thm rdecode_byteH_def;;

(* 16-bit words *)

let list_to_word16H_def = define_haskell_const
  `list_to_word16 : bool list -> word16`;;

export_thm list_to_word16H_def;;

let rdecode_word16H_def = define_haskell_const
  `rdecode_word16 : random -> word16 # random`;;

export_thm rdecode_word16H_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of the Haskell base.                                           *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-thm";;

(* Functions *)

let map_domain_id = prove
  (`map_domain I = (I : (A -> B) -> A -> B)`,
   REWRITE_TAC [FUN_EQ_THM; map_domain_def; I_THM; o_THM]);;

add_haskell_thm map_domain_id;;
export_thm map_domain_id;;

let map_range_id = prove
  (`map_range I = (I : (A -> B) -> A -> B)`,
   REWRITE_TAC [FUN_EQ_THM; map_range_def; I_THM; o_THM]);;

add_haskell_thm map_range_id;;
export_thm map_range_id;;

let map_domain_o = prove
  (`!(f : C -> B) (g : B -> A).
      map_domain f o map_domain g =
      (map_domain (g o f) : (A -> D) -> C -> D)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; map_domain_def; o_THM]);;

add_haskell_thm map_domain_o;;
export_thm map_domain_o;;

let map_range_o = prove
  (`!(f : B -> A) (g : C -> B).
      map_range f o map_range g =
      (map_range (f o g) : (D -> C) -> D -> A)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; map_range_def; o_THM]);;

add_haskell_thm map_range_o;;
export_thm map_range_o;;

(* Products *)

let map_fst_id = prove
  (`map_fst I = (I : A # B -> A # B)`,
   REWRITE_TAC [FUN_EQ_THM; I_THM] THEN
   X_GEN_TAC `x : A # B` THEN
   PAIR_CASES_TAC `x : A # B` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [map_fst_def; I_THM]);;

add_haskell_thm map_fst_id;;
export_thm map_fst_id;;

let map_snd_id = prove
  (`map_snd I = (I : A # B -> A # B)`,
   REWRITE_TAC [FUN_EQ_THM; I_THM] THEN
   X_GEN_TAC `x : A # B` THEN
   PAIR_CASES_TAC `x : A # B` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [map_snd_def; I_THM]);;

add_haskell_thm map_snd_id;;
export_thm map_snd_id;;

let map_fst_o = prove
  (`!(f : B -> A) (g : C -> B).
      map_fst f o map_fst g =
      (map_fst (f o g) : C # D -> A # D)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; o_THM] THEN
   X_GEN_TAC `x : C # D` THEN
   PAIR_CASES_TAC `x : C # D` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [map_fst_def; o_THM]);;

add_haskell_thm map_fst_o;;
export_thm map_fst_o;;

let map_snd_o = prove
  (`!(f : B -> A) (g : C -> B).
      map_snd f o map_snd g =
      (map_snd (f o g) : D # C -> D # A)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; o_THM] THEN
   X_GEN_TAC `x : D # C` THEN
   PAIR_CASES_TAC `x : D # C` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [map_snd_def; o_THM]);;

add_haskell_thm map_snd_o;;
export_thm map_snd_o;;

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

add_haskell_thm equal_optionH;;
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

add_haskell_thm equal_listH;;
export_thm equal_listH;;

(* ------------------------------------------------------------------------- *)
(* Source of the Haskell base.                                               *)
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
 (`!(d : random -> A # random) n r.
     rdecode_vectorH d n r =
     if n = 0 then ([],r) else
     let (h,r') = d r in
     let (t,r'') = rdecode_vectorH d (n - 1) r' in
     (CONS h t, r'')`,
  REPEAT GEN_TAC THEN
  HASKELL_TAC [] THEN
  NUM_CASES_TAC `n : num` THENL
  [DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [rdecode_vector_zero];
   DISCH_THEN (X_CHOOSE_THEN `m : num` SUBST1_TAC) THEN
   REWRITE_TAC [NOT_SUC; rdecode_vector_suc; SUC_SUB1]]);;

let () = (export_haskell_thm o prove)
 (`!(d : random -> A # random) r.
     rdecode_listH d r =
     let (n,r') = rdecode_geometricH r in
     rdecode_vectorH d n r'`,
  HASKELL_TAC [] THEN
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

let () = (export_haskell_thm o prove)
 (`!n r.
     rdecode_geometric_loopH n r =
     let (b,r') = rbit r in
     if b then n else
     rdecode_geometric_loopH (n + 1) r'`,
  HASKELL_TAC [GSYM ADD1] THEN
  ACCEPT_TAC rdecode_geometric_loop_def);;

let () = (export_haskell_thm o prove)
 (`rdecode_geometricH =
   \r.
     let (r1,r2) = rsplit r in
     (rdecode_geometric_loopH 0 r1, r2)`,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
  HASKELL_TAC [] THEN
  ACCEPT_TAC rdecode_geometric_def);;

let () = (export_haskell_thm o prove)
 (`!b. bit_to_numH b = (if b then 1 else 0)`,
  HASKELL_TAC [] THEN
  ACCEPT_TAC bit_to_num_def);;

let () = (export_haskell_thm o prove)
 (`!n. bit_tlH n = n DIV 2`,
  HASKELL_TAC [] THEN
  ACCEPT_TAC bit_tl_def);;

let () = (export_haskell_thm o prove)
 (`!h t. bit_consH h t = bit_to_numH h + 2 * t`,
  HASKELL_TAC [] THEN
  ACCEPT_TAC bit_cons_def);;

let () = (export_haskell_thm o prove)
 (`!n.
     bitwidthH n =
     if n = 0 then 0 else bitwidthH (bit_tlH n) + 1`,
  HASKELL_TAC [] THEN
  ACCEPT_TAC bitwidth_recursion);;

let () = (export_haskell_thm o prove)
 (`bits_to_numH [] = 0 /\
   (!h t. bits_to_numH (CONS h t) = bit_consH h (bits_to_numH t))`,
  HASKELL_TAC [bits_to_num_nil; bits_to_num_cons]);;

let () = (export_haskell_thm o prove)
 (`!m n. dividesH m n = if m = 0 then n = 0 else n MOD m = 0`,
  REPEAT GEN_TAC THEN
  HASKELL_TAC [] THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [zero_divides];
   MATCH_MP_TAC divides_mod THEN
   FIRST_ASSUM ACCEPT_TAC]);;

let () = (export_haskell_thm o prove)
 (`!n w r.
     rdecode_uniform_loopH n w r =
     let (l,r') = rbitsH w r in
     let m = bits_to_numH l in
     if m < n then m else rdecode_uniform_loopH n w r'`,
  HASKELL_TAC [] THEN
  ACCEPT_TAC rdecode_uniform_loop_def);;

let () = (export_haskell_thm o prove)
 (`!n.
     rdecode_uniformH n =
     \r.
       let w = bitwidthH (n - 1) in
       let r1,r2 = rsplit r in
       (rdecode_uniform_loopH n w r1 MOD n, r2)`,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
  HASKELL_TAC [] THEN
  ACCEPT_TAC rdecode_uniform_def);;

(* Streams *)

let () = (export_haskell_thm o prove)
 (`!(s : A stream) n.
     snthH s n = if n = 0 then shd s else snthH (stl s) (n - 1)`,
  GEN_TAC THEN
  HASKELL_TAC [] THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [shd_def];
   REWRITE_TAC [NOT_SUC; SUC_SUB1; snth_suc]]);;

let () = (export_haskell_thm o prove)
 (`!(s : A stream) n.
     stakeH s n = if n = 0 then [] else CONS (shd s) (stakeH (stl s) (n - 1))`,
  GEN_TAC THEN
  HASKELL_TAC [] THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [stake_zero];
   REWRITE_TAC [NOT_SUC; SUC_SUB1; stake_suc]]);;

let () = (export_haskell_thm o prove)
 (`!(f : B -> A # B) b.
     sunfoldH f b =
     let (a,b') = f b in
     scons a (sunfoldH f b')`,
  HASKELL_TAC [] THEN
  ACCEPT_TAC sunfold);;

(* Random streams *)

let () = (export_haskell_thm o prove)
 (`rbitsH = rdecode_vectorH rbit`,
  HASKELL_TAC [] THEN
  ACCEPT_TAC rbits_def);;

(* Bytes *)

let () = (export_haskell_thm o prove)
 (`(list_to_byteH [] = num_to_byte 0) /\
   (!h t.
      list_to_byteH (CONS h t) =
      if h then byte_add (num_to_byte 1) (byte_shl (list_to_byteH t) 1)
      else byte_shl (list_to_byteH t) 1)`,
  HASKELL_TAC [list_to_byte_nil; list_to_byte_cons]);;

let () = (export_haskell_thm o prove)
 (`!r.
     rdecode_byteH r =
     let (r1,r2) = rsplit r in
     let (l,r1') = rbitsH 8 r1 in
     (list_to_byteH l, r2)`,
  HASKELL_TAC [rdecode_byte; byte_width_def]);;

(* 16-bit words *)

let () = (export_haskell_thm o prove)
 (`(list_to_word16H [] = num_to_word16 0) /\
   (!h t.
      list_to_word16H (CONS h t) =
      if h then word16_add (num_to_word16 1) (word16_shl (list_to_word16H t) 1)
      else word16_shl (list_to_word16H t) 1)`,
  HASKELL_TAC [list_to_word16_nil; list_to_word16_cons]);;

let () = (export_haskell_thm o prove)
 (`!r.
     rdecode_word16H r =
     let (r1,r2) = rsplit r in
     let (l,r1') = rbitsH 16 r1 in
     (list_to_word16H l, r2)`,
  HASKELL_TAC [rdecode_word16; word16_width_def]);;

(* ------------------------------------------------------------------------- *)
(* Testing the Haskell base.                                                 *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-test";;

let () = (export_haskell_thm o prove)
 (`2 + 2 = 4`,
  NUM_REDUCE_TAC);;

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
