(* ========================================================================= *)
(* HASKELL SOURCE FOR THE STANDARD THEORY LIBRARY                            *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Haskell source for the standard theory library.                           *)
(* ------------------------------------------------------------------------- *)

logfile "base-haskell-src";;

(***
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
***)

let () = (export_thm o prove)
 (`(LENGTH ([] : A list) = 0) /\
   (!(h : A) t. LENGTH (CONS h t) = LENGTH t + 1)`,
  REWRITE_TAC [LENGTH_NIL; LENGTH_CONS; ADD1]);;

(***
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
***)

(* Natural numbers *)

let () = (export_thm o prove)
 (`!n. ODD n <=> n MOD 2 = 1`,
  ACCEPT_TAC ODD_MOD);;

(***
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
     bit_widthH n =
     if n = 0 then 0 else bit_widthH (bit_tlH n) + 1`,
  HASKELL_TAC [] THEN
  ACCEPT_TAC bit_width_recursion);;

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
       let w = bit_widthH (n - 1) in
       let r1,r2 = rsplit r in
       (rdecode_uniform_loopH n w r1 MOD n, r2)`,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
  HASKELL_TAC [] THEN
  ACCEPT_TAC rdecode_uniform_def);;

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
***)

(* ------------------------------------------------------------------------- *)
(* Haskell tests for the standard theory library.                            *)
(* ------------------------------------------------------------------------- *)

logfile "base-haskell-test";;

let () = (export_thm o prove)
 (`!x : A option. ~(is_some x <=> is_none x)`,
  GEN_TAC THEN
  MP_TAC (SPEC `x : A option` option_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [is_some_def; is_none_def]);;

export_thm sum_distinct;;  (* Haskell *)

(***
let () = (export_thm o prove)
 (`!x : A + B. ~(ISL x <=> ISR x)`,
  GEN_TAC THEN
  MP_TAC (SPEC `x : A + B` sum_CASES) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [ISL_def; ISR_def]);;
***)

(***
let () = (export_thm o prove)
 (`!l : (A # B) list. (let (x,y) = unzip l in zip x y) = l`,
  GEN_TAC THEN
  MP_TAC (SPEC `x : A option` option_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [is_some_def; is_none_def]);;
***)

logfile_end ();;
