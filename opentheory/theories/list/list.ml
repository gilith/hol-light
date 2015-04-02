(* ========================================================================= *)
(* LIST TYPES                                                                *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for list types.                                           *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/list/list.int";;

(* ------------------------------------------------------------------------- *)
(* Proof tools for list types.                                               *)
(* ------------------------------------------------------------------------- *)

let append_conv =
    let nil_conv = REWR_CONV NIL_APPEND in
    let cons_conv = REWR_CONV CONS_APPEND in
    let rec rewr_conv tm =
        (nil_conv ORELSEC
         (cons_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let length_convs =
    let nil_conv = REWR_CONV LENGTH_NIL in
    let cons_conv = REWR_CONV LENGTH_CONS in
    let rec rewr_convs tm =
        try (nil_conv tm, [])
        with Failure _ ->
          let th = cons_conv tm in
          let tm' = rand (rand (concl th)) in
          let (th',ths) = rewr_convs tm' in
          let c = RAND_CONV (REWR_CONV th') THENC NUM_SUC_CONV in
          (CONV_RULE (RAND_CONV c) th, th' :: ths) in
    rewr_convs;;

let length_conv tm =
    let (th,_) = length_convs tm in
    th;;

let replicate_conv =
    let zero_conv = REWR_CONV REPLICATE_0 in
    let suc_conv = REWR_CONV REPLICATE_SUC in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RAND_CONV num_CONV THENC
          suc_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let nth_conv =
    let zero_conv = REWR_CONV nth_zero in
    let side_conv = RAND_CONV length_conv THENC NUM_LT_CONV in
    let suc_th = SPEC_ALL nth_suc in
    let suc_conv tm =
        let th = PART_MATCH (lhs o rand) suc_th tm in
        let th' = side_conv (lhand (concl th)) in
        MP th (EQT_ELIM th') in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RAND_CONV num_CONV THENC
          suc_conv THENC
          rewr_conv)) tm in
    rewr_conv;;

let take_conv =
    let zero_conv = REWR_CONV take_zero in
    let side_conv = RAND_CONV length_conv THENC NUM_LE_CONV in
    let suc_th = SPEC_ALL take_suc in
    let suc_conv tm =
        let th = PART_MATCH (lhs o rand) suc_th tm in
        let th' = side_conv (lhand (concl th)) in
        MP th (EQT_ELIM th') in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RATOR_CONV (RAND_CONV num_CONV) THENC
          suc_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let drop_conv =
    let zero_conv = REWR_CONV drop_zero in
    let side_conv = RAND_CONV length_conv THENC NUM_LE_CONV in
    let suc_th = SPEC_ALL drop_suc in
    let suc_conv tm =
        let th = PART_MATCH (lhs o rand) suc_th tm in
        let th' = side_conv (lhand (concl th)) in
        MP th (EQT_ELIM th') in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RATOR_CONV (RAND_CONV num_CONV) THENC
          suc_conv THENC
          rewr_conv)) tm in
    rewr_conv;;

let zipwith_conv =
    let nil_conv = REWR_CONV zipwith_nil in
    let side_conv =
        LAND_CONV length_conv THENC
        RAND_CONV length_conv THENC
        NUM_EQ_CONV in
    let cons_th = SPEC_ALL zipwith_cons in
    let cons_conv tm =
        let th = PART_MATCH (lhs o rand) cons_th tm in
        let th' = side_conv (lhand (concl th)) in
        MP th (EQT_ELIM th') in
    fun c ->
      let rec rewr_conv tm =
          (nil_conv ORELSEC
           (cons_conv THENC
            LAND_CONV c THENC
            RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let list_eq_conv =
    let nil_conv = REWR_CONV (EQT_INTRO (ISPEC `[] : A list` EQ_REFL)) in
    let cons_conv = REWR_CONV CONS_11 in
    fun c ->
      let rec rewr_conv tm =
          (nil_conv ORELSEC
           (cons_conv THENC
            RATOR_CONV (RAND_CONV c) THENC
            RAND_CONV rewr_conv THENC
            TRY_CONV and_simp_conv)) tm in
      rewr_conv;;

let list_bit_conv =
    append_conv ORELSEC
    length_conv ORELSEC
    replicate_conv ORELSEC
    nth_conv ORELSEC
    take_conv ORELSEC
    drop_conv ORELSEC
    zipwith_conv ALL_CONV ORELSEC
    list_eq_conv ALL_CONV;;

let bit_blast_subterm_conv = list_bit_conv ORELSEC bit_blast_subterm_conv;;
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;  (* list *)
let bit_blast_tac = CONV_TAC bit_blast_conv;;  (* list *)
