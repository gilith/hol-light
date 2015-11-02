(* ========================================================================= *)
(* PROOF TOOLS FOR HARDWARE BUS DEVICES                                      *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

let mk_wire =
    let wire_tm = `wire` in
    fun x -> fun i -> fun xi ->
    mk_comb (mk_comb (mk_comb (wire_tm,x), i), xi);;

let dest_wire =
    let wire_tm = `wire` in
    fun tm ->
    let (tm,xi) = dest_comb tm in
    let (tm,i) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = wire_tm then (x,i,xi) else failwith "dest_wire";;

let mk_brev =
    let brev_tm = `brev` in
    fun x -> fun y ->
    mk_comb (mk_comb (brev_tm,x), y);;

let dest_brev =
    let brev_tm = `brev` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = brev_tm then (x,y) else failwith "dest_brev";;

let is_brev = can dest_brev;;

let mk_bconnect =
    let bconnect_tm = `bconnect` in
    fun x -> fun y ->
    mk_comb (mk_comb (bconnect_tm,x), y);;

let dest_bconnect =
    let bconnect_tm = `bconnect` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = bconnect_tm then (x,y) else failwith "dest_bconnect";;

let is_bconnect = can dest_bconnect;;

let mk_bdelay =
    let bdelay_tm = `bdelay` in
    fun x -> fun y ->
    mk_comb (mk_comb (bdelay_tm,x), y);;

let dest_bdelay =
    let bdelay_tm = `bdelay` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = bdelay_tm then (x,y) else failwith "dest_bdelay";;

let is_bdelay = can dest_bdelay;;

let mk_bnot =
    let bnot_tm = `bnot` in
    fun x -> fun y ->
    mk_comb (mk_comb (bnot_tm,x), y);;

let dest_bnot =
    let bnot_tm = `bnot` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = bnot_tm then (x,y) else failwith "dest_bnot";;

let is_bnot = can dest_bnot;;

let mk_band2 =
    let band2_tm = `band2` in
    fun x -> fun y -> fun z ->
    mk_comb (mk_comb (mk_comb (band2_tm,x), y), z);;

let dest_band2 =
    let band2_tm = `band2` in
    fun tm ->
    let (tm,z) = dest_comb tm in
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = band2_tm then (x,y,z) else failwith "dest_band2";;

let is_band2 = can dest_band2;;

let mk_bor2 =
    let bor2_tm = `bor2` in
    fun x -> fun y -> fun z ->
    mk_comb (mk_comb (mk_comb (bor2_tm,x), y), z);;

let dest_bor2 =
    let bor2_tm = `bor2` in
    fun tm ->
    let (tm,z) = dest_comb tm in
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = bor2_tm then (x,y,z) else failwith "dest_bor2";;

let is_bor2 = can dest_bor2;;

let mk_bxor2 =
    let bxor2_tm = `bxor2` in
    fun x -> fun y -> fun z ->
    mk_comb (mk_comb (mk_comb (bxor2_tm,x), y), z);;

let dest_bxor2 =
    let bxor2_tm = `bxor2` in
    fun tm ->
    let (tm,z) = dest_comb tm in
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = bxor2_tm then (x,y,z) else failwith "dest_bxor2";;

let is_bxor2 = can dest_bxor2;;

let mk_bcase1 =
    let bcase1_tm = `bcase1` in
    fun s -> fun x -> fun y -> fun z ->
    mk_comb (mk_comb (mk_comb (mk_comb (bcase1_tm,s), x), y), z);;

let dest_bcase1 =
    let bcase1_tm = `bcase1` in
    fun tm ->
    let (tm,z) = dest_comb tm in
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    let (tm,s) = dest_comb tm in
    if tm = bcase1_tm then (s,x,y,z) else failwith "dest_bcase1";;

let is_bcase1 = can dest_bcase1;;

(* ------------------------------------------------------------------------- *)
(* Automatically synthesizing hardware.                                      *)
(* ------------------------------------------------------------------------- *)

let band3_syn =
    let syn = prove
      (`!w x y z.
           band3 w x y z <=>
           ?n wx.
             width w = n /\
             width wx = n /\
             band2 w x wx /\
             band2 wx y z`,
       REPEAT GEN_TAC THEN
       EQ_TAC THENL
       [STRIP_TAC THEN
        MP_TAC
          (SPECL
             [`w : bus`; `x : bus`; `y : bus`; `z : bus`]
             band3_width) THEN
        ASM_REWRITE_TAC [] THEN
        POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [band3_def]) THEN
        STRIP_TAC THEN
        EXISTS_TAC `n : num` THEN
        EXISTS_TAC `wx : bus` THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC band2_width_out THEN
        EXISTS_TAC `w : bus` THEN
        EXISTS_TAC `x : bus` THEN
        ASM_REWRITE_TAC [];
        STRIP_TAC THEN
        REWRITE_TAC [band3_def] THEN
        EXISTS_TAC `wx : bus` THEN
        ASM_REWRITE_TAC []]) in
    [("and3b",syn)];;

let bor3_syn =
    let syn = prove
      (`!w x y z.
           bor3 w x y z <=>
           ?n wx.
             width w = n /\
             width wx = n /\
             bor2 w x wx /\
             bor2 wx y z`,
       REPEAT GEN_TAC THEN
       EQ_TAC THENL
       [STRIP_TAC THEN
        MP_TAC
          (SPECL
             [`w : bus`; `x : bus`; `y : bus`; `z : bus`]
             bor3_width) THEN
        ASM_REWRITE_TAC [] THEN
        POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [bor3_def]) THEN
        STRIP_TAC THEN
        EXISTS_TAC `n : num` THEN
        EXISTS_TAC `wx : bus` THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC bor2_width_out THEN
        EXISTS_TAC `w : bus` THEN
        EXISTS_TAC `x : bus` THEN
        ASM_REWRITE_TAC [];
        STRIP_TAC THEN
        REWRITE_TAC [bor3_def] THEN
        EXISTS_TAC `wx : bus` THEN
        ASM_REWRITE_TAC []]) in
    [("or3b",syn)];;

let bxor3_syn =
    let syn = prove
      (`!w x y z.
           bxor3 w x y z <=>
           ?n wx.
             width w = n /\
             width wx = n /\
             bxor2 w x wx /\
             bxor2 wx y z`,
       REPEAT GEN_TAC THEN
       EQ_TAC THENL
       [STRIP_TAC THEN
        MP_TAC
          (SPECL
             [`w : bus`; `x : bus`; `y : bus`; `z : bus`]
             bxor3_width) THEN
        ASM_REWRITE_TAC [] THEN
        POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [bxor3_def]) THEN
        STRIP_TAC THEN
        EXISTS_TAC `n : num` THEN
        EXISTS_TAC `wx : bus` THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC bxor2_width_out THEN
        EXISTS_TAC `w : bus` THEN
        EXISTS_TAC `x : bus` THEN
        ASM_REWRITE_TAC [];
        STRIP_TAC THEN
        REWRITE_TAC [bxor3_def] THEN
        EXISTS_TAC `wx : bus` THEN
        ASM_REWRITE_TAC []]) in
    [("xor3b",syn)];;

let bmajority3_syn =
    let syn = prove
      (`!w x y z.
           bmajority3 w x y z <=>
           ?n wx wy xy.
             width w = n /\
             width wx = n /\
             width wy = n /\
             width xy = n /\
             band2 w x wx /\
             band2 w y wy /\
             band2 x y xy /\
             bor3 wx wy xy z`,
       REPEAT GEN_TAC THEN
       EQ_TAC THENL
       [STRIP_TAC THEN
        MP_TAC
          (SPECL
             [`w : bus`; `x : bus`; `y : bus`; `z : bus`]
             bmajority3_width) THEN
        ASM_REWRITE_TAC [] THEN
        POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [bmajority3_def]) THEN
        STRIP_TAC THEN
        EXISTS_TAC `n : num` THEN
        EXISTS_TAC `wx : bus` THEN
        EXISTS_TAC `wy : bus` THEN
        EXISTS_TAC `xy : bus` THEN
        ASM_REWRITE_TAC [] THEN
        REPEAT CONJ_TAC THENL
        [MATCH_MP_TAC band2_width_out THEN
         EXISTS_TAC `w : bus` THEN
         EXISTS_TAC `x : bus` THEN
         ASM_REWRITE_TAC [];
         MATCH_MP_TAC band2_width_out THEN
         EXISTS_TAC `w : bus` THEN
         EXISTS_TAC `y : bus` THEN
         ASM_REWRITE_TAC [];
         MATCH_MP_TAC band2_width_out THEN
         EXISTS_TAC `x : bus` THEN
         EXISTS_TAC `y : bus` THEN
         ASM_REWRITE_TAC []];
        STRIP_TAC THEN
        REWRITE_TAC [bmajority3_def] THEN
        EXISTS_TAC `wx : bus` THEN
        EXISTS_TAC `wy : bus` THEN
        EXISTS_TAC `xy : bus` THEN
        ASM_REWRITE_TAC []]) in
    setify (("maj3b",syn) :: bor3_syn);;
