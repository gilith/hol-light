(* ========================================================================= *)
(* HARDWARE WIRE DEVICES                                                     *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of hardware wire devices.                                      *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-wire-def";;

(* ~~~~~~~~~~~~~~~~~~~~~~ *)
(* Primitive wire devices *)
(* ~~~~~~~~~~~~~~~~~~~~~~ *)

let connect_def = new_definition
  `!x y.
     connect x y <=>
     !t. signal y t = signal x t`;;

export_thm connect_def;;

let delay_def = new_definition
  `!x y.
     delay x y <=>
     !t. signal y (t + 1) = signal x t`;;

export_thm delay_def;;

let not_def = new_definition
  `!x y.
     not x y <=>
     !t. signal y t = ~signal x t`;;

export_thm not_def;;

let and2_def = new_definition
  `!x y z.
     and2 x y z <=>
     !t. signal z t = (signal x t /\ signal y t)`;;

export_thm and2_def;;

let or2_def = new_definition
  `!x y z.
     or2 x y z <=>
     !t. signal z t = (signal x t \/ signal y t)`;;

export_thm or2_def;;

let xor2_def = new_definition
  `!x y z.
     xor2 x y z <=>
     !t. signal z t = ~(signal x t = signal y t)`;;

export_thm xor2_def;;

let case1_def = new_definition
  `!s x y z.
     case1 s x y z <=>
     !t. signal z t = (if signal s t then signal x t else signal y t)`;;

export_thm case1_def;;

(* ~~~~~~~~~~~~~~~~~~~~ *)
(* Derived wire devices *)
(* ~~~~~~~~~~~~~~~~~~~~ *)

let pulse_def = new_definition
  `!x y.
     pulse x y <=>
     ?xd xn. delay x xd /\ not xd xn /\ and2 x xn y`;;

export_thm pulse_def;;

let and3_def = new_definition
  `!w x y z.
     and3 w x y z <=>
     ?wx. and2 w x wx /\ and2 wx y z`;;

export_thm and3_def;;

let or3_def = new_definition
  `!w x y z.
     or3 w x y z <=>
     ?wx. or2 w x wx /\ or2 wx y z`;;

export_thm or3_def;;

let xor3_def = new_definition
  `!w x y z.
     xor3 w x y z <=>
     ?wx. xor2 w x wx /\ xor2 wx y z`;;

export_thm xor3_def;;

let majority3_def = new_definition
  `!w x y z.
     majority3 w x y z <=>
     ?wx wy xy.
       and2 w x wx /\ and2 w y wy /\ and2 x y xy /\
       or3 wx wy xy z`;;

export_thm majority3_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of hardware wire devices.                                      *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-wire-thm";;

(* ~~~~~~~~~~~~~~~~~~~~~~ *)
(* Primitive wire devices *)
(* ~~~~~~~~~~~~~~~~~~~~~~ *)

let connect_signal = prove
 (`!x y t.
     connect x y ==>
     signal y t = signal x t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [connect_def]));;

export_thm connect_signal;;

let connect_refl = prove
 (`!x. connect x x`,
  REWRITE_TAC [connect_def]);;

export_thm connect_refl;;

let connect_exists = prove
 (`!x. ?y. connect x y`,
  GEN_TAC THEN
  EXISTS_TAC `x : wire` THEN
  MATCH_ACCEPT_TAC connect_refl);;

export_thm connect_exists;;

let delay_signal = prove
 (`!x y t.
     delay x y ==>
     signal y (t + 1) = signal x t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [delay_def]));;

export_thm delay_signal;;

let delay_exists = prove
 (`!x. ?y. delay x y`,
  GEN_TAC THEN
  REWRITE_TAC [delay_def] THEN
  EXISTS_TAC `mk_wire (stream (\t. t = 0 \/ signal x (t - 1)))` THEN
  GEN_TAC THEN
  REWRITE_TAC
    [mk_wire_signal; stream_tybij; ADD_SUB; ADD_EQ_0; ONE; NOT_SUC]);;

export_thm delay_exists;;

let not_signal = prove
 (`!x y t.
     not x y ==>
     signal y t = ~signal x t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [not_def]));;

export_thm not_signal;;

let not_exists = prove
 (`!x. ?y. not x y`,
  GEN_TAC THEN
  REWRITE_TAC [not_def] THEN
  EXISTS_TAC `mk_wire (stream (\t. ~signal x t))` THEN
  GEN_TAC THEN
  REWRITE_TAC [mk_wire_signal; stream_tybij]);;

export_thm not_exists;;

let and2_signal = prove
 (`!x y z t.
     and2 x y z ==>
     signal z t = (signal x t /\ signal y t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [and2_def]));;

export_thm and2_signal;;

let and2_exists = prove
 (`!x y. ?z. and2 x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [and2_def] THEN
  EXISTS_TAC `mk_wire (stream (\t. signal x t /\ signal y t))` THEN
  GEN_TAC THEN
  REWRITE_TAC [mk_wire_signal; stream_tybij]);;

export_thm and2_exists;;

let and2_right_ground = prove
 (`!x y. connect ground y ==> and2 x ground y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [and2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`ground`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm and2_right_ground;;

let and2_left_power = prove
 (`!x y. connect x y ==> and2 power x y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [and2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [power_signal]);;

export_thm and2_left_power;;

let or2_signal = prove
 (`!x y z t.
     or2 x y z ==>
     signal z t = (signal x t \/ signal y t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [or2_def]));;

export_thm or2_signal;;

let or2_exists = prove
 (`!x y. ?z. or2 x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [or2_def] THEN
  EXISTS_TAC `mk_wire (stream (\t. signal x t \/ signal y t))` THEN
  GEN_TAC THEN
  REWRITE_TAC [mk_wire_signal; stream_tybij]);;

export_thm or2_exists;;

let or2_right_ground = prove
 (`!x y. connect x y ==> or2 x ground y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [or2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm or2_right_ground;;

let xor2_signal = prove
 (`!x y z t.
     xor2 x y z ==>
     signal z t = ~(signal x t = signal y t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [xor2_def]));;

export_thm xor2_signal;;

let xor2_exists = prove
 (`!x y. ?z. xor2 x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [xor2_def] THEN
  EXISTS_TAC `mk_wire (stream (\t. ~(signal x t <=> signal y t)))` THEN
  GEN_TAC THEN
  REWRITE_TAC [mk_wire_signal; stream_tybij]);;

export_thm xor2_exists;;

let xor2_right_ground = prove
 (`!x y. connect x y ==> xor2 x ground y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [xor2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm xor2_right_ground;;

let xor2_left_power = prove
 (`!x y. not x y ==> xor2 power x y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [xor2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] not_signal) THEN
  ASM_REWRITE_TAC [power_signal]);;

export_thm xor2_left_power;;

let case1_signal = prove
 (`!s x y z t.
     case1 s x y z ==>
     signal z t = (if signal s t then signal x t else signal y t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [case1_def]));;

export_thm case1_signal;;

let case1_exists = prove
 (`!s x y. ?z. case1 s x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [case1_def] THEN
  EXISTS_TAC
    `mk_wire
       (stream (\t. if signal s t then signal x t else signal y t))` THEN
  GEN_TAC THEN
  REWRITE_TAC [mk_wire_signal; stream_tybij]);;

export_thm case1_exists;;

let case1_middle_ground = prove
 (`!x y z. (?xn. not x xn /\ and2 xn y z) ==> case1 x ground y z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [case1_def] THEN
  GEN_TAC THEN
  MP_TAC
    (SPECL [`x : wire`; `xn : wire`; `t : cycle`] not_signal) THEN
  MP_TAC
    (SPECL [`xn : wire`; `y : wire`; `z : wire`; `t : cycle`] and2_signal) THEN
  COND_CASES_TAC THEN
  BOOL_CASES_TAC `signal xn t` THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm case1_middle_ground;;

let case1_middle_power = prove
 (`!x y z. or2 x y z ==> case1 x power y z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [case1_def] THEN
  GEN_TAC THEN
  MP_TAC
    (SPECL [`x : wire`; `y : wire`; `z : wire`; `t : cycle`] or2_signal) THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC [power_signal]);;

export_thm case1_middle_power;;

(* ~~~~~~~~~~~~~~~~~~~~ *)
(* Derived wire devices *)
(* ~~~~~~~~~~~~~~~~~~~~ *)

let pulse_signal = prove
 (`!x y t.
     pulse x y ==>
     signal y (t + 1) = (~signal x t /\ signal x (t + 1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pulse_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : wire`; `xn : wire`; `y : wire`; `t + 1 : cycle`]
       and2_signal) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REVERSE_TAC (ASM_CASES_TAC `signal x (t + 1)`) THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC
    (SPECL
       [`xd : wire`; `xn : wire`; `t + 1 : cycle`]
       not_signal) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC delay_signal THEN
  ASM_REWRITE_TAC []);;

export_thm pulse_signal;;

let pulse_exists = prove
 (`!x. ?y. pulse x y`,
  GEN_TAC THEN
  REWRITE_TAC [pulse_def] THEN
  X_CHOOSE_THEN `xd : wire` STRIP_ASSUME_TAC
    (SPECL [`x : wire`] delay_exists) THEN
  X_CHOOSE_THEN `xn : wire` STRIP_ASSUME_TAC
    (SPECL [`xd : wire`] not_exists) THEN
  X_CHOOSE_THEN `y : wire` STRIP_ASSUME_TAC
    (SPECL [`x : wire`; `xn : wire`] and2_exists) THEN
  EXISTS_TAC `y : wire` THEN
  EXISTS_TAC `xd : wire` THEN
  EXISTS_TAC `xn : wire` THEN
  ASM_REWRITE_TAC []);;

export_thm pulse_exists;;

let and3_signal = prove
 (`!w x y z t.
     and3 w x y z ==>
     signal z t = (signal w t /\ signal x t /\ signal y t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [and3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`wx : wire`; `y : wire`; `z : wire`; `t : cycle`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`w : wire`; `x : wire`; `wx : wire`; `t : cycle`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [CONJ_ASSOC]);;

export_thm and3_signal;;

let and3_exists = prove
 (`!w x y. ?z. and3 w x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [and3_def] THEN
  X_CHOOSE_THEN `wx : wire` STRIP_ASSUME_TAC
    (SPECL [`w : wire`; `x : wire`] and2_exists) THEN
  X_CHOOSE_THEN `z : wire` STRIP_ASSUME_TAC
    (SPECL [`wx : wire`; `y : wire`] and2_exists) THEN
  EXISTS_TAC `z : wire` THEN
  EXISTS_TAC `wx : wire` THEN
  ASM_REWRITE_TAC []);;

export_thm and3_exists;;

let or3_signal = prove
 (`!w x y z t.
     or3 w x y z ==>
     signal z t = (signal w t \/ signal x t \/ signal y t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [or3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`wx : wire`; `y : wire`; `z : wire`; `t : cycle`]
       or2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`w : wire`; `x : wire`; `wx : wire`; `t : cycle`]
       or2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [DISJ_ASSOC]);;

export_thm or3_signal;;

let or3_exists = prove
 (`!w x y. ?z. or3 w x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [or3_def] THEN
  X_CHOOSE_THEN `wx : wire` STRIP_ASSUME_TAC
    (SPECL [`w : wire`; `x : wire`] or2_exists) THEN
  X_CHOOSE_THEN `z : wire` STRIP_ASSUME_TAC
    (SPECL [`wx : wire`; `y : wire`] or2_exists) THEN
  EXISTS_TAC `z : wire` THEN
  EXISTS_TAC `wx : wire` THEN
  ASM_REWRITE_TAC []);;

export_thm or3_exists;;

let or3_right_ground = prove
 (`!x y z. or2 x y z ==> or3 x y ground z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [or3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `z : wire` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC or2_right_ground THEN
  MATCH_ACCEPT_TAC connect_refl);;

export_thm or3_right_ground;;

let xor3_signal = prove
 (`!w x y z t.
     xor3 w x y z ==>
     signal z t = (signal w t = (signal x t = signal y t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [xor3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`wx : wire`; `y : wire`; `z : wire`; `t : cycle`]
       xor2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`w : wire`; `x : wire`; `wx : wire`; `t : cycle`]
       xor2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `signal w t` THEN
  BOOL_CASES_TAC `signal x t` THEN
  REWRITE_TAC []);;

export_thm xor3_signal;;

let xor3_exists = prove
 (`!w x y. ?z. xor3 w x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [xor3_def] THEN
  X_CHOOSE_THEN `wx : wire` STRIP_ASSUME_TAC
    (SPECL [`w : wire`; `x : wire`] xor2_exists) THEN
  X_CHOOSE_THEN `z : wire` STRIP_ASSUME_TAC
    (SPECL [`wx : wire`; `y : wire`] xor2_exists) THEN
  EXISTS_TAC `z : wire` THEN
  EXISTS_TAC `wx : wire` THEN
  ASM_REWRITE_TAC []);;

export_thm xor3_exists;;

let xor3_right_ground = prove
 (`!x y z. xor2 x y z ==> xor3 x y ground z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [xor3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `z : wire` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC xor2_right_ground THEN
  MATCH_ACCEPT_TAC connect_refl);;

export_thm xor3_right_ground;;

let majority3_signal = prove
 (`!w x y z t.
     majority3 w x y z ==>
     signal z t =
     ((signal w t /\ signal x t) \/
      (signal w t /\ signal y t) \/
      (signal x t /\ signal y t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [majority3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`w : wire`; `x : wire`; `wx : wire`; `t : cycle`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`w : wire`; `y : wire`; `wy : wire`; `t : cycle`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `xy : wire`; `t : cycle`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`wx : wire`; `wy : wire`; `xy : wire`; `z : wire`; `t : cycle`]
       or3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC []);;

export_thm majority3_signal;;

let majority3_exists = prove
 (`!w x y. ?z. majority3 w x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [majority3_def] THEN
  X_CHOOSE_THEN `wx : wire` STRIP_ASSUME_TAC
    (SPECL [`w : wire`; `x : wire`] and2_exists) THEN
  X_CHOOSE_THEN `wy : wire` STRIP_ASSUME_TAC
    (SPECL [`w : wire`; `y : wire`] and2_exists) THEN
  X_CHOOSE_THEN `xy : wire` STRIP_ASSUME_TAC
    (SPECL [`x : wire`; `y : wire`] and2_exists) THEN
  X_CHOOSE_THEN `z : wire` STRIP_ASSUME_TAC
    (SPECL [`wx : wire`; `wy : wire`; `xy : wire`] or3_exists) THEN
  EXISTS_TAC `z : wire` THEN
  EXISTS_TAC `wx : wire` THEN
  EXISTS_TAC `wy : wire` THEN
  EXISTS_TAC `xy : wire` THEN
  ASM_REWRITE_TAC []);;

export_thm majority3_exists;;

let majority3_right_ground = prove
 (`!x y z. and2 x y z ==> majority3 x y ground z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [majority3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `z : wire` THEN
  EXISTS_TAC `ground` THEN
  EXISTS_TAC `ground` THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC and2_right_ground THEN
   MATCH_ACCEPT_TAC connect_refl;
   MATCH_MP_TAC and2_right_ground THEN
   MATCH_ACCEPT_TAC connect_refl;
   MATCH_MP_TAC or3_right_ground THEN
   MATCH_MP_TAC or2_right_ground THEN
   MATCH_ACCEPT_TAC connect_refl]);;

export_thm majority3_right_ground;;

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

let mk_delay =
    let delay_tm = `delay` in
    fun x -> fun y ->
    mk_comb (mk_comb (delay_tm,x), y);;

let dest_delay =
    let delay_tm = `delay` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = delay_tm then (x,y) else failwith "dest_delay";;

let is_delay = can dest_delay;;

let mk_not =
    let not_tm = `not` in
    fun x -> fun y ->
    mk_comb (mk_comb (not_tm,x), y);;

let dest_not =
    let not_tm = `not` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = not_tm then (x,y) else failwith "dest_not";;

let is_not = can dest_not;;

let mk_and2 =
    let and2_tm = `and2` in
    fun x -> fun y -> fun z ->
    mk_comb (mk_comb (mk_comb (and2_tm,x), y), z);;

let dest_and2 =
    let and2_tm = `and2` in
    fun tm ->
    let (tm,z) = dest_comb tm in
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = and2_tm then (x,y,z) else failwith "dest_and2";;

let is_and2 = can dest_and2;;

let mk_or2 =
    let or2_tm = `or2` in
    fun x -> fun y -> fun z ->
    mk_comb (mk_comb (mk_comb (or2_tm,x), y), z);;

let dest_or2 =
    let or2_tm = `or2` in
    fun tm ->
    let (tm,z) = dest_comb tm in
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = or2_tm then (x,y,z) else failwith "dest_or2";;

let is_or2 = can dest_or2;;

let mk_xor2 =
    let xor2_tm = `xor2` in
    fun x -> fun y -> fun z ->
    mk_comb (mk_comb (mk_comb (xor2_tm,x), y), z);;

let dest_xor2 =
    let xor2_tm = `xor2` in
    fun tm ->
    let (tm,z) = dest_comb tm in
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = xor2_tm then (x,y,z) else failwith "dest_xor2";;

let is_xor2 = can dest_xor2;;

logfile_end ();;
