(* ========================================================================= *)
(* HARDWARE WIRE DEVICES                                                     *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of hardware wire devices.                                      *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-wire-def";;

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

let nor2_def = new_definition
  `!x y z.
     nor2 x y z <=>
     ?zn. or2 x y zn /\ not zn z`;;

export_thm nor2_def;;

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

let sticky_def = new_definition
  `!ld w x.
     sticky ld w x <=>
     ?p q r.
       case1 ld ground p q /\
       or2 w q r /\
       delay r p /\
       connect r x`;;

export_thm sticky_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of hardware wire devices.                                      *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-wire-thm";;

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
  REWRITE_TAC [mk_wire_signal; stream_snth; ADD_SUB; ADD_EQ_0; ONE; NOT_SUC]);;

export_thm delay_exists;;

let delay_ground = prove
 (`!x. connect ground x ==> delay ground x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [delay_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`ground`; `x : wire`; `t + 1`] connect_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm delay_ground;;

let delay_power = prove
 (`!x. connect power x ==> delay power x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [delay_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`power`; `x : wire`; `t + 1`] connect_signal) THEN
  ASM_REWRITE_TAC [power_signal]);;

export_thm delay_power;;

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
  REWRITE_TAC [mk_wire_signal; stream_snth]);;

export_thm not_exists;;

let not_ground = prove
 (`!x. connect power x ==> not ground x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [not_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`power`; `x : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [power_signal; ground_signal]);;

export_thm not_ground;;

let not_power = prove
 (`!x. connect ground x ==> not power x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [not_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`ground`; `x : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [power_signal; ground_signal]);;

export_thm not_power;;

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
  REWRITE_TAC [mk_wire_signal; stream_snth]);;

export_thm and2_exists;;

let and2_left_ground = prove
 (`!x y. connect ground y ==> and2 ground x y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [and2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`ground`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm and2_left_ground;;

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

let and2_right_power = prove
 (`!x y. connect x y ==> and2 x power y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [and2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [power_signal]);;

export_thm and2_right_power;;

let and2_refl = prove
 (`!x y. connect x y ==> and2 x x y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [and2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC []);;

export_thm and2_refl;;

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
  REWRITE_TAC [mk_wire_signal; stream_snth]);;

export_thm or2_exists;;

let or2_left_ground = prove
 (`!x y. connect x y ==> or2 ground x y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [or2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm or2_left_ground;;

let or2_right_ground = prove
 (`!x y. connect x y ==> or2 x ground y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [or2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm or2_right_ground;;

let or2_left_power = prove
 (`!x y. connect power y ==> or2 power x y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [or2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`power`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [power_signal]);;

export_thm or2_left_power;;

let or2_right_power = prove
 (`!x y. connect power y ==> or2 x power y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [or2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`power`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [power_signal]);;

export_thm or2_right_power;;

let or2_refl = prove
 (`!x y. connect x y ==> or2 x x y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [or2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC []);;

export_thm or2_refl;;

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
  REWRITE_TAC [mk_wire_signal; stream_snth]);;

export_thm xor2_exists;;

let xor2_left_ground = prove
 (`!x y. connect x y ==> xor2 ground x y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [xor2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm xor2_left_ground;;

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

let xor2_right_power = prove
 (`!x y. not x y ==> xor2 x power y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [xor2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `t : cycle`] not_signal) THEN
  ASM_REWRITE_TAC [power_signal]);;

export_thm xor2_right_power;;

let xor2_refl = prove
 (`!x y. connect ground y ==> xor2 x x y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [xor2_def] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`ground`; `y : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm xor2_refl;;

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
  REWRITE_TAC [mk_wire_signal; stream_snth]);;

export_thm case1_exists;;

let case1_left_ground = prove
 (`!x y z. connect y z ==> case1 ground x y z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [case1_def] THEN
  GEN_TAC THEN
  MP_TAC
    (SPECL [`y : wire`; `z : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm case1_left_ground;;

let case1_left_power = prove
 (`!x y z. connect x z ==> case1 power x y z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [case1_def] THEN
  GEN_TAC THEN
  MP_TAC
    (SPECL [`x : wire`; `z : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC [power_signal]);;

export_thm case1_left_power;;

let case1_middle_ground = prove
 (`!x y z xn. not x xn /\ and2 xn y z ==> case1 x ground y z`,
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

let case1_right_ground = prove
 (`!x y z. and2 x y z ==> case1 x y ground z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [case1_def] THEN
  GEN_TAC THEN
  MP_TAC
    (SPECL [`x : wire`; `y : wire`; `z : wire`; `t : cycle`] and2_signal) THEN
  COND_CASES_TAC THEN
  BOOL_CASES_TAC `signal x t` THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm case1_right_ground;;

let case1_right_power = prove
 (`!x y z xn. not x xn /\ or2 xn y z ==> case1 x y power z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [case1_def] THEN
  GEN_TAC THEN
  MP_TAC
    (SPECL [`x : wire`; `xn : wire`; `t : cycle`] not_signal) THEN
  MP_TAC
    (SPECL [`xn : wire`; `y : wire`; `z : wire`; `t : cycle`] or2_signal) THEN
  COND_CASES_TAC THEN
  BOOL_CASES_TAC `signal xn t` THEN
  ASM_REWRITE_TAC [power_signal]);;

export_thm case1_right_power;;

let case1_middle_ground_right_power = prove
 (`!x y. not x y ==> case1 x ground power y`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC case1_middle_ground THEN
  EXISTS_TAC `y : wire` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC and2_right_power THEN
  REWRITE_TAC [connect_refl]);;

export_thm case1_middle_ground_right_power;;

let case1_middle_power_right_ground = prove
 (`!x y. connect x y ==> case1 x power ground y`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC case1_middle_power THEN
  MATCH_MP_TAC or2_right_ground THEN
  ASM_REWRITE_TAC []);;

export_thm case1_middle_power_right_ground;;

let case1_refl = prove
 (`!x y z. connect y z ==> case1 x y y z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [case1_def; COND_ID] THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`y : wire`; `z : wire`; `t : cycle`] connect_signal) THEN
  ASM_REWRITE_TAC []);;

export_thm case1_refl;;

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

let pulse_signal_false = prove
 (`!x y t. pulse x y /\ ~signal x t ==> ~signal y t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pulse_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : wire`; `xn : wire`; `y : wire`; `t : cycle`]
       and2_signal) THEN
  ASM_REWRITE_TAC []);;

export_thm pulse_signal_false;;

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

let nor2_signal = prove
 (`!x y z t.
     nor2 x y z ==>
     signal z t = (~signal x t /\ ~signal y t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [nor2_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`zn : wire`; `z : wire`; `t : cycle`]
       not_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `zn : wire`; `t : cycle`]
       or2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [DE_MORGAN_THM]);;

export_thm nor2_signal;;

let nor2_exists = prove
 (`!x y. ?z. nor2 x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [nor2_def] THEN
  X_CHOOSE_THEN `zn : wire` STRIP_ASSUME_TAC
    (SPECL [`x : wire`; `y : wire`] or2_exists) THEN
  X_CHOOSE_THEN `z : wire` STRIP_ASSUME_TAC
    (SPECL [`zn : wire`] not_exists) THEN
  EXISTS_TAC `z : wire` THEN
  EXISTS_TAC `zn : wire` THEN
  ASM_REWRITE_TAC []);;

export_thm nor2_exists;;

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

let sticky_signal = prove
 (`!ld w x t k.
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     sticky ld w x ==>
     (signal x (t + k) <=> ?i. i <= k /\ signal w (t + i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [sticky_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`r : wire`;
        `x : wire`;
        `t + k : cycle`]
       connect_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `!i. i <= k ==> (signal ld (t + i) <=> i = 0)` THEN
  SPEC_TAC (`k : cycle`, `k : cycle`) THEN
  INDUCT_TAC THENL
  [DISCH_THEN (MP_TAC o SPEC `0`) THEN
   REWRITE_TAC [ADD_0; LE_ZERO; UNWIND_THM2] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`w : wire`;
         `q : wire`;
         `r : wire`;
         `t : cycle`]
        or2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `ground`;
         `p : wire`;
         `q : wire`;
         `t : cycle`]
        case1_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [ground_signal];
   ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`w : wire`;
        `q : wire`;
        `r : wire`;
        `t + SUC k : cycle`]
       or2_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [LE; RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  AP_TERM_TAC THEN
  MP_TAC
    (SPECL
       [`ld : wire`;
        `ground`;
        `p : wire`;
        `q : wire`;
        `t + SUC k : cycle`]
       case1_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM (MP_TAC o SPEC `SUC k`) THEN
  REWRITE_TAC [LE_REFL; NOT_SUC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC
    (SPECL
       [`r : wire`;
        `p : wire`;
        `t + k : cycle`]
       delay_signal) THEN
  ASM_REWRITE_TAC [GSYM ADD1; ADD_SUC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `k : cycle` THEN
  ASM_REWRITE_TAC [SUC_LE]);;

export_thm sticky_signal;;

(* ------------------------------------------------------------------------- *)
(* Proof tools.                                                              *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-wire-tools.ml";;
