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

let delay_signal = prove
  (`!x y t.
      delay x y ==>
      signal y (t + 1) = signal x t`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [delay_def]));;

export_thm delay_signal;;

let not_signal = prove
  (`!x y t.
      not x y ==>
      signal y t = ~signal x t`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [not_def]));;

export_thm not_signal;;

let and2_signal = prove
  (`!x y z t.
      and2 x y z ==>
      signal z t = (signal x t /\ signal y t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [and2_def]));;

export_thm and2_signal;;

let and2_right_ground = prove
 (`!x y. y = ground ==> and2 x ground y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [and2_def; ground_signal]);;

export_thm and2_right_ground;;

let or2_signal = prove
  (`!x y z t.
      or2 x y z ==>
      signal z t = (signal x t \/ signal y t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [or2_def]));;

export_thm or2_signal;;

let or2_right_ground = prove
 (`!x y. y = x ==> or2 x ground y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [or2_def; ground_signal]);;

export_thm or2_right_ground;;

let xor2_signal = prove
  (`!x y z t.
      xor2 x y z ==>
      signal z t = ~(signal x t = signal y t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [xor2_def]));;

export_thm xor2_signal;;

let xor2_right_ground = prove
 (`!x y. y = x ==> xor2 x ground y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [xor2_def; ground_signal]);;

export_thm xor2_right_ground;;

let case1_signal = prove
  (`!s x y z t.
      case1 s x y z ==>
      signal z t = (if signal s t then signal x t else signal y t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [case1_def]));;

export_thm case1_signal;;

(* ~~~~~~~~~~~~~~~~~~~~ *)
(* Derived wire devices *)
(* ~~~~~~~~~~~~~~~~~~~~ *)

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

let or3_right_ground = prove
 (`!x y z. or2 x y z ==> or3 x y ground z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [or3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `z : wire` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC or2_right_ground THEN
  REFL_TAC);;

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

let xor3_right_ground = prove
 (`!x y z. xor2 x y z ==> xor3 x y ground z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [xor3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `z : wire` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC xor2_right_ground THEN
  REFL_TAC);;

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
   REFL_TAC;
   MATCH_MP_TAC and2_right_ground THEN
   REFL_TAC;
   MATCH_MP_TAC or3_right_ground THEN
   MATCH_MP_TAC or2_right_ground THEN
   REFL_TAC]);;

export_thm majority3_right_ground;;

logfile_end ();;
