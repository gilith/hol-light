(* ========================================================================= *)
(* ADDER DEVICES                                                             *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of adder devices.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-adder-def";;

(* ------------------------------------------------------------------------- *)
(* Wire adder devices.                                                       *)
(* ------------------------------------------------------------------------- *)

let adder2_def = new_definition
  `!x y s c.
     adder2 x y s c <=>
     xor2 x y s /\ and2 x y c`;;

export_thm adder2_def;;

let adder3_def = new_definition
  `!x y z s c.
     adder3 x y z s c <=>
     xor3 x y z s /\ majority3 x y z c`;;

export_thm adder3_def;;

(* ------------------------------------------------------------------------- *)
(* Bus adder devices.                                                        *)
(* ------------------------------------------------------------------------- *)

(***
let badder2_def = new_definition
  `!x y s c.
     badder2 x y s c <=>
     ?n.
       width x = n /\ width y = n /\
       width s = n /\ width c = n /\
       bxor2 x y s /\ band2 x y c`;;

       !i xi yi si ci.
         wire x i xi /\ wire y i yi /\
         wire s i si /\ wire c i ci ==>
         adder2 xi yi si ci`;;

export_thm badder2_def;;

let badder3_def = new_definition
  `!x y z s c.
     badder3 x y z s c <=>
     ?n.
       width x = n /\ width y = n /\ width z = n /\
       width s = n /\ width c = n /\
       !i xi yi zi si ci.
         wire x i xi /\ wire y i yi /\ wire z i zi /\
         wire s i si /\ wire c i ci ==>
         adder3 xi yi zi si ci`;;

export_thm badder3_def;;

let badder4_def = new_definition
  `!w x y z s c.
     badder4 w x y z s c <=>
     ?n p q p0 p1 q1 z0 z1 s0 s1 s2 c0 c1.
       width w = n + 1 /\
       width x = n + 1 /\
       width y = n + 1 /\
       width z = n + 1 /\
       width s = n + 2 /\
       width c = n + 1 /\
       badder3 w x y p q /\
       bsub p 0 1 p0 /\
       bsub z 0 1 z0 /\
       badder2 p0 z0 s0 c0 /\
       bsub p 1 n p1 /\
       bsub q 0 n q1 /\
       bsub z 1 n z1 /\
       badder3 p1 q1 z1 s1 c1 /\
       bsub q n 1 s2 /\
       s = bappend s0 (bappend s1 s2) /\
       c = bappend c0 c1`;;

export_thm badder4_def;;
***)

(* ------------------------------------------------------------------------- *)
(* Properties of adder devices.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-adder-thm";;

(* ------------------------------------------------------------------------- *)
(* Wire adder devices.                                                       *)
(* ------------------------------------------------------------------------- *)

(***
let badder2_wire = prove
 (`!x y s c i xi yi si ci.
     badder2 x y s c /\
     wire x i xi /\ wire y i yi /\
     wire s i si /\ wire c i ci ==>
     adder2 xi yi si ci`,

export_thm badder2_wire;;

let adder3_right_ground = prove
 (`!x y s c. adder2 x y s c ==> adder3 x y ground s c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder2_def; adder3_def] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC xor3_right_ground THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC majority3_right_ground THEN
   ASM_REWRITE_TAC []]);;

export_thm adder3_right_ground;;

let adder3_signal = prove
 (`!x y z s c t.
     adder3 x y z s c ==>
     bit_to_num (signal x t) + bit_to_num (signal y t) +
     bit_to_num (signal z t) =
     bit_to_num (signal s t) + 2 * bit_to_num (signal c t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `z : wire`; `s : wire`; `t : cycle`]
       xor3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `z : wire`; `c : wire`; `t : cycle`]
       majority3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `signal x t` THEN
  BOOL_CASES_TAC `signal y t` THEN
  BOOL_CASES_TAC `signal z t` THEN
  REWRITE_TAC [bit_to_num_def] THEN
  NUM_REDUCE_TAC);;

export_thm adder3_signal;;

let adder2_signal = prove
 (`!x y s c t.
     adder2 x y s c ==>
     bit_to_num (signal x t) + bit_to_num (signal y t) =
     bit_to_num (signal s t) + 2 * bit_to_num (signal c t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `s : wire`; `c : wire`]
            adder3_right_ground) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL [`x : wire`; `y : wire`; `ground`;
            `s : wire`; `c : wire`; `t : cycle`]
       adder3) THEN
  ASM_REWRITE_TAC [bit_to_num_ground; ADD_0]);;

export_thm adder2_signal;;
***)

(* ------------------------------------------------------------------------- *)
(* Bus adder devices.                                                        *)
(* ------------------------------------------------------------------------- *)

logfile_end ();;
