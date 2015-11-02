(* ========================================================================= *)
(* PROOF TOOLS FOR HARDWARE ADDER DEVICES                                    *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Automatically synthesizing hardware.                                      *)
(* ------------------------------------------------------------------------- *)

let adder2_syn = [("add2",adder2_def)];;

let adder3_syn =
    setify (("add3",adder3_def) :: xor3_syn @ majority3_syn);;

let badder2_syn = [("add2b",badder2_def)];;

let badder3_syn =
    setify (("add3b",badder3_def) :: bxor3_syn @ bmajority3_syn);;

let scshiftr_syn =
    setify (("shrsc",scshiftr_def) :: badder2_syn);;
