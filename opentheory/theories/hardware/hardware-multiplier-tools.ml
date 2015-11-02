(* ========================================================================= *)
(* PROOF TOOLS FOR HARDWARE MULTIPLIER DEVICES                               *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Automatically synthesizing hardware.                                      *)
(* ------------------------------------------------------------------------- *)

let bmult_syn =
    setify (("mulb",bmult_def) :: adder2_syn @ badder3_syn @ adder3_syn);;

let scmult_syn =
    setify
      (("mulsc",scmult_def) ::
       scshiftr_syn @ pipe_syn @ bmult_syn);;
