(* ========================================================================= *)
(* PROOF TOOLS FOR HARDWARE COUNTER DEVICES                                  *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Automatically synthesizing hardware.                                      *)
(* ------------------------------------------------------------------------- *)

let mk_event_counter_arg n =
    let r = bit_width_num n in
    let m = bit_shl_num num_1 r in
    bits_to_bus (num_to_bitvec (m -/ n) r);;

let mk_counter_arg n =
    let n2 = add_num n num_2 in
    let (m,r) =
        let r = bit_width_num n2 -/ num_1 in
        let m = bit_shl_num num_1 r +/ r in
        if le_num n2 m then (m,r) else
        let rs = r +/ num_1 in
        (bit_shl_num num_1 rs +/ rs, rs) in
    bits_to_bus (num_to_bitvec (m -/ n2) r);;

let bpipe_syn = [("pipeb",bpipe_def)];;

let pipe_syn = setify (("pipe",pipe_def) :: bpipe_syn);;

let event_counter_syn = setify (("ctre",event_counter_def) :: badder2_syn);;

let counter_syn = setify (("ctr",counter_def) :: badder2_syn);;

let counter_pulse_syn =
    setify (("ctrp",counter_pulse_def) :: pulse_syn @ counter_syn);;

let synthesize_counter n =
    let ld = `ld : wire` in
    let nb = mk_counter_arg n in
    let dn = `dn : wire` in
    let fvs = [`t : cycle`; `k : cycle`] in
    let th0 = SPECL ([mk_numeral n; ld; nb; dn] @ fvs) counter_signal in
    let th1 =
        let bus_conv =
            REWRITE_CONV
              [bnil_width; bwire_width; bappend_width;
               bnil_bsignal; bwire_bsignal; bappend_bsignal; APPEND] in
        let wth = (bus_conv THENC NUM_REDUCE_CONV) (mk_width nb) in
        let conv =
            REWRITE_CONV [wth] THENC
            bus_conv THENC
            REWRITE_CONV [ground_signal; power_signal] THENC
            REWRITE_CONV [bits_to_num_cons; bits_to_num_nil] THENC
            REWRITE_CONV [bit_cons_false; bit_cons_true] THENC
            NUM_REDUCE_CONV in
        CONV_RULE
          (LAND_CONV
             (RAND_CONV
                (LAND_CONV conv THENC
                 REWR_CONV TRUE_AND_THM))) th0 in
    let th2 =
        let (asms,_) = dest_imp (concl th1) in
        let (_,ckt) = dest_conj asms in
        let cth = EQT_INTRO (ASSUME ckt) in
        CONV_RULE
          (LAND_CONV
             (RAND_CONV (REWR_CONV cth) THENC
              REWR_CONV AND_TRUE_THM)) th1 in
    let th = GENL fvs th2 in
    let primary = frees (concl th) in
    synthesize_hardware counter_syn primary th;;

(* Testing
let counter_91_ckt = synthesize_counter (dest_numeral `91`);;
let name = Verilog_module "counter_91";;
let comment = default_verilog_comment ();;  (* counter_91 *)
let primary = Verilog_primary (`clk : wire` :: frees_circuit counter_91_ckt);;
hardware_to_verilog_file name comment primary counter_91_ckt;;
*)
