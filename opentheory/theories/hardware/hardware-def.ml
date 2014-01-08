(* ========================================================================= *)
(* DEFINITION OF THE HARDWARE MODEL                                          *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

logfile "hardware-def";;

(* ------------------------------------------------------------------------- *)
(* Cycles are the primitive time steps.                                      *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("cycle",`:num`);;

(* ------------------------------------------------------------------------- *)
(* Wires are streams of signals.                                             *)
(* ------------------------------------------------------------------------- *)

let (mk_dest_wire,dest_mk_wire) =
  CONJ_PAIR (define_newtype ("w","wire") ("s",`:bool stream`));;

export_thm mk_dest_wire;;
export_thm dest_mk_wire;;

let wire_tybij = CONJ mk_dest_wire dest_mk_wire;;

(* ------------------------------------------------------------------------- *)
(* Wires generate signals at each cycle.                                     *)
(* ------------------------------------------------------------------------- *)

let signal_def = new_definition `!w. signal w = snth (dest_wire w)`;;

export_thm signal_def;;

(* ------------------------------------------------------------------------- *)
(* Power and ground wires.                                                   *)
(* ------------------------------------------------------------------------- *)

let ground_def = new_definition `ground = mk_wire (sreplicate F)`;;

export_thm ground_def;;

let power_def = new_definition `power = mk_wire (sreplicate T)`;;

export_thm power_def;;

(* ------------------------------------------------------------------------- *)
(* Buses are lists of wires.                                                 *)
(* ------------------------------------------------------------------------- *)

let (mk_dest_bus,dest_mk_bus) =
  CONJ_PAIR (define_newtype ("x","bus") ("l",`:wire list`));;

export_thm mk_dest_bus;;
export_thm dest_mk_bus;;

let bus_tybij = CONJ mk_dest_bus dest_mk_bus;;

(* ------------------------------------------------------------------------- *)
(* Bus constructors.                                                         *)
(* ------------------------------------------------------------------------- *)

let bnil_def = new_definition
  `bnil = mk_bus []`;;

export_thm bnil_def;;

let bwire_def = new_definition
  `!w. bwire w = mk_bus [w]`;;

export_thm bwire_def;;

let bappend_def = new_definition
  `!x y. bappend x y = mk_bus (APPEND (dest_bus x) (dest_bus y))`;;

export_thm bappend_def;;

(* ------------------------------------------------------------------------- *)
(* Bus widths.                                                               *)
(* ------------------------------------------------------------------------- *)

let width_def = new_definition
  `!x. width x = LENGTH (dest_bus x)`;;

export_thm width_def;;

(* ------------------------------------------------------------------------- *)
(* Buses generate signal lists at each cycle.                                *)
(* ------------------------------------------------------------------------- *)

let bsignal_def = new_definition
  `!x t. bsignal x t = MAP (\w. signal w t) (dest_bus x)`;;

export_thm bsignal_def;;

(* ------------------------------------------------------------------------- *)
(* Sub-buses.                                                                *)
(* ------------------------------------------------------------------------- *)

let bsub_def = new_definition
  `!x k n y.
     bsub x k n y <=>
     k + n <= width x /\
     y = mk_bus (take n (drop k (dest_bus x)))`;;

export_thm bsub_def;;

(* ------------------------------------------------------------------------- *)
(* Power and ground buses.                                                   *)
(* ------------------------------------------------------------------------- *)

let bground_def = new_definition
  `!n. bground n = mk_bus (REPLICATE ground n)`;;

export_thm bground_def;;

let bpower_def = new_definition
  `!n. bpower n = mk_bus (REPLICATE power n)`;;

export_thm bpower_def;;

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

let mk_ground = `ground`;;

let mk_power = `power`;;

let bit_to_wire b = if b then mk_power else mk_ground;;

let mk_bnil = `bnil`;;

let mk_bwire =
    let bwire_tm = `bwire` in
    fun w -> mk_comb (bwire_tm,w);;

let dest_bwire =
    let bwire_tm = `bwire` in
    fun tm ->
    let (tm,w) = dest_comb tm in
    if tm = bwire_tm then w else failwith "dest_bwire";;

let mk_bappend =
    let bappend_tm = `bappend` in
    fun x -> fun y -> mk_comb (mk_comb (bappend_tm,x), y);;

let dest_bappend =
    let bappend_tm = `bappend` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = bappend_tm then (x,y) else failwith "dest_bappend";;

let mk_width =
    let width_tm = `width` in
    fun x -> mk_comb (width_tm,x);;

let dest_width =
    let width_tm = `width` in
    fun tm ->
    let (tm,x) = dest_comb tm in
    if tm = width_tm then x else failwith "dest_width";;

let mk_bsub =
    let bsub_tm = `bsub` in
    fun x -> fun k -> fun n -> fun y ->
    mk_comb (mk_comb (mk_comb (mk_comb (bsub_tm,x), k), n), y);;

let dest_bsub =
    let bsub_tm = `bsub` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,n) = dest_comb tm in
    let (tm,k) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = bsub_tm then (x,k,n,y) else failwith "dest_bsub";;

let dest_bground =
    let bground_tm = `bground` in
    fun tm ->
    let (tm,n) = dest_comb tm in
    if tm = bground_tm then n else failwith "dest_bground";;

let dest_bpower =
    let bpower_tm = `bpower` in
    fun tm ->
    let (tm,n) = dest_comb tm in
    if tm = bpower_tm then n else failwith "dest_bpower";;

let bits_to_bus l =
    let f h t = mk_bappend (mk_bwire (bit_to_wire h)) t in
    itlist f l mk_bnil;;

let genvar_bus =
    let wire_ty = `:wire` in
    let rec mk_bus n =
        if eq_num n num_0 then mk_bnil else
        let w = genvar wire_ty in
        let b = mk_bus (n -/ num_1) in
        mk_bappend (mk_bwire w) b in
    mk_bus;;

logfile_end ();;
