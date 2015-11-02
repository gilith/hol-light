(* ========================================================================= *)
(* PROOF TOOLS FOR HARDWARE WIRE DEVICES                                     *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

let mk_connect =
    let connect_tm = `connect` in
    fun x -> fun y ->
    mk_comb (mk_comb (connect_tm,x), y);;

let dest_connect =
    let connect_tm = `connect` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = connect_tm then (x,y) else failwith "dest_connect";;

let is_connect = can dest_connect;;

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

let mk_case1 =
    let case1_tm = `case1` in
    fun w -> fun x -> fun y -> fun z ->
    mk_comb (mk_comb (mk_comb (mk_comb (case1_tm,w), x), y), z);;

let dest_case1 =
    let case1_tm = `case1` in
    fun tm ->
    let (tm,z) = dest_comb tm in
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    let (tm,w) = dest_comb tm in
    if tm = case1_tm then (w,x,y,z) else failwith "dest_case1";;

let is_case1 = can dest_case1;;

(* ------------------------------------------------------------------------- *)
(* Automatically synthesizing hardware.                                      *)
(* ------------------------------------------------------------------------- *)

let pulse_syn = [("pulse",pulse_def)];;

let nor2_syn = [("nor2",nor2_def)];;

let and3_syn = [("and3",and3_def)];;

let or3_syn = [("or3",or3_def)];;

let xor3_syn = [("xor3",xor3_def)];;

let majority3_syn = setify (("maj3",majority3_def) :: or3_syn);;

let sticky_syn = [("sticky",sticky_def)];;
