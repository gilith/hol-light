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
(* Assumption rules allow backward reasoning on theorem assumptions.         *)
(* ------------------------------------------------------------------------- *)

type asm_rule = term -> thm -> term list option * thm;;

let apply_asm_rule (asm_rule : asm_rule) =
    let rec apply_iteration same asms th =
        match asms with
          [] -> (same,th)
        | asm :: asms ->
          try (let (newso,th) = asm_rule asm th in
               match newso with
                 Some news -> apply_iteration false (news @ asms) th
               | None -> (false,th))
          with Failure _ -> apply_iteration same asms th in
    let rec apply_loop th =
        let (same,th) = apply_iteration true (hyp th) th in
        if same then th else apply_loop th in
    apply_loop;;

let then_asm_rule (ar1 : asm_rule) (ar2 : asm_rule) : asm_rule =
    let ar2l asm (asmso,th) =
        let (newso,th) = ar2 asm th in
        let asmso =
            match (newso,asmso) with
              (Some news, Some asms) -> Some (news @ asms)
            | _ -> None in
        (asmso,th) in
    fun asm -> fun th ->
    let (newso,th) = ar1 asm th in
    match newso with
      Some news -> itlist ar2l news (Some [], th)
    | None -> failwith "then_asm_rule";;

let orelse_asm_rule (ar1 : asm_rule) (ar2 : asm_rule) : asm_rule =
    fun asm -> fun th ->
    try (ar1 asm th)
    with Failure _ -> ar2 asm th;;

let first_asm_rule (ars0 : asm_rule list) : asm_rule =
    let rec first ars asm th =
        match ars with
          [] -> failwith "first_asm_rule"
        | ar :: ars -> orelse_asm_rule ar (first ars) asm th in
    first ars0;;

let (thm_asm_rule,conv_asm_rule) =
    let eq_to_imp_thm = MATCH_MP (TAUT `(a <=> b) ==> (b ==> a)`) in
    let mk_imp_thm =
        let pull_exists =
            let conv = REWR_CONV LEFT_IMP_EXISTS_THM in
            let rec pull tm =
                TRY_CONV
                  (conv THENC
                   TRY_CONV (RAND_CONV (ABS_CONV pull))) tm in
            CONV_RULE pull in
        let collect_asms =
            let conv = TRY_CONV (REWR_CONV IMP_CONJ) in
            let rec collect th =
                if not (is_imp (concl th)) then ([],th) else
                let th = CONV_RULE conv th in
                let (asm,_) = dest_imp (concl th) in
                let (asms,th) = collect (UNDISCH th) in
                (asm :: asms, th) in
            collect in
        let norm_imp_thm th =
            let th = pull_exists th in
            let (vs,_) = strip_forall (concl th) in
            let th = SPEC_ALL th in
            let (asms,th) = collect_asms th in
            (vs,asms,th) in
        fun th ->
        let th = SPEC_ALL th in
        let tm = concl th in
        if is_iff tm then norm_imp_thm (eq_to_imp_thm th)
        else if is_imp tm then norm_imp_thm th
        else ([],[],th) in
    let imp_thm_asm_rule (vs,asms,ith) : asm_rule =
        fun asm -> fun th ->
        let fresh v = (genvar (type_of v), v) in
        let (_,sub,_) = term_match [] (concl ith) asm in
        let fsub = map fresh vs in
        let ith = INST sub (INST fsub ith) in
        let asms = map (vsubst sub o vsubst fsub) asms in
        (Some asms, PROVE_HYP ith th) in
    let thm_asm_rule th = imp_thm_asm_rule (mk_imp_thm th) in
    let conv_asm_rule (conv : conv) : asm_rule =
        fun asm -> fun th ->
        let eth = conv asm in
        let ith =
            try (EQT_ELIM eth)
            with Failure _ -> UNDISCH (eq_to_imp_thm eth) in
        (Some (hyp ith), PROVE_HYP ith th) in
    (thm_asm_rule,conv_asm_rule);;

let subst_var_asm_rule : asm_rule =
    fun asm -> fun th ->
    let asm_rule l r = (None, PROVE_HYP (REFL r) (INST [(r,l)] th)) in
    let (l,r) = dest_eq asm in
    if is_var l then asm_rule l r
    else if is_var r then asm_rule r l
    else failwith "subst_var_asm_rule";;

(* ------------------------------------------------------------------------- *)
(* Automatically generating verified circuits.                               *)
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
