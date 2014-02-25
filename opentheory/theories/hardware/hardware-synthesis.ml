(* ========================================================================= *)
(* HARDWARE SYNTHESIS                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let maps (f : 'a -> 's -> 'b * 's) =
    let rec m xs s =
        match xs with
          [] -> ([],s)
        | x :: xs ->
          let (y,s) = f x s in
          let (ys,s) = m xs s in
          (y :: ys, s) in
     m;;

let null_subst (sub : (term * term) list) =
    match sub with
      [] -> true
    | _ -> false;;

let compose_subst old_sub new_sub =
    new_sub @ map (fun (t,v) -> (vsubst new_sub t, v)) old_sub;;

let simple_conv th =
    let redex = lhs (concl th) in
    fun tm -> if tm = redex then th else failwith "simple_conv";;

let orelse_sym_conv : conv -> conv =
    let rewr = REWR_CONV EQ_SYM_EQ in
    fun c -> c ORELSEC (rewr THENC c);;

(* ------------------------------------------------------------------------- *)
(* Name generators.                                                          *)
(* ------------------------------------------------------------------------- *)

type namer = Namer of term list * string * term list;;

let frozen_vars (Namer (x,_,_)) = x;;

let current_scope (Namer (_,x,_)) = x;;

let generated_vars (Namer (_,_,x)) = x;;

let new_namer frozen = Namer (frozen,"",frozen);;

let add_generated_vars vs' (Namer (f,s,vs)) = Namer (f, s, vs' @ vs);;

let reset_scope s (Namer (f,_,vs)) = Namer (f,s,vs);;

let is_unfrozen_var namer v = is_var v && not (mem v (frozen_vars namer));;

let not_unfrozen_var namer v = not (is_unfrozen_var namer v);;

let fresh_variant v namer =
    let v = variant (generated_vars namer) v in
    let namer = add_generated_vars [v] namer in
    (v,namer);;

let fresh_var v namer =
    let (s,ty) = dest_var v in
    let sc = current_scope namer in
    let s = if String.length sc = 0 then s else sc ^ "." ^ s in
    fresh_variant (mk_var (s,ty)) namer;;

let freshen_vars vs namer =
    let (vs',namer) = maps fresh_var vs namer in
    (zip vs' vs, namer);;

let fresh_bus v n namer =
    let (s,_) = dest_var v in
    let tm = variable_bus s n in
    let vs = frees tm in
    let (vs',namer) = maps fresh_variant vs namer in
    (vsubst (zip vs' vs) tm, namer);;

let narrow_scope s namer =
    if String.length s = 0 then namer else
    let sc = mk_var (s,bool_ty) in
    let (sc,namer) = fresh_var sc namer in
    let (sc,_) = dest_var sc in
    reset_scope sc namer;;

(* ------------------------------------------------------------------------- *)
(* Prolog rules allow backward reasoning on theorem assumptions.             *)
(* ------------------------------------------------------------------------- *)

type prolog_rule =
     Prolog_rule of
       (term -> namer -> thm * (term * term) list * namer);;

let all_prolog_rule =
    Prolog_rule (fun tm -> fun namer -> (ASSUME tm, [], namer));;

let no_prolog_rule =
    Prolog_rule (fun _ -> fun _ -> failwith "no_prolog_rule");;

let apply_prolog_rule (Prolog_rule pr) = pr;;

let check_prolog_rule f pr =
    Prolog_rule
      (fun tm -> fun namer ->
       let () = f tm in
       apply_prolog_rule pr tm namer);;

let orelse_prolog_rule pr1 pr2 =
    Prolog_rule
      (fun tm -> fun namer ->
       try (apply_prolog_rule pr1 tm namer)
       with Failure _ -> apply_prolog_rule pr2 tm namer);;

let try_prolog_rule pr =
    orelse_prolog_rule pr all_prolog_rule;;

let first_prolog_rule =
    let rec first prs =
        match prs with
          [] -> no_prolog_rule
        | pr :: prs -> orelse_prolog_rule pr (first prs) in
    first;;

let prove_hyp_prolog_rule pr =
    let rec prolog_asms th sub namer asms =
        match asms with
          [] -> (th,sub,namer)
        | asm :: asms ->
          let asm = vsubst sub asm in
          let (asm_th,asm_sub,asm_namer) = apply_prolog_rule pr asm namer in
          let th = PROVE_HYP asm_th (INST asm_sub th) in
          let sub = compose_subst sub asm_sub in
          let namer = reset_scope (current_scope namer) asm_namer in
          prolog_asms th sub namer asms in
    fun th -> fun namer -> prolog_asms th [] namer (hyp th);;

let then_prolog_rule pr1 pr2 =
    Prolog_rule
      (fun tm -> fun namer0 ->
       let (th,sub1,namer) = apply_prolog_rule pr1 tm namer0 in
       let (th,sub2,namer) = prove_hyp_prolog_rule pr2 th namer in
       let sub = compose_subst sub1 sub2 in
       let namer = reset_scope (current_scope namer0) namer in
       (th,sub,namer));;

let repeat_prove_hyp_prolog_rule pr =
    let rec prolog_asms fvs th sub namer asms =
        match asms with
          [] -> (th,sub,namer)
        | asm :: asms ->
          let asm = vsubst sub asm in
          let (asm_th,asm_sub,asm_namer) = apply_prolog_rule pr asm namer in
          let th = PROVE_HYP asm_th (INST asm_sub th) in
          let sub = compose_subst sub asm_sub in
          let namer = reset_scope (current_scope namer) asm_namer in
          if length (intersect (map snd asm_sub) fvs) = 0 then
            prolog_asms (union (frees asm) fvs) th sub namer asms
          else
            prolog_asms [] th sub namer (hyp th) in
     fun th -> fun namer -> prolog_asms [] th [] namer (hyp th);;

let then_repeat_prolog_rule pr1 pr2 =
    Prolog_rule
      (fun tm -> fun namer0 ->
       let (th,sub1,namer) = apply_prolog_rule pr1 tm namer0 in
       let (th,sub2,namer) = repeat_prove_hyp_prolog_rule pr2 th namer in
       let sub = compose_subst sub1 sub2 in
       let namer = reset_scope (current_scope namer0) namer in
       (th,sub,namer));;

let rec repeat_prolog_rule pr =
    Prolog_rule
      (fun tm -> fun namer ->
       let rule =
           try_prolog_rule
             (then_repeat_prolog_rule pr (repeat_prolog_rule pr)) in
       apply_prolog_rule rule tm namer);;

let (scope_thm_prolog_rule,conv_prolog_rule) =
    let eq_to_imp_thm = MATCH_MP (TAUT `(a <=> b) ==> (b ==> a)`) in
    let mk_prolog_thm =
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
                if not (is_imp (concl th)) then th else
                let th = CONV_RULE conv th in
                collect (UNDISCH th) in
            collect in
        let norm_imp_thm th =
            let th = SPEC_ALL (pull_exists th) in
            let (asms,conc) = dest_imp (concl th) in
            let vs = filter (not o C mem (frees conc)) (frees asms) in
            (vs, collect_asms th) in
        fun th ->
        let th = SPEC_ALL th in
        let th = if is_iff (concl th) then eq_to_imp_thm th else th in
        if is_imp (concl th) then norm_imp_thm th else ([],th) in
    let prolog_thm_rule s (vs,th) =
        let pat = concl th in
        Prolog_rule
          (fun tm -> fun namer ->
           let namer = narrow_scope s namer in
           let (_,sub,_) = term_match [] pat tm in
           let (vs_sub,namer) = freshen_vars vs namer in
           let sub = vs_sub @ sub in
           let th = INST sub th in
           (th,[],namer)) in
    let thm_rule s th = prolog_thm_rule s (mk_prolog_thm th) in
    let conv_rule (conv : conv) =
        Prolog_rule
          (fun tm -> fun namer ->
           let eq_th = conv tm in
           let th =
               try (EQT_ELIM eq_th)
               with Failure _ -> UNDISCH (eq_to_imp_thm eq_th) in
           (th,[],namer)) in
    (thm_rule,conv_rule);;

let thm_prolog_rule = scope_thm_prolog_rule "";;

let sym_prolog_rule : prolog_rule =
    Prolog_rule
      (fun tm -> fun namer ->
       let (l,r) = dest_eq tm in
       (SYM (ASSUME (mk_eq (r,l))), [], namer));;

let orelse_sym_prolog_rule pr =
    orelse_prolog_rule pr (then_prolog_rule sym_prolog_rule pr);;

let subst_var_prolog_rule =
    orelse_sym_prolog_rule
      (Prolog_rule
         (fun tm -> fun namer ->
          let (l,r) = dest_eq tm in
          if is_unfrozen_var namer l then (REFL r, [(r,l)], namer)
          else failwith "subst_var_prolog_rule"));;

(* ------------------------------------------------------------------------- *)
(* Automatically synthesizing hardware.                                      *)
(* ------------------------------------------------------------------------- *)

let num_simp_prolog_rule =
    let push_numeral_conv =
        let dest_add = dest_binop `(+) : num -> num -> num` in
        let th = prove
          (`!m n p : num. m + (n + p) = n + (m + p)`,
           REPEAT GEN_TAC THEN
           REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
           MATCH_ACCEPT_TAC ADD_SYM) in
        let rewr1 = REWR_CONV ADD_SYM in
        let rewr2 = REWR_CONV th in
        let conv tm =
            let (x,y) = dest_add tm in
            if not (is_numeral x) then failwith "push_numeral_conv" else
            try (rewr2 tm) with Failure _ ->
            if is_numeral y then NUM_REDUCE_CONV tm else
            rewr1 tm in
        REDEPTH_CONV conv in
    let simp_conv =
        REWRITE_CONV
          [ZERO_ADD; ADD_0; GSYM ADD_ASSOC;
           bnil_width; bwire_width; bappend_width] THENC
        push_numeral_conv THENC
        NUM_REDUCE_CONV in
    conv_prolog_rule (CHANGED_CONV simp_conv);;

let num_eq_prolog_rule =
    let is_num_type = (=) `:num` in
    let add_tm = `(+) : num -> num -> num` in
    let mk_add = mk_binop add_tm in
    let dest_add = dest_binop add_tm in
    let numeral_eq_add_numeral_conv tm =
        let (m,t) = dest_eq tm in
        let mn = dest_numeral m in
        let (t,n) = dest_add t in
        let nn = dest_numeral n in
        let th = NUM_REDUCE_CONV (mk_add (mk_numeral (mn -/ nn)) n) in
        let conv = LAND_CONV (K (SYM th)) THENC REWR_CONV EQ_ADD_RCANCEL in
        conv tm in
    let reduce_conv =
        FIRST_CONV
          [numeral_eq_add_numeral_conv] in
    let check tm =
       let (l,r) = dest_eq tm in
       if is_num_type (type_of l) then () else
       failwith "num_eq_prolog_rule" in
    check_prolog_rule check
      (orelse_sym_prolog_rule (conv_prolog_rule reduce_conv));;

let mk_bus_prolog_rule =
    orelse_sym_prolog_rule
      (Prolog_rule
         (fun tm -> fun namer ->
          let (t,n) = dest_eq tm in
          let nn = dest_numeral n in
          let v = dest_width t in
          if not_unfrozen_var namer v then failwith "mk_bus_prolog_rule" else
          let (b,namer) = fresh_bus v nn namer in
          let sub = [(b,v)] in
          (ASSUME (vsubst sub tm), sub, namer)));;

let (wire_prolog_rule,bsub_prolog_rule,bground_prolog_rule) =
    let zero_suc_conv : conv =
        let suc_tm = `SUC` in
        let mk_suc tm = mk_comb (suc_tm,tm) in
        fun tm ->
        let n = dest_numeral tm in
        if eq_num n num_0 then REFL tm else
        let m = mk_suc (mk_numeral (n -/ num_1)) in
        SYM (NUM_SUC_CONV m) in
    let wire_prolog_rule =
        let zero_rule = thm_prolog_rule wire_zero in
        let suc_rule = thm_prolog_rule wire_suc in
        let conv tm =
            let (x,_,_) = dest_wire tm in
            let (w,_) = dest_bappend x in
            let _ = dest_bwire w in
            LAND_CONV (zero_suc_conv) tm in
        then_prolog_rule
          (conv_prolog_rule conv)
          (orelse_prolog_rule zero_rule suc_rule) in
    let bsub_prolog_rule =
        let suc_thm = prove
          (`!w x k n y.
              bsub x k n y ==>
              bsub (bappend (bwire w) x) (SUC k) n y`,
           REPEAT STRIP_TAC THEN
           SUBGOAL_THEN `SUC k = width (bwire w) + k` SUBST1_TAC THENL
           [REWRITE_TAC [bwire_width; ONE; SUC_ADD; ZERO_ADD];
            ASM_REWRITE_TAC [bsub_in_suffix]]) in
        let zero_zero_thm = prove
          (`!x y.
              y = bnil ==>
              bsub x 0 0 y`,
           REPEAT STRIP_TAC THEN
           ASM_REWRITE_TAC [bsub_zero; LE_0]) in
        let zero_suc_thm = prove
          (`!w x n y.
              (?z. y = bappend (bwire w) z /\ bsub x 0 n z) ==>
              bsub (bappend (bwire w) x) 0 (SUC n) y`,
           REPEAT STRIP_TAC THEN
           FIRST_X_ASSUM SUBST_VAR_TAC THEN
           MATCH_MP_TAC bsub_suc THEN
           REWRITE_TAC [wire_zero] THEN
           MATCH_MP_TAC suc_thm THEN
           ASM_REWRITE_TAC []) in
        let suc_rule = thm_prolog_rule suc_thm in
        let zero_zero_rule = thm_prolog_rule zero_zero_thm in
        let zero_suc_rule = thm_prolog_rule zero_suc_thm in
        let conv tm =
            let _ = dest_bsub tm in
            RATOR_CONV
              (LAND_CONV zero_suc_conv THENC
               RAND_CONV zero_suc_conv) tm in
        then_prolog_rule
          (conv_prolog_rule conv)
          (orelse_prolog_rule
             suc_rule
             (orelse_prolog_rule zero_zero_rule zero_suc_rule)) in
    let bground_prolog_rule =
        let zero_conv = REWR_CONV bground_zero in
        let suc_conv = REWR_CONV bground_suc in
        let rec expand_conv tm =
            (RAND_CONV zero_suc_conv THENC
             (zero_conv ORELSEC
              (suc_conv THENC
               RAND_CONV expand_conv))) tm in
        let conv tm =
            let _ = dest_bground tm in
            expand_conv tm in
        conv_prolog_rule (CHANGED_CONV (DEPTH_CONV conv)) in
    (wire_prolog_rule,bsub_prolog_rule,bground_prolog_rule);;

let brev_prolog_rule =
    let bnil_thm = prove
      (`!y. y = bnil ==> brev bnil y`,
       REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC [brev_bnil]) in
    let bwire_thm = prove
      (`!w y. y = bwire w ==> brev (bwire w) y`,
       REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC [brev_bwire]) in
    let bappend_thm = prove
      (`!x1 x2 y1 y2 y.
          y = bappend y1 y2 /\ brev x1 y2 /\ brev x2 y1 ==>
          brev (bappend x1 x2) y`,
       REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC [] THEN
       MATCH_MP_TAC brev_bappend THEN
       ASM_REWRITE_TAC []) in
    let bappend_conv =
        let rewr0 = (REWR_CONV o prove)
          (`!x. bappend x bnil = bappend bnil x`,
           REWRITE_TAC [bappend_bnil; bnil_bappend]) in
        let rewr1 = REWR_CONV (GSYM bappend_assoc) in
        let rec conv tm =
            (let (x,y) = dest_bappend tm in
             if is_bnil y then rewr0 else
             if is_bappend y then RAND_CONV conv THENC rewr1 else
             failwith "brev_prolog_rule.bappend_conv") tm in
        LAND_CONV conv in
    let bnil_rule = thm_prolog_rule bnil_thm in
    let bwire_rule = thm_prolog_rule bwire_thm in
    let bappend_rule =
        then_prolog_rule
          (conv_prolog_rule bappend_conv)
          (thm_prolog_rule bappend_thm) in
    Prolog_rule
      (fun tm -> fun namer ->
       let (x,_) = dest_brev tm in
       if is_bnil x then apply_prolog_rule bnil_rule tm namer else
       if is_bwire x then apply_prolog_rule bwire_rule tm namer else
       if is_bappend x then apply_prolog_rule bappend_rule tm namer else
       failwith "brev_prolog_rule");;

let connect_wire_prolog_rule =
    Prolog_rule
      (fun tm -> fun namer ->
       let (x,y) = dest_connect tm in
       if is_unfrozen_var namer y then (SPEC x connect_refl, [(x,y)], namer)
       else failwith "connect_wire_prolog_rule");;

let wire_connect_prolog_rule =
    Prolog_rule
      (fun tm -> fun namer ->
       let (x,y) = dest_connect tm in
       if is_unfrozen_var namer x then (SPEC y connect_refl, [(y,x)], namer)
       else failwith "wire_connect_prolog_rule");;

let connect_prolog_rule =
    orelse_prolog_rule connect_wire_prolog_rule wire_connect_prolog_rule;;

let partition_primary primary th =
    let outputs = map rand (hyp th) in
    partition (not o C mem outputs) primary;;

let rescue_primary_outputs_prolog_rule =
    let connect_equal_wires = prove
        (`!w x. connect w x ==> x = w`,
         REPEAT STRIP_TAC THEN
         MATCH_MP_TAC signal_eq_imp THEN
         GEN_TAC THEN
         MATCH_MP_TAC connect_signal THEN
         ASM_REWRITE_TAC []) in
     let connect_conv primary_output namer =
         let wire =
             let (s,ty) = dest_var primary_output in
             mk_var (s ^ "_o", ty) in
         let (wire,namer) = fresh_var wire namer in
         let rescue_th = SPECL [wire; primary_output] connect_equal_wires in
         (simple_conv (UNDISCH rescue_th), namer) in
     fun primary_outputs -> fun namer ->
     let (convs,namer) = maps connect_conv primary_outputs namer in
     (conv_prolog_rule (ONCE_DEPTH_CONV (FIRST_CONV convs)), namer);;

let rescue_primary_outputs =
    let cleanup_rule =
        try_prolog_rule
          (first_prolog_rule
             [subst_var_prolog_rule;
              connect_wire_prolog_rule]) in
    fun primary_outputs -> fun th -> fun namer ->
    if length primary_outputs = 0 then (th,namer) else
    let (rescue_rule,namer) =
        rescue_primary_outputs_prolog_rule primary_outputs namer in
    let (th,_,namer) = prove_hyp_prolog_rule rescue_rule th namer in
    let (th,_,namer) = repeat_prove_hyp_prolog_rule cleanup_rule th namer in
    (th,namer);;

let merge_logic =
    let sort_wires w1 w2 =
        let (s1,_) = dest_var w1 in
        let (s2,_) = dest_var w2 in
        if String.length s2 < String.length s1 then (w2,w1) else (w1,w2) in
    let rec merge_asms th asms =
        match asms with
          [] -> th
        | asm :: asms ->
          if is_connect asm then merge_asms th asms else
          let (f,w) = dest_comb asm in
          let pred h = rator h = f in
          match filter pred asms with
            [] -> merge_asms th asms
          | h :: _ -> merge_thm (INST [sort_wires w (rand h)] th)
    and merge_thm th = merge_asms th (hyp th) in
    merge_thm;;

let delete_dead_logic primary_inputs primary_outputs th =
    let defs =
        let mk_def asm = (rand asm, (frees (rator asm), asm)) in
        map mk_def (hyp th) in
    let find_def wire =
        match filter (fun (w,_) -> w = wire) defs with
          [] -> failwith "delete_dead_logic: no definition found for wire"
        | [(_,ws_asm)] -> ws_asm
        | _ :: _ :: _ ->
          failwith "delete_dead_logic: multiple definitions found for wire" in
    let rec reachable seen work =
        match work with
          [] -> seen
        | wire :: work ->
          if mem wire seen then reachable seen work else
          let seen = wire :: seen in
          if mem wire primary_inputs then reachable seen work else
          let (ws,_) = find_def wire in
          reachable seen (ws @ work) in
    let alive = reachable [] primary_outputs in
    let alive =
        let (pis,alive) = partition (C mem primary_inputs) alive in
        let n = length primary_inputs - length pis in
        let () =
            if n = 0 then () else
            warn true
              (string_of_int n ^ " unused primary input" ^
               (if n = 1 then "" else "s")) in
        alive in
    let (delays,wires) = partition (fun (_,(_,asm)) -> is_delay asm) defs in
    let (alive_delays,alive_wires) =
        let is_delay wire = exists (fun (w,_) -> w = wire) delays in
        partition is_delay alive in
    let () =
        let n = length delays - length alive_delays in
        if n = 0 then () else
        warn true
          (string_of_int n ^ " unused delay" ^
           (if n = 1 then "" else "s")) in
    let () =
        let n = length wires - length alive_wires in
        if n = 0 then () else
        let dead = subtract (map fst wires) alive_wires in
        let msg =
            string_of_int n ^ " unused wire" ^
            (if n = 1 then "" else "s") ^ ":\n  " ^
            String.concat "\n  " (map string_of_term dead) in
        warn true msg in
    (*** Delete dead logic ***)
    th;;

let rename_wires =
    let rename p w (n,s) =
        (n + 1, (mk_var (p ^ string_of_int n, type_of w), w) :: s) in
    fun primary -> fun th ->
    let gvs = filter (not o C mem primary) (freesl (hyp th)) in
    let delays = filter is_delay (hyp th) in
    let delay_outputs = map rand delays in
    let (rvs,wvs) = partition (C mem delay_outputs) gvs in
    let (_,sub) = itlist (rename "r") rvs (0,[]) in
    let (_,sub) = itlist (rename "w") wvs (0,sub) in
    INST sub th;;

let instantiate_hardware =
    let basic_rules =
        [subst_var_prolog_rule;
         num_simp_prolog_rule;
         num_eq_prolog_rule;
         mk_bus_prolog_rule;
         wire_prolog_rule;
         bsub_prolog_rule;
         brev_prolog_rule;
         bground_prolog_rule;
         connect_prolog_rule] @
        map thm_prolog_rule
        [bconnect_bappend_bwire; bconnect_bnil;
         bdelay_bappend_bwire; bdelay_bnil;
         bnot_bappend_bwire; bnot_bnil;
         band2_bappend_bwire; band2_bnil;
         bor2_bappend_bwire; bor2_bnil;
         bxor2_bappend_bwire; bxor2_bnil;
         bcase1_bappend_bwire; bcase1_bnil;
         not_ground; not_power;
         and2_left_ground; and2_right_ground;
         and2_left_power; and2_right_power;
         or2_left_ground; or2_right_ground;
         or2_left_power; or2_right_power;
         xor2_left_ground; xor2_right_ground;
         xor2_left_power; xor2_right_power;
         case1_middle_ground; case1_right_ground;
         case1_middle_power] in
    fun ths ->
    let user_rules = map (uncurry scope_thm_prolog_rule) ths in
    let rule = first_prolog_rule (basic_rules @ user_rules) in
    let instantiate = repeat_prove_hyp_prolog_rule (repeat_prolog_rule rule) in
    fun primary -> fun th ->
    let namer = new_namer primary in
    let (th,_,namer) = instantiate th namer in
    let (primary_inputs,primary_outputs) = partition_primary primary th in
    let (th,namer) = rescue_primary_outputs primary_outputs th namer in
    let th = merge_logic th in
    let th = delete_dead_logic primary_inputs primary_outputs th in
(***
    let th = rename_wires primary th in
***)
    th;;

(*** Testing
instantiate_hardware counter_syn (frees (concl counter91_thm)) counter91_thm;;
instantiate_hardware montgomery_mult_syn (frees (concl montgomery91_thm)) montgomery91_thm;;
***)

(* ------------------------------------------------------------------------- *)
(* Pretty-printing synthesized hardware in Verilog.                          *)
(* ------------------------------------------------------------------------- *)

let VERILOG_LINE_LENGTH = 79;;

type verilog_arg =
     Wire_verilog_arg of term
   | Bus_verilog_arg of bus_wires;;

let rec collect_verilog_args wires =
    match wires with
      [] -> []
    | wire :: wires ->
      let args = collect_verilog_args wires in
      try (let (w,i) = dest_bus_wire wire in
           match args with
             Bus_verilog_arg (Bus_wires (x,js)) :: rest ->
             if w = x then Bus_verilog_arg (Bus_wires (w, i :: js)) :: rest else
             Bus_verilog_arg (Bus_wires (w,[i])) :: args
           | _ -> Bus_verilog_arg (Bus_wires (w,[i])) :: args)
      with Failure _ -> Wire_verilog_arg wire :: args;;

let comment_box_text =
    let split s =
        let n = String.length s in
        let rec f i =
                try (if n <= i then [""] else
                 let j = String.index_from s i '\n' in
                 String.sub s i (j - i) :: f (j + 1))
            with Not_found -> [String.sub s i (n - i)] in
            f 0 in
    let top = "/*" ^ String.make (VERILOG_LINE_LENGTH - 3) '-' ^ "+" in
    let middle s =
        let space = VERILOG_LINE_LENGTH - (String.length s + 3) in
        "| " ^ s ^ String.make space ' ' ^ "|" in
    let bottom = "+" ^ String.make (VERILOG_LINE_LENGTH - 3) '-' ^ "*/" in
    fun text ->
        top ^ "\n" ^
        String.concat "\n" (map middle (split text)) ^ "\n" ^
        bottom ^ "\n";;

let hardware_to_verilog =
    let wire_name =
        let wire_ty = `:wire` in
        fun w ->
        if is_ground w then "1'b0" else
        if is_power w then "1'b1" else
        if not (is_var w) then
          failwith ("wire not a var: " ^ string_of_term w)
        else
        let (n,ty) = dest_var w in
        if ty <> wire_ty then
          failwith ("wire has bad type: " ^ string_of_term w)
        else
          n in
    let wire_names = map wire_name in
    let wire_sort =
        let var_name v = fst (dest_var v) in
        let var_cmp v1 v2 = String.compare (var_name v1) (var_name v2) < 0 in
        sort var_cmp in
    let arg_name arg =
        match arg with
          Wire_verilog_arg w -> wire_name w
        | Bus_verilog_arg (Bus_wires (b,_)) -> b in
    let arg_names = map arg_name in
    let arg_decl arg =
        match arg with
          Wire_verilog_arg w -> wire_name w
        | Bus_verilog_arg (Bus_wires (b,is)) -> range_to_string is ^ " " ^ b in
    let arg_decls = map arg_decl in
    let verilog_comment name property =
        let prop =
            let n = get_margin () in
            let () = set_margin (VERILOG_LINE_LENGTH - 4) in
            let s = string_of_term property in
            let () = set_margin n in
            s in
        comment_box_text
          ("module " ^ name ^ " satisfies the following property:\n\n" ^
           prop) ^ "\n" in
    let verilog_module_begin name args =
        "module " ^ name ^ "(" ^
        String.concat "," (arg_names args) ^
        ");" in
    let verilog_declarations kind xs =
        if length xs = 0 then "" else
        ("\n  " ^ kind ^ " " ^
         String.concat (";\n  " ^ kind ^ " ") xs ^
         ";\n") in
    let verilog_wire_declarations kind wires =
        verilog_declarations kind (wire_names wires) in
    let verilog_arg_declarations kind args =
        verilog_declarations kind (arg_decls args) in
    let verilog_connect tm =
        let (x,y) = dest_connect tm in
        "assign " ^ wire_name y ^ " = " ^ wire_name x ^ ";" in
    let verilog_delay tm =
        let (w,r) = dest_delay tm in
        wire_name r ^ " <= " ^ wire_name w in
    let verilog_not tm =
        let (x,y) = dest_not tm in
        "assign " ^ wire_name y ^ " = ~" ^ wire_name x ^ ";" in
    let verilog_and2 tm =
        let (x,y,z) = dest_and2 tm in
        "assign " ^ wire_name z ^
        " = " ^ wire_name x ^ " & " ^ wire_name y ^ ";" in
    let verilog_or2 tm =
        let (x,y,z) = dest_or2 tm in
        "assign " ^ wire_name z ^
        " = " ^ wire_name x ^ " | " ^ wire_name y ^ ";" in
    let verilog_xor2 tm =
        let (x,y,z) = dest_xor2 tm in
        "assign " ^ wire_name z ^
        " = " ^ wire_name x ^ " ^ " ^ wire_name y ^ ";" in
    let verilog_case1 tm =
        let (w,x,y,z) = dest_case1 tm in
        "assign " ^ wire_name z ^
        " = " ^ wire_name w ^ " ? " ^ wire_name x ^ " : " ^ wire_name y ^ ";" in
    let verilog_comb comb =
        if is_connect comb then verilog_connect comb
        else if is_not comb then verilog_not comb
        else if is_and2 comb then verilog_and2 comb
        else if is_or2 comb then verilog_or2 comb
        else if is_xor2 comb then verilog_xor2 comb
        else if is_case1 comb then verilog_case1 comb
        else failwith ("weird assumption: " ^ string_of_term comb) in
    let verilog_combinational combs wires =
        let find_comb w =
            match filter ((=) w o rand) combs with
              [] ->
              failwith ("no combinational assignment for wire " ^ wire_name w)
            | [c] -> c
            | _ :: _ :: _ ->
              failwith
                ("multiple combinational assignments for wire " ^
                 wire_name w) in
        if length combs = 0 then "" else
        ("\n  " ^
         String.concat ("\n  ")
           (map (verilog_comb o find_comb) wires) ^
         "\n") in
    let verilog_delays clk delays registers =
        let find_delay r =
            match filter ((=) r o rand) delays with
              [] -> failwith ("no delay for register " ^ wire_name r)
            | [d] -> d
            | _ :: _ :: _ ->
              failwith ("multiple delays for register " ^ wire_name r) in
        if length delays = 0 then "" else
        ("\n  always @(posedge " ^ wire_name clk ^ ")\n" ^
         "    begin\n      " ^
         String.concat (";\n      ")
           (map (verilog_delay o find_delay) registers) ^
         ";\n    end\n") in
    let verilog_module_end name = "\nendmodule // " ^ name ^ "\n" in
    fun name -> fun primary -> fun th ->
    let (delays,combs) = partition is_delay (hyp th) in
    let registers = wire_sort (map rand delays) in
    let wires = map rand combs in
    let (primary_outputs,primary_inputs) = partition (C mem wires) primary in
    let wires = wire_sort (filter (not o C mem primary_outputs) wires) in
    let primary_input_args = collect_verilog_args primary_inputs in
    let primary_output_args = collect_verilog_args primary_outputs in
    verilog_comment name (concl th) ^
    verilog_module_begin name (primary_input_args @ primary_output_args) ^
    verilog_arg_declarations "input" primary_input_args ^
    verilog_arg_declarations "output" primary_output_args ^
    verilog_wire_declarations "reg" registers ^
    verilog_wire_declarations "wire" wires ^
    verilog_combinational combs (wires @ primary_outputs) ^
    verilog_delays (hd primary) delays registers ^
    verilog_module_end name;;

(*** Testing
let name = "montgomery91";;
let property = concl montgomery91_thm;;
output_string stdout (hardware_to_verilog "montgomery91" primary montgomery91_thm);;
output_string stdout (hardware_to_verilog "montgomery91" primary th);;
***)

let hardware_to_verilog_file name wires th =
    let file = "opentheory/hardware/" ^ name ^ ".v" in
    let s = hardware_to_verilog name wires th in
    let h = open_out file in
    let () = output_string h s in
    let () = close_out h in
    file;;
