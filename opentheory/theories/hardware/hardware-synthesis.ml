(* ========================================================================= *)
(* HARDWARE SYNTHESIS                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

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

let is_unfrozen_var frozen v = is_var v && not (mem v frozen);;

let not_unfrozen_var frozen v = not (is_unfrozen_var frozen v);;

(* ------------------------------------------------------------------------- *)
(* Prolog rules allow backward reasoning on theorem assumptions.             *)
(* ------------------------------------------------------------------------- *)

type prolog_rule = term list -> term -> thm * (term * term) list;;

let all_prolog_rule : prolog_rule =
    fun _ -> fun tm -> (ASSUME tm, []);;

let no_prolog_rule : prolog_rule =
    fun _ -> fun _ -> failwith "no_prolog_rule";;

let orelse_prolog_rule (pr1 : prolog_rule) (pr2 : prolog_rule) : prolog_rule =
    fun frozen -> fun tm ->
    try (pr1 frozen tm)
    with Failure _ -> pr2 frozen tm;;

let try_prolog_rule (pr : prolog_rule) : prolog_rule =
    orelse_prolog_rule pr all_prolog_rule;;

let first_prolog_rule (prs0 : prolog_rule list) : prolog_rule =
    let rec first prs frozen tm =
        match prs with
          [] -> failwith "first_prolog_rule"
        | pr :: prs -> orelse_prolog_rule pr (first prs) frozen tm in
    first prs0;;

let prove_hyp_prolog_rule (pr : prolog_rule) =
    fun frozen ->
    let rec prolog_asms th sub asms =
        match asms with
          [] -> (th,sub)
        | asm :: asms ->
          let asm = vsubst sub asm in
          let (asm_th,asm_sub) = pr frozen asm in
          let th = PROVE_HYP asm_th (INST asm_sub th) in
          let sub = compose_subst sub asm_sub in
          prolog_asms th sub asms in
     fun th -> prolog_asms th [] (hyp th);;

let then_prolog_rule (pr1 : prolog_rule) (pr2 : prolog_rule) : prolog_rule =
    fun frozen -> fun tm ->
    let (th,sub1) = pr1 frozen tm in
    let (th,sub2) = prove_hyp_prolog_rule pr2 frozen th in
    let sub = compose_subst sub1 sub2 in
    (th,sub);;

let repeat_prove_hyp_prolog_rule (pr : prolog_rule) =
    fun frozen ->
    let rec prolog_asms fvs th sub asms =
        match asms with
          [] -> (th,sub)
        | asm :: asms ->
          let asm = vsubst sub asm in
          let (asm_th,asm_sub) = pr frozen asm in
          let th = PROVE_HYP asm_th (INST asm_sub th) in
          let sub = compose_subst sub asm_sub in
          if length (intersect (map snd asm_sub) fvs) = 0 then
            prolog_asms (union (frees asm) fvs) th sub asms
          else
            prolog_asms [] th sub (hyp th) in
     fun th -> prolog_asms [] th [] (hyp th);;

let then_repeat_prolog_rule (pr1 : prolog_rule) pr2 : prolog_rule =
    fun frozen -> fun tm ->
    let (th,sub1) = pr1 frozen tm in
    let (th,sub2) = repeat_prove_hyp_prolog_rule pr2 frozen th in
    let sub = compose_subst sub1 sub2 in
    (th,sub);;

let rec repeat_prolog_rule (pr : prolog_rule) : prolog_rule =
    fun frozen -> fun tm ->
    try_prolog_rule
      (then_repeat_prolog_rule pr (repeat_prolog_rule pr)) frozen tm;;

let (thm_prolog_rule,conv_prolog_rule) =
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
    let prolog_thm_rule (vs,th) : prolog_rule =
        let fresh v = (genvar (type_of v), v) in
        let pat = concl th in
        fun _ -> fun tm ->
        let (_,sub,_) = term_match [] pat tm in
        let sub = map fresh vs @ sub in
        let th = INST sub th in
        (th,[]) in
    let thm_rule th = prolog_thm_rule (mk_prolog_thm th) in
    let conv_rule (conv : conv) : prolog_rule =
        fun _ -> fun tm ->
        let eq_th = conv tm in
        let th =
            try (EQT_ELIM eq_th)
            with Failure _ -> UNDISCH (eq_to_imp_thm eq_th) in
        (th,[]) in
    (thm_rule,conv_rule);;

let sym_prolog_rule : prolog_rule =
    fun _ -> fun tm ->
    let (l,r) = dest_eq tm in
    (SYM (ASSUME (mk_eq (r,l))), []);;

let orelse_sym_prolog_rule (pr : prolog_rule) : prolog_rule =
    orelse_prolog_rule pr (then_prolog_rule sym_prolog_rule pr);;

let subst_var_prolog_rule : prolog_rule =
    orelse_sym_prolog_rule
      (fun frozen -> fun tm ->
       let (l,r) = dest_eq tm in
       if is_unfrozen_var frozen l then (REFL r, [(r,l)])
       else failwith "subst_var_prolog_rule");;

(* ------------------------------------------------------------------------- *)
(* Automatically synthesizing hardware.                                      *)
(* ------------------------------------------------------------------------- *)

let num_simp_prolog_rule : prolog_rule =
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

let num_eq_prolog_rule : prolog_rule =
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
    fun frozen -> fun tm ->
    let (l,r) = dest_eq tm in
    if not (is_num_type (type_of l)) then failwith "num_eq_prolog_rule" else
    orelse_sym_prolog_rule (conv_prolog_rule reduce_conv) frozen tm;;

let mk_bus_prolog_rule : prolog_rule =
    orelse_sym_prolog_rule
      (fun frozen -> fun tm ->
       let (t,n) = dest_eq tm in
       let nn = dest_numeral n in
       let v = dest_width t in
       if not_unfrozen_var frozen v then failwith "mk_bus_prolog_rule" else
       let sub = [(genvar_bus nn, v)] in
       (ASSUME (vsubst sub tm), sub));;

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

(***
let brev_prolog_rule =
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
***)

let connect_wire_prolog_rule : prolog_rule =
    fun frozen -> fun tm ->
    let (x,y) = dest_connect tm in
    if is_unfrozen_var frozen y then (SPEC x connect_refl, [(x,y)])
    else failwith "connect_wire_prolog_rule: frozen";;

let wire_connect_prolog_rule : prolog_rule =
    fun frozen -> fun tm ->
    let (x,y) = dest_connect tm in
    if is_unfrozen_var frozen x then (SPEC y connect_refl, [(y,x)])
    else failwith "wire_connect_prolog_rule: frozen";;

let connect_prolog_rule : prolog_rule =
    orelse_prolog_rule connect_wire_prolog_rule wire_connect_prolog_rule;;

let partition_primary primary th =
    let outputs = map rand (hyp th) in
    partition (not o C mem outputs) primary;;

let rescue_primary_outputs_prolog_rule : term list -> prolog_rule =
    let connect_equal_wires = prove
        (`!w x. connect w x ==> x = w`,
         REPEAT STRIP_TAC THEN
         MATCH_MP_TAC signal_eq_imp THEN
         GEN_TAC THEN
         MATCH_MP_TAC connect_signal THEN
         ASM_REWRITE_TAC []) in
     let connect_conv primary_output =
         let wire = genvar (type_of primary_output) in
         let rescue_th = SPECL [wire; primary_output] connect_equal_wires in
         simple_conv (UNDISCH rescue_th) in
     fun primary_outputs ->
     let rescue_conv = FIRST_CONV (map connect_conv primary_outputs) in
     conv_prolog_rule (ONCE_DEPTH_CONV rescue_conv);;

let rescue_primary_outputs =
    let cleanup_rule =
        try_prolog_rule
          (first_prolog_rule
             [subst_var_prolog_rule;
              connect_wire_prolog_rule]) in
    fun primary_outputs -> fun th ->
    if length primary_outputs = 0 then th else
    let rescue_rule = rescue_primary_outputs_prolog_rule primary_outputs in
    let (th,_) = prove_hyp_prolog_rule rescue_rule primary_outputs th in
    let (th,_) = repeat_prove_hyp_prolog_rule cleanup_rule primary_outputs th in
    th;;

let merge_logic =
    let rec merge_asms th asms =
        match asms with
          [] -> th
        | asm :: asms ->
          if is_connect asm then merge_asms th asms else
          let (f,w) = dest_comb asm in
          let pred h = rator h = f in
          match filter pred asms with
            [] -> merge_asms th asms
          | h :: _ -> merge_thm (INST [(rand h, w)] th)
    and merge_thm th = merge_asms th (hyp th) in
    merge_thm;;

let delete_dead_logic primary_inputs primary_outputs th =
    let defs =
        let mk_def asm = (rand asm, frees (rator asm), asm) in
        map mk_def (hyp th) in
    let find_def wire =
        match filter (fun (w,_,_) -> w = wire) defs with
          [] -> failwith "delete_dead_logic: no definition found for wire"
        | [(_,ws,asm)] -> (ws,asm)
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
    let (delays,wires) = partition (fun (_,_,asm) -> is_delay asm) defs in
    let (alive_delays,alive_wires) =
        let is_delay wire = exists (fun (w,_,_) -> w = wire) delays in
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
        warn true
          (string_of_int n ^ " unused wire" ^
           (if n = 1 then "" else "s")) in
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
         case1_middle_ground; case1_middle_power] in
    fun ths ->
    let user_rules = map thm_prolog_rule ths in
    let rule = first_prolog_rule (basic_rules @ user_rules) in
    let instantiate = repeat_prove_hyp_prolog_rule (repeat_prolog_rule rule) in
    fun primary -> fun th ->
    let (th,_) = instantiate primary th in
    let (primary_inputs,primary_outputs) = partition_primary primary th in
    let th = rescue_primary_outputs primary_outputs th in
    let th = merge_logic th in
(***
    let th = delete_dead_logic primary_inputs primary_outputs th in
***)
    let th = rename_wires primary th in
    th;;

(*** Testing
let mk_asms asms =
    MATCH_MP (TAUT `!t. t ==> T`) (itlist (CONJ o ASSUME) asms TRUTH);;
let frozen : term list = [`x : wire`; `y : wire`; `z : wire`];;
let th = mk_asms [`connect w x`; `connect x y`; `connect y z`];;
rescue_primary_outputs frozen th;;

instantiate_hardware [badder2_def; counter_def] (frees (concl counter91_thm)) counter91_thm;;
***)

(* ------------------------------------------------------------------------- *)
(* Pretty-printing synthesized hardware in Verilog.                          *)
(* ------------------------------------------------------------------------- *)

let hardware_to_verilog =
    let wire_name =
        let wire_ty = `:wire` in
        fun w ->
        let (n,ty) = dest_var w in
        if ty = wire_ty then n else failwith "wire_name" in
    let wire_names = map wire_name in
    let wire_sort =
        let wire_num w =
            let s = wire_name w in
            let s = String.sub s 1 (String.length s - 1) in
            int_of_string s in
        let wire_cmp w1 w2 = wire_num w1 <= wire_num w2 in
        sort wire_cmp in
    let comment_box_text =
        let split s =
            let n = String.length s in
            let rec f i =
                try (if n <= i then [""] else
                     let j = String.index_from s i '\n' in
                     String.sub s i (j - i) :: f (j + 1))
                with Not_found -> [String.sub s i (n - i)] in
            f 0 in
        let line_length = 79 in
        let top = "/*" ^ String.make (line_length - 3) '-' ^ "+" in
        let middle s =
            let space = line_length - (String.length s + 3) in
            "| " ^ s ^ String.make space ' ' ^ "|" in
        let bottom = "+" ^ String.make (line_length - 3) '-' ^ "*/" in
        fun text ->
            top ^ "\n" ^
            String.concat "\n" (map middle (split text)) ^ "\n" ^
            bottom ^ "\n" in
    let verilog_comment name property =
        comment_box_text
          ("module " ^ name ^ " satisfies the following property:\n\n" ^
           string_of_term property) ^ "\n" in
    let verilog_module_begin name wires =
        "module " ^ name ^ "(" ^
        String.concat "," (wire_names wires) ^
        ");" in
    let verilog_wire_declarations kind ws =
        if length ws = 0 then "" else
        ("\n  " ^ kind ^ " " ^
         String.concat (";\n  " ^ kind ^ " ") (wire_names ws) ^
         ";\n") in
    let verilog_connect tm =
        let (x,y) = dest_connect tm in
        wire_name y ^ " = " ^ wire_name x in
    let verilog_delay tm =
        let (w,r) = dest_delay tm in
        wire_name r ^ " <= " ^ wire_name w in
    let verilog_not tm =
        let (x,y) = dest_not tm in
        wire_name y ^ " = ~" ^ wire_name x in
    let verilog_and2 tm =
        let (x,y,z) = dest_and2 tm in
        wire_name z ^ " = " ^ wire_name x ^ " & " ^ wire_name y in
    let verilog_or2 tm =
        let (x,y,z) = dest_or2 tm in
        wire_name z ^ " = " ^ wire_name x ^ " | " ^ wire_name y in
    let verilog_xor2 tm =
        let (x,y,z) = dest_xor2 tm in
        wire_name z ^ " = " ^ wire_name x ^ " ^ " ^ wire_name y in
    let verilog_assignment comb =
        if is_connect comb then verilog_connect comb
        else if is_not comb then verilog_not comb
        else if is_and2 comb then verilog_and2 comb
        else if is_or2 comb then verilog_or2 comb
        else if is_xor2 comb then verilog_xor2 comb
        else failwith ("weird assumption: " ^ string_of_term comb) in
    let verilog_assignments combs wires =
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
        ("\n  assign " ^
         String.concat (";\n  assign ")
           (map (verilog_assignment o find_comb) wires) ^
         ";\n") in
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
    fun name -> fun primary_wires -> fun th ->
    let (delays,combinational) = partition is_delay (hyp th) in
    let (registers,wires) =
        let ws = filter (not o C mem primary_wires) (freesl (hyp th)) in
        let ws = wire_sort ws in
        let delay_outputs = map rand delays in
        partition (C mem delay_outputs) ws in
    let (primary_outputs,primary_inputs) =
        let combinational_outputs = map rand combinational in
        partition (C mem combinational_outputs) primary_wires in
    verilog_comment name (concl th) ^
    verilog_module_begin name (primary_inputs @ primary_outputs) ^
    verilog_wire_declarations "input" primary_inputs ^
    verilog_wire_declarations "output" primary_outputs ^
    verilog_wire_declarations "reg" registers ^
    verilog_wire_declarations "wire" wires ^
    verilog_assignments combinational (wires @ primary_outputs) ^
    verilog_delays (hd primary_wires) delays registers ^
    verilog_module_end name;;

let hardware_to_verilog_file name wires th =
    let file = "opentheory/hardware/" ^ name ^ ".v" in
    let s = hardware_to_verilog name wires th in
    let h = open_out file in
    let () = output_string h s in
    let () = close_out h in
    file;;
