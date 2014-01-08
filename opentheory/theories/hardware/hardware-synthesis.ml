(* ========================================================================= *)
(* HARDWARE SYNTHESIS                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

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
(* Automatically synthesizing hardware.                                      *)
(* ------------------------------------------------------------------------- *)

let num_eq_asm_rule : asm_rule =
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
    let conv =
        REWRITE_CONV [bnil_width; bwire_width; bappend_width] THENC
        NUM_REDUCE_CONV THENC
        TRY_CONV numeral_eq_add_numeral_conv in
    fun asm -> fun th ->
    let (l,r) = dest_eq asm in
    if not (is_num_type (type_of l)) then failwith "num_eq_asm_rule" else
    conv_asm_rule (CHANGED_CONV conv) asm th;;

let mk_bus_asm_rule : asm_rule =
    fun asm -> fun th ->
    let (t,n) = dest_eq asm in
    let nn = dest_numeral n in
    let v = dest_width t in
    if not (is_var v) then failwith "mk_bus_asm_rule" else
    (None, INST [(genvar_bus nn, v)] th);;

let (wire_asm_rule,bsub_asm_rule,bground_asm_rule) =
    let numeral_conv : conv =
        fun tm ->
        if is_numeral tm then REFL tm else
        let th = NUM_REDUCE_CONV tm in
        if is_numeral (rhs (concl th)) then th else
        failwith "numeral_conv" in
    let zero_suc_conv : conv =
        let suc_tm = `SUC` in
        let mk_suc tm = mk_comb (suc_tm,tm) in
        fun tm ->
        let n = dest_numeral tm in
        if eq_num n num_0 then REFL tm else
        let m = mk_suc (mk_numeral (n -/ num_1)) in
        SYM (NUM_SUC_CONV m) in
    let wire_asm_rule =
        let zero_rule = thm_asm_rule wire_zero in
        let suc_rule = thm_asm_rule wire_suc in
        let conv tm =
            let (x,_,_) = dest_wire tm in
            let (w,_) = dest_bappend x in
            let _ = dest_bwire w in
            LAND_CONV (numeral_conv THENC zero_suc_conv) tm in
        then_asm_rule
          (conv_asm_rule conv)
          (orelse_asm_rule zero_rule suc_rule) in
    let bsub_asm_rule =
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
        let suc_rule = thm_asm_rule suc_thm in
        let zero_zero_rule = thm_asm_rule zero_zero_thm in
        let zero_suc_rule = thm_asm_rule zero_suc_thm in
        let conv tm =
            let _ = dest_bsub tm in
            RATOR_CONV
              (LAND_CONV (numeral_conv THENC zero_suc_conv) THENC
               RAND_CONV (numeral_conv THENC zero_suc_conv)) tm in
        then_asm_rule
          (conv_asm_rule conv)
          (orelse_asm_rule
             suc_rule
             (orelse_asm_rule zero_zero_rule zero_suc_rule)) in
    let bground_asm_rule =
        let zero_conv = REWR_CONV bground_zero in
        let suc_conv = REWR_CONV bground_suc in
        let rec expand_conv tm =
            (RAND_CONV zero_suc_conv THENC
             (zero_conv ORELSEC
              (suc_conv THENC
               RAND_CONV expand_conv))) tm in
        let conv tm =
            let _ = dest_bground tm in
            (RAND_CONV numeral_conv THENC expand_conv) tm in
        conv_asm_rule (CHANGED_CONV (DEPTH_CONV conv)) in
    (wire_asm_rule,bsub_asm_rule,bground_asm_rule);;

let merge_wire_asm_rule gvs : asm_rule =
    fun asm -> fun th ->
    if not (mem (rand asm) gvs) then failwith "frozen output" else
    if is_connect asm then
       let (x,y) = dest_connect asm in
       (None, PROVE_HYP (SPEC x connect_refl) (INST [(x,y)] th))
    else
      let (f,w) = dest_comb asm in
      let pred h = rator h = f && not (h = asm) in
      match filter pred (hyp th) with
        [] -> failwith "no merge possible"
      | h :: _ -> (None, INST [(rand h, w)] th);;

let instantiate_hardware =
    let basic_asm_rule =
        let basic_rules =
            [subst_var_asm_rule;
             num_eq_asm_rule;
             mk_bus_asm_rule;
             wire_asm_rule;
             bsub_asm_rule;
             bground_asm_rule] in
        let basic_thms =
            [bconnect_bappend_bwire; bconnect_bnil;
             bdelay_bappend_bwire; bdelay_bnil;
             bnot_bappend_bwire; bnot_bnil;
             band2_bappend_bwire; band2_bnil;
             bor2_bappend_bwire; bor2_bnil;
             bxor2_bappend_bwire; bxor2_bnil;
             bcase1_bappend_bwire; bcase1_bnil;
             case1_middle_ground; case1_middle_power] in
        first_asm_rule (basic_rules @ map thm_asm_rule basic_thms) in
    let merge_wires th =
        let cvs = frees (concl th) in
        let gvs = filter (not o C mem cvs) (freesl (hyp th)) in
        apply_asm_rule (merge_wire_asm_rule gvs) th in
    let rename_wires =
        let rename p w (n,s) =
            (n + 1, (mk_var (p ^ string_of_int n, type_of w), w) :: s) in
        fun th ->
        let cvs = frees (concl th) in
        let gvs = filter (not o C mem cvs) (freesl (hyp th)) in
        let delays = filter is_delay (hyp th) in
        let delay_outputs = map rand delays in
        let (rvs,wvs) = partition (C mem delay_outputs) gvs in
        let (_,sub) = itlist (rename "r") rvs (0,[]) in
        let (_,sub) = itlist (rename "w") wvs (0,sub) in
        INST sub th in
    fun ths ->
    let user_asm_rule = first_asm_rule (map thm_asm_rule ths) in
    let asm_rule = orelse_asm_rule basic_asm_rule user_asm_rule in
    rename_wires o merge_wires o apply_asm_rule asm_rule;;

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

logfile_end ();;
