(* ========================================================================= *)
(* HARDWARE SYNTHESIS                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

#load "unix.cma";;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

module String_map = Map.Make(String);;

let timed f x =
    let t = Unix.gettimeofday() in
    let fx = f x in
    let td = Unix.gettimeofday() -. t in
    (fx,td);;

let complain s =
    let () = output_string stderr (s ^ "\n") in
    let () = flush stderr in
    ();;

let memory_footprint =
    let mb = float_of_int (Sys.word_size / 8) /. (1024.0 *. 1024.0) in
    fun () ->
    let () = Gc.full_major () in
    let {Gc.live_words = m0; Gc.top_heap_words = mx} = Gc.stat () in
    (float_of_int m0 *. mb, float_of_int mx *. mb);;

let complain_timed s f x =
    let (fx,t) = timed f x in
    let t = int_of_float t in
    let (m0,mx) = memory_footprint () in
    let m0 = int_of_float m0 in
    let mx = int_of_float mx in
    let () = complain ("- " ^ s ^ ": " ^ string_of_int t ^ " second" ^ (if t = 1 then "" else "s") ^ " (" ^ string_of_int m0 ^ "-" ^ string_of_int mx ^ "Mb)") in
    fx;;

let random_odd_num w =
    let f n =
        let n = mult_num num_2 n in
        if Random.bool () then add_num n num_1 else n in
    let n = funpow (w - 2) f num_1 in
    add_num (mult_num num_2 n) num_1;;

let maps (f : 'a -> 's -> 'b * 's) =
    let rec m xs s =
        match xs with
          [] -> ([],s)
        | x :: xs ->
          let (y,s) = f x s in
          let (ys,s) = m xs s in
          (y :: ys, s) in
     m;;

let find_max cmp =
    let f x m = if cmp m x then x else m in
    fun xs ->
    match rev xs with
      [] -> failwith "find_max: empty list"
    | x :: xs -> itlist f xs x;;

let disjoint xs =
    let notmem x = not (mem x xs) in
    forall notmem;;

let translate f s =
    let rec tr acc i =
        if i = 0 then String.concat "" acc else
        let i = i - 1 in
        let c = String.get s i in
        tr (f c :: acc) i in
    tr [] (String.length s);;

let split c s =
    let rec split_from i =
    try (let j = String.index_from s i c in
         let (x,xs) = split_from (j + 1) in
         (String.sub s i (j - i), x :: xs))
    with Not_found -> (String.sub s i (String.length s - i), []) in
    split_from 0;;

let deprime s = fst (split '\'' s);;

let is_true =
    let true_tm = `T` in
    fun tm -> tm = true_tm;;

let mk_one_var =
    let one_ty = `:1` in
    fun s -> mk_var (s,one_ty);;

let null_subst (sub : (term * term) list) =
    match sub with
      [] -> true
    | _ -> false;;

let compose_subst old_sub new_sub =
    if null_subst new_sub then old_sub else
    let apply_new_sub (t,v) = (vsubst new_sub t, v) in
    map apply_new_sub old_sub @ new_sub;;

let simple_conv th =
    let redex = lhs (concl th) in
    fun tm -> if tm = redex then th else failwith "simple_conv";;

let orelse_sym_conv : conv -> conv =
    let rewr = REWR_CONV EQ_SYM_EQ in
    fun c -> c ORELSEC (rewr THENC c);;

let undisch_bind th =
    let (tm,_) = dest_imp (concl th) in
    (tm, UNDISCH th);;

let string_of_subst =
    let maplet (t,v) = string_of_term v ^ " |-> " ^ string_of_term t ^ "\n" in
    fun sub ->
    "<sub> [" ^ (if length sub = 0 then "" else ("\n  " ^ String.concat "\n  " (map maplet sub))) ^ "]";;

(* ------------------------------------------------------------------------- *)
(* A special exception for synthesis bugs.                                   *)
(* ------------------------------------------------------------------------- *)

exception Synthesis_bug of string;;

(* ------------------------------------------------------------------------- *)
(* Efficiently store sets of variables.                                      *)
(* ------------------------------------------------------------------------- *)

type varset = Varset of hol_type list String_map.t;;

let empty_varset = Varset String_map.empty;;

let mem_varset v (Varset m) =
    let (s,ty) = dest_var v in
    String_map.mem s m &&
    mem ty (String_map.find s m);;

let add_varset v vs =
    if mem_varset v vs then vs else
    let Varset m = vs in
    let (s,ty) = dest_var v in
    let l = if String_map.mem s m then String_map.find s m else [] in
    Varset (String_map.add s (ty :: l) m);;

let add_list_varset vl vs = rev_itlist add_varset vl vs;;

let from_list_varset vl = add_list_varset vl empty_varset;;

let variant_varset vs v =
    if not (mem_varset v vs) then v else
    let (s,ty) = dest_var v in
    let rec f s =
        let s' = s ^ "'" in
        let v' = mk_var (s',ty) in
        if mem_varset v' vs then f s' else v' in
    f s;;

(* ------------------------------------------------------------------------- *)
(* Name generators.                                                          *)
(* ------------------------------------------------------------------------- *)

type scope = string * varset;;

type namer = Namer of varset * scope * scope list;;

let scope_to_string sc = if sc = "" then "<global>" else sc;;

let frozen_vars (Namer (x,_,_)) = x;;

let current_scope (Namer (_,(x,_),_)) = x;;

let current_scope_vars (Namer (_,(_,x),_)) = x;;

let new_namer frozen =
    let vs = from_list_varset frozen in
    Namer (vs,("",vs),[]);;

let is_unfrozen_var namer v =
    is_var v && not (mem_varset v (frozen_vars namer));;

let not_unfrozen_var namer v = not (is_unfrozen_var namer v);;

let fresh_var v namer =
    let Namer (f,(sc,vs),sl) = namer in
    let v =
        if String.length sc = 0 then v else
        let (s,ty) = dest_var v in
        mk_var (sc ^ "." ^ s, ty) in
    let v = variant_varset vs v in
    let vs = add_varset v vs in
    let namer = Namer (f,(sc,vs),sl) in
    (v,namer);;

let freshen_vars vs namer =
    let (vs',namer) = maps fresh_var vs namer in
    (zip vs' vs, namer);;

let narrow_scope s namer =
    if String.length s = 0 then namer else
    let (sc,namer) = fresh_var (mk_one_var s) namer in
    let Namer (f,sc_vs,sl) = namer in
    let (sc,_) = dest_var sc in
    let vs = empty_varset in
    let sl = sc_vs :: sl in
    Namer (f,(sc,vs),sl);;

let widen_scope s namer =
    let rec pop sl =
        match sl with
          [] -> raise (Synthesis_bug "widen_scope.pop: no match")
        | (sc,vs) :: sl -> if s = sc then ((sc,vs),sl) else pop sl in
    let Namer (f,(sc,vs),sl) = namer in
    if s = sc then namer else
    let (sc_vs,sl) = pop sl in
    Namer (f,sc_vs,sl);;

(* ------------------------------------------------------------------------- *)
(* Prolog rules allow backward reasoning on theorem assumptions.             *)
(* ------------------------------------------------------------------------- *)

type prolog_result =
     Prolog_result of term list * thm * (term * term) list * namer
   | Prolog_unchanged;;

type prolog_rule = Prolog_rule of (term -> namer -> prolog_result);;

type prolog_object =
     Goal_prolog_object of term
   | Sub_prolog_object of (term * term) list;;

let all_prolog_rule =
    Prolog_rule (fun _ -> fun _ -> Prolog_unchanged);;

let no_prolog_rule =
    Prolog_rule (fun _ -> fun _ -> failwith "no_prolog_rule");;

let apply_prolog_rule (Prolog_rule pr) goal namer =
    let subgoals_th_sub_namer = pr goal namer in
(* Debugging
    let (subgoals,th,sub,_) = subgoals_th_sub_namer in
    let () =
        let n = length subgoals in
        let msg = "apply_prolog_rule: reducing goal\n" ^ string_of_term goal ^ "\nto " ^ string_of_int n ^ " subgoal" ^ (if n = 1 then "" else "s") ^ (if n = 0 then "" else ":\n" ^ String.concat "\n" (map string_of_term subgoals)) ^ "\nusing theorem:\n" ^ string_of_thm th ^ "\n" in
        print_string msg in
    let () =
        let goal' = vsubst sub goal in
        if aconv goal' (concl th) then () else
        let () = complain ("using substitution\n" ^ string_of_subst sub ^ "\nconclusion of\n" ^ string_of_thm th ^ "\ndoesn't match goal[substitution]\n" ^ string_of_term goal' ^ "\n") in
        raise (Synthesis_bug "apply_prolog_rule: conclusion doesn't match goal[substitution]") in
    let () =
        let tms = hyp th in
        let check tm =
            if mem tm tms then () else
            let () = complain ("subgoal\n" ^ string_of_term tm ^ "\nnot a hypothesis in\n" ^ string_of_thm th ^ "\n") in
            raise (Synthesis_bug "apply_prolog_rule: subgoal not a hypothesis") in
        List.iter check tms in
*)
    subgoals_th_sub_namer;;

let unchanged_apply_prolog_rule (Prolog_rule pr) goal namer =
    match pr goal namer with
      Prolog_result (subgoals,th,sub,namer) -> (subgoals,th,sub,namer)
    | Prolog_unchanged -> ([goal], ASSUME goal, [], namer);;

let check_prolog_rule f pr =
    Prolog_rule
      (fun goal -> fun namer ->
       let () = f goal in
       apply_prolog_rule pr goal namer);;

let orelse_prolog_rule pr1 pr2 =
    Prolog_rule
      (fun goal -> fun namer ->
       try (apply_prolog_rule pr1 goal namer)
       with Failure _ -> apply_prolog_rule pr2 goal namer);;

let try_prolog_rule pr =
    orelse_prolog_rule pr all_prolog_rule;;

let first_prolog_rule =
    let rec first prs =
        match prs with
          [] -> no_prolog_rule
        | pr :: prs -> orelse_prolog_rule pr (first prs) in
    first;;

let prove_hyp_prolog_rule pr =
    let finalize_asm sub asm acc = vsubst sub asm :: acc in
    let rec finalize_asms acc sub asmsl =
        match asmsl with
          [] -> acc
        | (gsub,asms) :: asmsl ->
          let sub = compose_subst gsub sub in
          let acc = rev_itlist (finalize_asm sub) asms acc in
          finalize_asms acc sub asmsl in
    let rec prolog_asms asms asmsl th sub namer goals =
        match goals with
          [] -> (finalize_asms (rev asms) [] asmsl, th, sub, namer)
        | goal :: goals ->
          let goal = vsubst sub goal in
          match apply_prolog_rule pr goal namer with
            Prolog_result (gasms,gth,gsub,gnamer) ->
              let namer = widen_scope (current_scope namer) gnamer in
              let (asms,asmsl,th,sub) =
                  if null_subst gsub then
                    let asms = List.rev_append gasms asms in
                    let th = PROVE_HYP gth th in
                    (asms,asmsl,th,sub)
                  else
                    let asmsl = (gsub,asms) :: asmsl in
                    let asms = rev gasms in
                    let th = PROVE_HYP gth (INST gsub th) in
                    let sub = compose_subst sub gsub in
                    (asms,asmsl,th,sub) in
              prolog_asms asms asmsl th sub namer goals
          | Prolog_unchanged ->
              let asms = goal :: asms in
              prolog_asms asms asmsl th sub namer goals in
    fun goals -> fun th -> fun namer ->
    prolog_asms [] [] th [] namer goals;;

let then_prolog_rule pr1 pr2 =
    Prolog_rule
      (fun goal -> fun namer0 ->
       match apply_prolog_rule pr1 goal namer0 with
         Prolog_result (asms,th,sub1,namer) ->
           let (asms,th,sub2,namer) =
               prove_hyp_prolog_rule pr2 asms th namer in
           let sub = compose_subst sub1 sub2 in
           let namer = widen_scope (current_scope namer0) namer in
           Prolog_result (asms,th,sub,namer)
       | Prolog_unchanged ->
           apply_prolog_rule pr2 goal namer0);;

let repeat_prove_hyp_prolog_rule pr =
    let rollback_asm gsub asm goals =
        Goal_prolog_object (vsubst gsub asm) :: goals in
    let rec rollback_asms gsub gsubdom asms fvs asmsl goals =
        let goals = rev_itlist (rollback_asm gsub) asms goals in
        if disjoint fvs gsubdom then (fvs,asmsl,goals) else
        match asmsl with
          [] -> raise (Synthesis_bug "repeat_prove_hyp_prolog_rule.rollback_asms")
        | (asms,fvs) :: asmsl ->
          rollback_asms gsub gsubdom asms fvs asmsl goals in
    let rec finalize_asms acc asmsl =
        match asmsl with
          [] -> acc
        | (asms,_) :: asmsl ->
          let acc = List.rev_append asms acc in
          finalize_asms acc asmsl in
    let rec prolog_asms asms fvs asmsl th sub namer goals =
        match goals with
          [] -> (finalize_asms (rev asms) asmsl, th, sub, namer)
        | Sub_prolog_object oldsub :: goals ->
          prolog_asms asms fvs asmsl th (compose_subst oldsub sub) namer goals
        | Goal_prolog_object goal :: goals ->
          let goal = vsubst sub goal in
(* Debugging
          let () =
              let msg = "goal = " ^ string_of_term goal ^ "\n" in
              print_string msg in
          let () =
              let msg = "sub = " ^ string_of_subst th ^ "\n" in
              print_string msg in
          let () =
              let msg = "th = " ^ string_of_thm th ^ "\n" in
              print_string msg in
*)
          match apply_prolog_rule pr goal namer with
            Prolog_result (gasms,gth,[],gnamer) ->
              let th = PROVE_HYP gth th in
              let namer = widen_scope (current_scope namer) gnamer in
              let asms = List.rev_append gasms asms in
              prolog_asms asms fvs asmsl th sub namer goals
          | Prolog_result (gasms,gth,gsub,gnamer) ->
              let th = PROVE_HYP gth (INST gsub th) in
              let sub = compose_subst sub gsub in
              let namer = widen_scope (current_scope namer) gnamer in
              let fvs' = union fvs (freesl asms) in
(* Debugging
              let () =
                  let n = length fvs' in
                  let msg = "processed goals contain " ^ string_of_int n ^ " free variable" ^ (if n = 1 then "" else "s") ^ " in scope " ^ scope_to_string (current_scope namer) in
                  complain msg in
*)
              let gsubdom = map snd gsub in
              if disjoint fvs' gsubdom then
                let asmsl = (asms,fvs) :: asmsl in
                prolog_asms (rev gasms) fvs' asmsl th sub namer goals
              else
                let goals =
                    map (fun gasm -> Goal_prolog_object gasm) gasms @
                    Sub_prolog_object sub ::
                    goals in
                let (fvs,asmsl,goals') =
                    rollback_asms gsub gsubdom asms fvs asmsl goals in
(* Debugging
                let () =
                    let n = length goals' - length goals in
                    let msg = "rolling back " ^ string_of_int n ^ " goal" ^ (if n = 1 then "" else "s") ^ " in scope " ^ scope_to_string (current_scope namer) in
                    complain msg in
*)
                prolog_asms [] fvs asmsl th [] namer goals'
            | Prolog_unchanged ->
                let asms = goal :: asms in
                prolog_asms asms fvs asmsl th sub namer goals in
    fun asms -> fun th -> fun namer ->
    let goals = map (fun asm -> Goal_prolog_object asm) asms in
    prolog_asms [] [] [] th [] namer goals;;

let then_repeat_prolog_rule pr1 pr2 =
    Prolog_rule
      (fun goal -> fun namer0 ->
       match apply_prolog_rule pr1 goal namer0 with
         Prolog_result (asms,th,sub1,namer) ->
           let (asms,th,sub2,namer) =
               repeat_prove_hyp_prolog_rule pr2 asms th namer in
           let sub = compose_subst sub1 sub2 in
           let namer = widen_scope (current_scope namer0) namer in
           Prolog_result (asms,th,sub,namer)
       | Prolog_unchanged ->
           apply_prolog_rule pr2 goal namer0);;

let rec repeat_prolog_rule pr =
    Prolog_rule
      (fun goal -> fun namer ->
       let rule =
           try_prolog_rule
             (then_repeat_prolog_rule pr (repeat_prolog_rule pr)) in
       apply_prolog_rule rule goal namer);;

let scope_thm_prolog_rule =
    let mk_prolog_thm =
        let eq_to_imp_thm = MATCH_MP (TAUT `(a <=> b) ==> (b ==> a)`) in
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
                let (asm,th) = undisch_bind th in
                let (asms,th) = collect th in
                (asm :: asms, th) in
            collect in
        let norm_imp_thm th =
            let th = SPEC_ALL (pull_exists th) in
            let (asms,conc) = dest_imp (concl th) in
            let vs = filter (not o C mem (frees conc)) (frees asms) in
            let (asms,th) = collect_asms th in
            (vs,asms,th) in
        fun th ->
        let th = SPEC_ALL th in
        let th = if is_iff (concl th) then eq_to_imp_thm th else th in
        if is_imp (concl th) then norm_imp_thm th else ([],[],th) in
    let prolog_thm_rule s (vs,asms,th) =
        let pat = concl th in
        Prolog_rule
          (fun tm -> fun namer ->
           let (_,sub,_) = term_match [] pat tm in
           let namer = narrow_scope s namer in
           let (vs_sub,namer) = freshen_vars vs namer in
           let sub = vs_sub @ sub in
           let asms = map (vsubst sub) asms in
           let th = INST sub th in
           Prolog_result (asms,th,[],namer)) in
    fun s -> fun th ->
    prolog_thm_rule s (mk_prolog_thm th);;

let thm_prolog_rule = scope_thm_prolog_rule "";;

let conv_prolog_rule (conv : conv) =
    Prolog_rule
      (fun tm -> fun namer ->
       let eq_th = conv tm in
       let tm' = rhs (concl eq_th) in
       if is_true tm' then
         let th = EQT_ELIM eq_th in
         Prolog_result ([],th,[],namer)
       else if tm' = tm then
         Prolog_unchanged
       else
         let th = EQ_MP (SYM eq_th) (ASSUME tm') in
         Prolog_result ([tm'],th,[],namer));;

let sym_prolog_rule : prolog_rule =
    Prolog_rule
      (fun tm -> fun namer ->
       let (l,r) = dest_eq tm in
       let stm = mk_eq (r,l) in
       Prolog_result ([stm], SYM (ASSUME stm), [], namer));;

let orelse_sym_prolog_rule pr =
    orelse_prolog_rule pr (then_prolog_rule sym_prolog_rule pr);;

let subst_var_prolog_rule =
    orelse_sym_prolog_rule
      (Prolog_rule
         (fun tm -> fun namer ->
          let (l,r) = dest_eq tm in
          if is_unfrozen_var namer l then
            Prolog_result ([], REFL r, [(r,l)], namer)
          else failwith "subst_var_prolog_rule"));;

(* ------------------------------------------------------------------------- *)
(* Extracting information from a synthesized circuit.                        *)
(* ------------------------------------------------------------------------- *)

let ckt_logic' th = hyp th;;

let wire_defn' logic w =
    match filter (fun g -> rand g = w) logic with
      [] -> failwith "wire_defn: no definition"
    | [g] -> g
    | _ :: _ :: _ -> failwith "wire_defn: multiple definitions";;

let wire_fanin1' logic w = frees (rator (wire_defn' logic w));;

let ckt_wires' logic = freesl logic;;

let ckt_primary_inputs' logic wires =
    subtract wires (map rand logic);;

let ckt_primary_outputs' logic =
    map (snd o dest_connect) (filter is_connect logic);;

let ckt_delays' logic =
    map (snd o dest_delay) (filter is_delay logic);;

let ckt_gates' logic =
    let pred g = not (is_delay g) && not (is_connect g) in
    filter pred logic;;

let wire_fanin' logic primary_inputs =
    let rec f fringe cone ws =
        match ws with
          [] -> (fringe,cone)
        | w :: ws ->
          if mem w fringe then f fringe cone ws else
          if mem w cone then f fringe cone ws else
          if mem w primary_inputs then f (w :: fringe) cone ws else
          let g = wire_defn' logic w in
          if is_delay g then f (w :: fringe) cone ws else
          f fringe (w :: cone) (frees (rator g) @ ws) in
    fun w -> f [] [] (wire_fanin1' logic w);;

let ckt_fanin' logic primary_inputs primary_outputs delays =
    let fanin w = (w, wire_fanin' logic primary_inputs w) in
    map fanin (primary_outputs @ delays);;

let wire_fanout' (fanin : (term * (term list * term list)) list) w =
    let add (v,(f,_)) z = if mem w f then v :: z else z in
    itlist add fanin [];;

let ckt_fanout' (primary_inputs : term list) delays fanin =
    map (fun w -> (w, wire_fanout' fanin w)) (primary_inputs @ delays);;

let ckt_logic = ckt_logic';;

let ckt_wires th =
    let logic = ckt_logic' th in
    ckt_wires' logic;;

let ckt_primary_inputs th =
    let logic = ckt_logic' th in
    let wires = ckt_wires' logic in
    ckt_primary_inputs' logic wires;;

let ckt_delays th =
    let logic = ckt_logic' th in
    ckt_delays' logic;;

let ckt_primary_outputs th =
    let logic = ckt_logic' th in
    ckt_primary_outputs' logic;;

let ckt_gates th =
    let logic = ckt_logic' th in
    ckt_gates' logic;;

let wire_fanin th =
    let logic = ckt_logic' th in
    let wires = ckt_wires' logic in
    let primary_inputs = ckt_primary_inputs' logic wires in
    wire_fanin' logic primary_inputs;;

let ckt_fanin th =
    let logic = ckt_logic' th in
    let wires = ckt_wires' logic in
    let primary_inputs = ckt_primary_inputs' logic wires in
    let primary_outputs = ckt_primary_outputs' logic in
    let delays = ckt_delays' logic in
    ckt_fanin' logic primary_inputs primary_outputs delays;;

let wire_fanout th =
    let logic = ckt_logic' th in
    let wires = ckt_wires' logic in
    let primary_inputs = ckt_primary_inputs' logic wires in
    let primary_outputs = ckt_primary_outputs' logic in
    let delays = ckt_delays' logic in
    let fanin = ckt_fanin' logic primary_inputs primary_outputs delays in
    wire_fanout' fanin;;

let ckt_fanout th =
    let logic = ckt_logic' th in
    let wires = ckt_wires' logic in
    let primary_inputs = ckt_primary_inputs' logic wires in
    let primary_outputs = ckt_primary_outputs' logic in
    let delays = ckt_delays' logic in
    let fanin = ckt_fanin' logic primary_inputs primary_outputs delays in
    ckt_fanout' primary_inputs delays fanin;;

(* ------------------------------------------------------------------------- *)
(* Elaborating circuits by expanding module definitions and bit blasting     *)
(* bus variables once their width is known.                                  *)
(* ------------------------------------------------------------------------- *)

let is_synthesizable tm =
    is_connect tm or
    is_not tm or
    is_and2 tm or
    is_or2 tm or
    is_xor2 tm or
    is_case1 tm or
    is_delay tm;;

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
          let b = variable_bus (fst (dest_var v)) nn in
          let sub = [(b,v)] in
          let asm = vsubst sub tm in
          Prolog_result ([asm], ASSUME asm, sub, namer)));;

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

let elaboration_rule =
    let rules =
        [subst_var_prolog_rule;
         num_simp_prolog_rule;
         num_eq_prolog_rule;
         mk_bus_prolog_rule;
         wire_prolog_rule;
         bsub_prolog_rule;
         brev_prolog_rule;
         bground_prolog_rule] @
        map thm_prolog_rule
        [bconnect_bappend_bwire; bconnect_bnil;
         bdelay_bappend_bwire; bdelay_bnil;
         bnot_bappend_bwire; bnot_bnil;
         band2_bappend_bwire; band2_bnil;
         bor2_bappend_bwire; bor2_bnil;
         bxor2_bappend_bwire; bxor2_bnil;
         bcase1_bappend_bwire; bcase1_bnil] in
    fun syn ->
    let user_rules = map (uncurry scope_thm_prolog_rule) syn in
    repeat_prolog_rule (first_prolog_rule (rules @ user_rules));;

let elaborate_circuit =
    let check_elaboration tms =
        match filter (not o is_synthesizable) tms with
          [] -> ()
        | bad ->
          let n = length bad in
          let s = "term" ^ (if n = 1 then "" else "s") in
          let () = complain ("\n" ^ string_of_int n ^ " unsynthesizable " ^ s ^ ":") in
          let () = List.iter (complain o string_of_term) bad in
          failwith ("couldn't reduce " ^ string_of_int n ^ " " ^ s) in
    fun syn ->
    let rule = elaboration_rule syn in
    fun th -> fun namer ->
    let (tms,th,_,namer) =
        repeat_prove_hyp_prolog_rule rule (hyp th) th namer in
(* Debugging
    let () =
        let n = length (current_scope_vars namer) in
        let () = complain ("elaborate_circuit: " ^ string_of_int n ^ " variable" ^ (if n = 1 then "" else "s") ^ " in global scope") in
        () in
*)
    let () = check_elaboration tms in
    (th,namer);;

(* ------------------------------------------------------------------------- *)
(* Simplifying circuits by merging connecting wires (using a union-find      *)
(* algorithm) and propagating constants through the logic.                   *)
(* ------------------------------------------------------------------------- *)

type class_rep =
     Frozen_class_rep of term
   | Wire_class_rep of string;;

type class_entry =
     Root_class_entry of class_rep
   | Another_class_entry of int;;

type wire_class =
     Wire_class of int * int String_map.t * class_entry Int_map.t;;

let sub_class_rep w r =
    match r with
      Frozen_class_rep tm -> [(tm, mk_wire_var w)]
    | Wire_class_rep s ->
      if s = w then [] else [(mk_wire_var s, mk_wire_var w)];;

let lt_class_rep r1 r2 =
    match r2 with
      Frozen_class_rep _ -> false
    | Wire_class_rep w2 ->
      match r1 with
        Frozen_class_rep _ -> true
      | Wire_class_rep w1 ->
        String.length w1 < String.length w2;;

let size_wire_class (Wire_class (n,_,_)) = n;;

let null_wire_class wc = size_wire_class wc = 0;;

let empty_wire_class = Wire_class (0,String_map.empty,Int_map.empty);;

let find_wire_class =
    let rec find i cls =
        match Int_map.find i cls with
          Root_class_entry r -> (i,r,cls)
        | Another_class_entry j ->
          let (k,r,cls) = find j cls in
          let cls =
              if j = k then cls else
              Int_map.add i (Another_class_entry k) cls in
          (k,r,cls) in
    fun w -> fun (Wire_class (n,ws,cls)) ->
    if String_map.mem w ws then
      let i = String_map.find w ws in
      let (k,r,cls) = find i cls in
      (k, r, Wire_class (n,ws,cls))
    else
      let ws = String_map.add w n ws in
      let r = Wire_class_rep w in
      let cls = Int_map.add n (Root_class_entry r) cls in
      (n, r, Wire_class (n + 1, ws, cls));;

let union_wire_class k1 k2 (Wire_class (n,ws,cls)) =
    let ce = Another_class_entry k2 in
    Wire_class (n, ws, Int_map.add k1 ce cls);;

let update_wire_class k tm (Wire_class (n,ws,cls)) =
    let ce = Root_class_entry (Frozen_class_rep tm) in
    Wire_class (n, ws, Int_map.add k ce cls);;

let sub_wire_class =
    let add w _ (sub,wc) =
        let (_,r,wc) = find_wire_class w wc in
        let sub = sub_class_rep w r @ sub in
        (sub,wc) in
    fun wc ->
    let Wire_class (_,ws,_) = wc in
    String_map.fold add ws ([],wc);;

let connect_wires namer =
    let add asm wc =
        if not (is_connect asm) then wc else
        let (w1,w2) = dest_connect asm in
        let v1 = is_unfrozen_var namer w1 in
        let v2 = is_unfrozen_var namer w2 in
        if v1 then
          let (k1,r1,wc) = find_wire_class (dest_wire_var w1) wc in
          if v2 then
            let (k2,r2,wc) = find_wire_class (dest_wire_var w2) wc in
            if k1 = k2 then wc else
            if lt_class_rep r2 r1 then union_wire_class k1 k2 wc else
            union_wire_class k2 k1 wc
          else
            update_wire_class k1 w2 wc
        else if v2 then
          let (k2,r2,wc) = find_wire_class (dest_wire_var w2) wc in
          update_wire_class k2 w1 wc
        else
          wc in
     fun th ->
     let wc = rev_itlist add (hyp th) empty_wire_class in
     let (sub,_) = sub_wire_class wc in
     match sub with
       [] -> None
     | _ -> Some (INST sub th);;

let simplify_prolog_rule =
    let rules =
        map thm_prolog_rule
        [connect_refl;
         not_ground; not_power;
         and2_left_ground; and2_right_ground;
         and2_left_power; and2_right_power;
         and2_refl;
         or2_left_ground; or2_right_ground;
         or2_left_power; or2_right_power;
         or2_refl;
         xor2_left_ground; xor2_right_ground;
         xor2_left_power; xor2_right_power;
         xor2_refl;
         case1_left_ground; case1_left_power;
         case1_middle_power;
         case1_right_ground;
         case1_refl;
         case1_middle_ground_right_power;
         (* The following simplification rules introduce new wires, so *)
         (* we put them last in the list *)
         case1_middle_ground;
         case1_right_power] in
    repeat_prolog_rule (first_prolog_rule rules);;

let simplify_circuit =
    let rec simplify th namer =
        let (_,th,_,namer) =
            complain_timed "- Propagated constant wires"
              (prove_hyp_prolog_rule simplify_prolog_rule (hyp th) th) namer in
        match complain_timed "- Connected wires" (connect_wires namer) th with
          None -> (th,namer)
        | Some th -> simplify th namer in
    fun th -> fun namer ->
(* Debugging
    let () =
        let print_goal goal = complain ("  " ^ string_of_term goal) in
        let n = length goals in
        let () = complain ("simplify_circuit: " ^ string_of_int n ^ " assumption" ^ (if n = 1 then "" else "s") ^ " to simplify:") in
        let () = List.iter print_goal (hyp th) in
        () in
*)
    let th =
        match complain_timed "- Connected wires" (connect_wires namer) th with
          None -> th
        | Some th -> th in
    simplify th namer;;

(* ------------------------------------------------------------------------- *)
(* Rescue a primary output P that is used as an internal wire in the circuit *)
(* by renaming it to a new internal wire P_o that drives the output P.       *)
(* ------------------------------------------------------------------------- *)

let connect_wire_prolog_rule =
    Prolog_rule
      (fun tm -> fun namer ->
       let (x,y) = dest_connect tm in
       if is_unfrozen_var namer y then
         Prolog_result ([], SPEC x connect_refl, [(x,y)], namer)
       else failwith "connect_wire_prolog_rule");;

let wire_connect_prolog_rule =
    Prolog_rule
      (fun tm -> fun namer ->
       let (x,y) = dest_connect tm in
       if is_unfrozen_var namer x then
         Prolog_result ([], SPEC y connect_refl, [(y,x)], namer)
       else failwith "wire_connect_prolog_rule");;

let connect_prolog_rule =
    Prolog_rule
      (fun tm -> fun namer ->
       let (x,y) = dest_connect tm in
       let (w2,w1) =
           if is_unfrozen_var namer x then
             if is_unfrozen_var namer y then
               let sx = dest_wire_var x in
               let sy = dest_wire_var y in
               if String.length sy < String.length sx then (y,x) else (x,y)
             else (y,x)
           else if is_unfrozen_var namer y then (x,y)
           else failwith "connect_prolog_rule" in
       Prolog_result ([], SPEC w2 connect_refl, [(w2,w1)], namer));;

let rescue_primary_outputs_conv =
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
     let conv = ONCE_DEPTH_CONV (FIRST_CONV convs) in
     (conv,namer);;

let rescue_primary_outputs_prolog_rule primary_outputs namer =
    let (conv,namer) = rescue_primary_outputs_conv primary_outputs namer in
    (conv_prolog_rule conv, namer);;

let rescue_primary_outputs =
    let cleanup_rule = try_prolog_rule connect_wire_prolog_rule in
    fun primary_outputs -> fun th -> fun namer ->
    let (rescue_rule,namer) =
        rescue_primary_outputs_prolog_rule primary_outputs namer in
    let (_,th,_,namer) =
        complain_timed "- Interposed wires before primary outputs"
          (prove_hyp_prolog_rule rescue_rule (hyp th) th) namer in
    let asms = filter is_connect (hyp th) in
(* Debugging
    let () =
        let print_asm asm = complain ("  " ^ string_of_term asm) in
        let n = length asms in
        let () = complain ("rescue_primary_outputs: " ^ string_of_int n ^ " assumption" ^ (if n = 1 then "" else "s") ^ " to clean up:") in
        let () = List.iter print_asm asms in
        () in
*)
    let (_,th,_,namer) =
        complain_timed "- Cleaned up"
          (repeat_prove_hyp_prolog_rule cleanup_rule asms th) namer in
    (th,namer);;

(* ------------------------------------------------------------------------- *)
(* Merge syntactically identical logic using Hopcroft's algorithm.           *)
(* ------------------------------------------------------------------------- *)

let merge_logic_initialize =
    let add_gate asm (wire_inps,wire_cls,clses) =
        if is_connect asm then (wire_inps,wire_cls,clses) else
        let (w,inps,cls) =
            if is_not asm then
              let (x,w) = dest_not asm in
              (w,[x],0)
            else if is_and2 asm then
              let (x,y,w) = dest_and2 asm in
              (w,[x;y],1)
            else if is_or2 asm then
              let (x,y,w) = dest_or2 asm in
              (w,[x;y],2)
            else if is_xor2 asm then
              let (x,y,w) = dest_xor2 asm in
              (w,[x;y],3)
            else if is_case1 asm then
              let (x,y,z,w) = dest_case1 asm in
              (w,[x;y;z],4)
            else if is_delay asm then
              let (x,w) = dest_delay asm in
              (w,[x],5)
            else
              failwith ("merge_logic: bad gate:\n  " ^ string_of_term asm) in
        let w = dest_wire_var w in
        let inps = map dest_wire_var inps in
        let wire_inps = String_map.add w inps wire_inps in
        let wire_cls = String_map.add w cls wire_cls in
        let ws = if Int_map.mem cls clses then Int_map.find cls clses else [] in
        let clses = Int_map.add cls (w :: ws) clses in
        (wire_inps,wire_cls,clses) in
    let init_class _ ws acc =
        match ws with
          [_] -> acc
        | _ -> ws :: acc in
    let add_primary_input w (nxt_cls,wire_cls) =
        let w = dest_wire_var w in
        let wire_cls = String_map.add w nxt_cls wire_cls in
        (nxt_cls + 1, wire_cls) in
    fun primary_inputs -> fun ckt ->
        let wire_inps = String_map.empty in
        let wire_cls = String_map.empty in
        let clses = Int_map.empty in
        let (wire_inps,wire_cls,clses) =
            rev_itlist add_gate (hyp ckt) (wire_inps,wire_cls,clses) in
        let clses = Int_map.fold init_class clses [] in
        let nxt_cls = 6 in
        let (nxt_cls,wire_cls) =
            rev_itlist add_primary_input primary_inputs (nxt_cls,wire_cls) in
        (wire_inps,nxt_cls,wire_cls,clses);;

let merge_logic_refine =
    let rec lt_category k1 k2 =
        match (k1,k2) with
          ([],[]) -> false
        | (i1 :: k1, i2 :: k2) -> i1 < i2 or (i1 <= i2 && lt_category k1 k2)
        | _ -> failwith "merge_logic_refine.lt_category" in
    let compare_category (k1,_) (k2,_) = lt_category k1 k2 in
    let sort_category kws = mergesort compare_category kws in
    let rec eq_category k1 k2 =
        match (k1,k2) with
          ([],[]) -> true
        | (i1 :: k1, i2 :: k2) -> i1 = i2 && eq_category k1 k2
        | _ -> failwith "merge_logic_refine.eq_category" in
    let group_category =
        let rec grp acc k ws kws =
            match kws with
              [] -> ws :: acc
            | (k',w) :: kws ->
              if eq_category k' k then grp acc k (w :: ws) kws
              else grp (ws :: acc) k' [w] kws in
        fun kws ->
        match kws with
          [] -> []
        | (k,w) :: kws -> grp [] k [w] kws in
    fun wire_inps ->
    let classify wire_cls w = String_map.find w wire_cls in
    let categorize wire_cls w =
        let ws = String_map.find w wire_inps in
        (map (classify wire_cls) ws, w) in
    let split wire_cls cls =
        group_category (sort_category (map (categorize wire_cls) cls)) in
    let add_new cls (nxt_cls,wire_cls,clses) =
        let update w w_cls = String_map.add w nxt_cls w_cls in
        let wire_cls = rev_itlist update cls wire_cls in
        let clses = match cls with [_] -> clses | _ -> cls :: clses in
        (nxt_cls + 1, wire_cls, clses) in
    let refine cls (nxt_cls,wire_cls,clses) =
        match split wire_cls cls with
          [_] -> (nxt_cls, wire_cls, cls :: clses)
        | subcls -> rev_itlist add_new subcls (nxt_cls,wire_cls,clses) in
    fun nxt_cls -> fun wire_cls -> fun clses ->
    rev_itlist refine clses (nxt_cls,wire_cls,[]);;

let merge_logic_refine_loop wire_inps =
    let rec loop nxt_cls wire_cls clses =
        let (nxt_cls',wire_cls',clses') =
            merge_logic_refine wire_inps nxt_cls wire_cls clses in
        if nxt_cls' = nxt_cls then clses else loop nxt_cls' wire_cls' clses' in
    loop;;

let merge_logic_substitution =
    let lt_wire w1 w2 = String.length w1 < String.length w2 in
    let add_wire w x sub =
(* Debugging
        let () =
            let msg =
                "Merging wires " ^ string_of_term w ^
                " and " ^ string_of_term x in
            complain msg in
*)
        (w,x) :: sub in
    let add_cls cls sub =
        match map mk_wire_var (mergesort lt_wire cls) with
          [] -> failwith "merge_logic_substitution.add_cls.[]"
        | [_] -> failwith "merge_logic_substitution.add_cls.[_]"
        | w :: ws -> rev_itlist (add_wire w) ws sub in
    fun clses ->
    rev_itlist add_cls clses [];;

let merge_logic primary_inputs ckt =
    let (wire_inps,nxt_cls,wire_cls,clses) =
        merge_logic_initialize primary_inputs ckt in
    match merge_logic_refine_loop wire_inps nxt_cls wire_cls clses with
      [] -> ckt
    | clses -> INST (merge_logic_substitution clses) ckt;;

(* ------------------------------------------------------------------------- *)
(* Deleting dead logic.                                                      *)
(* ------------------------------------------------------------------------- *)

let delete_dead_logic primary_inputs primary_outputs th =
    let defs =
        let mk_def asm = (rand asm, (frees (rator asm), asm)) in
        map mk_def (hyp th) in
    let find_def wire =
        match filter (fun (w,_) -> w = wire) defs with
          [] -> failwith ("delete_dead_logic: no definition found for wire " ^ dest_wire_var wire)
        | [(_,ws_asm)] -> ws_asm
        | _ :: _ :: _ ->
          failwith ("delete_dead_logic: multiple definitions found for wire " ^ dest_wire_var wire) in
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

(* ------------------------------------------------------------------------- *)
(* Renaming wires to replace primed variables with numeric variants.         *)
(* ------------------------------------------------------------------------- *)

type deprime_name =
     Wire_deprime of term
   | Module_deprime of deprime

and deprime = Deprime of (string * (string * deprime_name) list) list;;

let empty_deprime = Deprime [];;

let add_deprime w =
    let rec add mp ms (Deprime l) =
        let m = deprime mp in
        let (ml,l) = partition (fun (x,_) -> x = m) l in
        let ml =
            match ml with
              [] -> []
            | [(_,x)] -> x
            | _ :: _ :: _ -> failwith "add_deprime: multiple ml" in
        let (mpl,ml) = partition (fun (x,_) -> x = mp) ml in
        let mpl = addn ms mpl in
        Deprime ((m, ((mp,mpl) :: ml)) :: l)
    and addn ms mpl =
        match ms with
          [] ->
          if length mpl = 0 then Wire_deprime w else
          failwith "add_deprime: wire slot already occupied"
        | mp :: ms ->
          let dp =
              match mpl with
                [] -> empty_deprime
              | [(_, Module_deprime dp)] -> dp
              | _ -> failwith "add_deprime: bad module slot" in
          Module_deprime (add mp ms dp) in
    let (s,_) = dest_var w in
    uncurry add (split '.' s);;

let wires_to_deprime ws = itlist add_deprime ws empty_deprime;;

let deprime_to_sub =
    let mpl_cmp (mp1,_) (mp2,_) = String.length mp1 < String.length mp2 in
    let narrow sc n = if String.length sc = 0 then n else sc ^ "." ^ n in
    fun frozen ->
    let rec go_dp sc sub (Deprime l) = go_ml sc sub l
    and go_ml sc sub ml =
        match ml with
          [] -> sub
        | (m,[(_,dpn)]) :: ml ->
          let sub = go_dpn (narrow sc m) sub dpn in
          go_ml sc sub ml
        | (m,mpl) :: ml ->
          let mpl = mergesort mpl_cmp mpl in
          let sub = go_mpl (narrow sc m) 0 sub mpl in
          go_ml sc sub ml
    and go_mpl sc n sub mpl =
        match mpl with
          [] -> sub
        | (_,dpn) :: mpl ->
          let sub = go_dpn (sc ^ string_of_int n) sub dpn in
          go_mpl sc (n + 1) sub mpl
    and go_dpn sc sub dpn =
        match dpn with
          Wire_deprime w ->
          if mem w frozen then sub else
          let w' = mk_var (sc,wire_ty) in
          if w' = w then sub else
          if mem w' frozen then failwith "deprime_to_sub: hitting frozen" else
          (w',w) :: sub
        | Module_deprime dp -> go_dp sc sub dp in
     go_dp "" [];;

let rename_wires primary th =
    let ws = freesl (hyp th) in
    let dp = wires_to_deprime ws in
    let sub = deprime_to_sub primary dp in
    INST sub th;;

(* ------------------------------------------------------------------------- *)
(* Synthesizing hardware.                                                    *)
(* ------------------------------------------------------------------------- *)

let partition_primary primary th =
    let outputs = map rand (hyp th) in
    partition (not o C mem outputs) primary;;

let synthesize_hardware syn primary th =
    let namer = new_namer primary in
    let (th,namer) =
        complain_timed "Elaborated modules"
          (elaborate_circuit syn th) namer in
    let (th,namer) =
        complain_timed "Simplified circuit"
          (simplify_circuit th) namer in
    let (primary_inputs,primary_outputs) =
        partition_primary primary th in
    let (th,namer) =
        complain_timed "Rescued primary outputs"
          (rescue_primary_outputs primary_outputs th) namer in
    let th =
        complain_timed "Merged identical logic"
          merge_logic primary_inputs th in
    let th =
        complain_timed "Deleted dead logic"
          (delete_dead_logic primary_inputs primary_outputs) th in
    let th =
        complain_timed "Renamed wires"
          (rename_wires primary) th in
    th;;

(*** Testing
synthesize_hardware counter_syn (frees (concl counter91_thm)) counter91_thm;;
synthesize_hardware montgomery_mult_syn (frees (concl montgomery91_thm)) montgomery91_thm;;
***)

(* ------------------------------------------------------------------------- *)
(* Duplicating delays to reduce fanout load.                                 *)
(*                                                                           *)
(* If a given delay (or primary input) has been duplicated d times and       *)
(* has n delays (or primary outputs), then we define the fanout load to      *)
(* be n / d.                                                                 *)
(*                                                                           *)
(* Suppose a given delay with parameters (d,n) is driven by a delay with     *)
(* parameters (fd,fn). Then duplicating the given delay fx more times        *)
(* would decrease its fanout load to n / (d + fx), but increase the fanout   *)
(* load of the driving delay to (fn + fx) / fd. We find the fx that          *)
(* balances these by solving                                                 *)
(*                                                                           *)
(*   (fn + fx) / fd = n / (d + fx)                                           *)
(*   <=>                                                                     *)
(*   fx^2 + (fn + d) * fx + (fn * d - fd * n) = 0                            *)
(*   <=>                                                                     *)
(*   fx = (-(fn + d) +/- sqrt{(fn + d)^2 - 4 * (fn * d - fd * n)}) / 2       *)
(*                                                                           *)
(* Note that we always choose + in the +/- above, because choosing - is      *)
(* guaranteed to result in a negative x. We are only interested in increases *)
(* to the duplication because our algorithm initializes all duplications to  *)
(* 1 and finds a fixed point by increasing duplication where it would reduce *)
(* overall fanout load.                                                      *)
(*                                                                           *)
(* In detail, the algorithm checks every delay in descending order of        *)
(* fanout load, and for a given delay finds the fx that would balance the    *)
(* fanout load with every driving delay. It then sets x to be the minimum    *)
(* of all the fx, rounded down to the nearest integer. If x is less than     *)
(* 1 then nothing changes, otherwise we increase the duplication of the      *)
(* delay (and increase the fn values for the driving delays by x). When      *)
(* there are no more fanout load reductions possible, the algorithm          *)
(* terminates.                                                               *)
(* ------------------------------------------------------------------------- *)

let duplicate_logic =
    let load d n = float n /. float d in
    let ann_load ((w : term), (d,n)) = (w, (d, n, load d n)) in
    let cmp_load
          ((_,(_,_,l1)) : term * (int * int * float))
          ((_,(_,_,l2)) : term * (int * int * float)) =
        l2 < l1 in
    let sort_load = mergesort cmp_load in
    let merge_load = merge cmp_load in
    let reduce_load w d n =
        let find_delta fd fn =
            let a = 1.0 in
            let b = float (fn + d) in
            let c = float (fn * d - fd * n) in
            let b2 = b *. b in
            let ac4 = 4.0 *. a *. c in
            if b2 < ac4 then failwith "negative discriminant" else
            let x = (sqrt (b2 -. ac4) -. b) /. (2.0 *. a) in
            if x < 0.0 then 0 else truncate x in
        let min_delta (_,(fd,fn,_)) x = min (find_delta fd fn) x in
        fun self -> fun fds ->
        let x =
            if self then find_delta d n else
            match fds with
              [] -> find_delta 1 d
            | (_,(fd,fn,_)) :: fds ->
              itlist min_delta fds (find_delta fd fn) in
        if x = 0 then None else
        let d = d + x in
        let n = if self then n + x else n in
        let fds = map (fun (f,(fd,fn,_)) -> (f, (fd, fn + x))) fds in
(* Debugging
        let () =
            let msg =
                "Raising duplication of wire " ^ string_of_term w ^
                " to " ^ string_of_int d ^ "\n" in
            print_string msg in
*)
        Some ((w,(d,n)) :: fds) in
    fun primary_inputs ->
    fun (fanin : (term * (term list * term list)) list) ->
    let rec balance seen wds =
        match wds with
          [] -> seen
        | wd :: wds ->
          let (w,(d,n,l)) = wd in
          let fs = if mem w primary_inputs then [] else fst (assoc w fanin) in
          let pred (f,_) = mem f fs in
          let (fds1,seen') = partition pred seen in
          let (fds2,wds') = partition pred wds in
          match reduce_load w d n (mem w fs) (fds1 @ fds2) with
            None -> balance (wd :: seen) wds
          | Some fds ->
            let fds = sort_load (map ann_load fds) in
            balance [] (merge_load fds (List.rev_append seen' wds')) in
    fun fanout ->
    let init (w, (ws : term list)) = ann_load (w, (1, length ws)) in
    balance [] (sort_load (map init fanout));;

(* Testing
let ckt = counter91_thm;;
let ckt = montgomery91_thm;;
let fanin = ckt_fanin ckt;;
let primary_inputs = ckt_primary_inputs ckt;;
let fanout = ckt_fanout ckt;;
duplicate_logic primary_inputs fanin fanout;;
*)

(* ------------------------------------------------------------------------- *)
(* Profiling synthesized hardware.                                           *)
(* ------------------------------------------------------------------------- *)

let pp_print_float fmt f = Format.fprintf fmt "%.1f" f;;

let pp_print_count fmt (title,i) =
    let () = Format.pp_open_box fmt 2 in
    let () = Format.pp_print_string fmt (title ^ ":") in
    let () = Format.pp_print_space fmt () in
    let () = Format.pp_print_int fmt i in
    let () = Format.pp_close_box fmt () in
    ();;

let pp_print_distribution print_x print_y fmt (title,xys) =
    let xys = mergesort (fun (_,y1) -> fun (_,y2) -> y1 < y2) xys in
    let print_iy s i =
        let (_,y) = List.nth xys i in
        let () = Format.pp_print_space fmt () in
        let () = Format.pp_print_string fmt s in
        let () = Format.pp_print_string fmt "=" in
        let () = print_y fmt y in
        () in
    let imax = length xys - 1 in
    let i99 = (imax * 99) / 100 in
    let i95 = (imax * 19) / 20 in
    let i90 = (imax * 9) / 10 in
    let i75 = (imax * 3) / 4 in
    let i50 = imax / 2 in
    let i25 = imax / 4 in
    let (xmax,_) = List.nth xys imax in
    let () = Format.pp_open_box fmt 2 in
    let () = Format.pp_print_string fmt (title ^ ":") in
    let () = print_iy "25%" i25 in
    let () = print_iy "50%" i50 in
    let () = print_iy "75%" i75 in
    let () = print_iy "90%" i90 in
    let () = print_iy "95%" i95 in
    let () = print_iy "99%" i99 in
    let () = print_iy "max" imax in
    let () = Format.pp_print_string fmt " (" in
    let () = print_x fmt xmax in
    let () = Format.pp_print_string fmt ")" in
    let () = Format.pp_close_box fmt () in
    ();;

let pp_print_hardware_profile fmt th =
    let logic = ckt_logic' th in
    let wires = ckt_wires' logic in
    let primary_inputs = ckt_primary_inputs' logic wires in
    let primary_outputs = ckt_primary_outputs' logic in
    let delays = ckt_delays' logic in
    let gates = ckt_gates' logic in
    let fanin = ckt_fanin' logic primary_inputs primary_outputs delays in
    let fanout = ckt_fanout' primary_inputs delays fanin in
    let fanout_load = duplicate_logic primary_inputs fanin fanout in
    let (fanin,fanin_cone) =
        let fc (w,(f,c)) = ((w, length f), (w, length c)) in
        unzip (map fc fanin) in
    let fanout = map (fun (w,f) -> (w, length f)) fanout in
    let duplication = map (fun (w,(d,_,_)) -> (w,d)) fanout_load in
    let fanout_load = map (fun (w,(_,_,l)) -> (w, truncate l)) fanout_load in
    let pp_print_wire_dist =
        pp_print_distribution pp_print_term Format.pp_print_int in
    let () = Format.pp_open_box fmt 0 in
    let () = pp_print_count fmt ("Primary inputs", length primary_inputs) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_count fmt ("Primary outputs", length primary_outputs) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_count fmt ("Delays", length delays) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_count fmt ("Gates", length gates) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_wire_dist fmt ("Fan-in",fanin) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_wire_dist fmt ("Fan-in cone",fanin_cone) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_wire_dist fmt ("Fan-out",fanout) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_wire_dist fmt ("Fan-out load",fanout_load) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_wire_dist fmt ("Duplication",duplication) in
    let () = Format.pp_close_box fmt () in
    ();;

let hardware_profile_to_string = print_to_string pp_print_hardware_profile;;

(*** Testing
print_string ("\n" ^ hardware_profile_to_string counter91_thm ^ "\n");;
print_string ("\n" ^ hardware_profile_to_string montgomery91_thm ^ "\n");;
***)

(* ------------------------------------------------------------------------- *)
(* Pretty-printing synthesized hardware in Verilog.                          *)
(* ------------------------------------------------------------------------- *)

let VERILOG_LINE_LENGTH = 79;;

type verilog_arg =
     Wire_verilog_arg of term
   | Bus_verilog_arg of bus_wires;;

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
        let space = max 1 (VERILOG_LINE_LENGTH - (String.length s + 3)) in
        "| " ^ s ^ String.make space ' ' ^ "|" in
    let bottom = "+" ^ String.make (VERILOG_LINE_LENGTH - 3) '-' ^ "*/" in
    fun text ->
        top ^ "\n" ^
        String.concat "\n" (map middle (split text)) ^ "\n" ^
        bottom ^ "\n";;

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

let verilog_wire_names =
    let verilog_name =
        let zap = "[]" in
        let spacer = "." in
        let tr c =
            if String.contains zap c then "" else
            if String.contains spacer c then "_" else
            String.make 1 c in
        translate tr in
    fun primary ->
    let verilog_wire w =
        if mem w primary then w else
        let s = dest_wire_var w in
        mk_wire_var (verilog_name s) in
    fun th ->
    let ws = freesl (hyp th) in
    let ws' = map verilog_wire ws in
    let () =
        if length (setify ws') = length ws' then () else
        let f w ws =
            let w' = verilog_wire w in
            match filter (fun (_,y) -> y = w') ws with
              [] -> (w,w') :: ws
            | (x,_) :: _ ->
              let msg =
                  "verilog_wire_names: different wire names:\n  " ^
                  dest_wire_var x ^ "\n  " ^ dest_wire_var w ^
                  "map to the same verilog wire name:\n  " ^
                  dest_wire_var w' in
              failwith msg in
        let _ = itlist f ws [] in
        failwith "verilog_wire_names: bug" in
    let sub = filter (fun (w',w) -> w' <> w) (zip ws' ws) in
    INST sub th;;

let hardware_to_verilog =
    let wire_name w =
        if is_ground w then "1'b0" else
        if is_power w then "1'b1" else
        dest_wire_var w in
    let wire_names = map wire_name in
    let wire_sort =
        let wire_cmp w1 w2 =
            String.compare (dest_wire_var w1) (dest_wire_var w2) < 0 in
        mergesort wire_cmp in
    let arg_name arg =
        match arg with
          Wire_verilog_arg w -> wire_name w
        | Bus_verilog_arg (Bus_wires (b,_)) -> b in
    let arg_names = map arg_name in
    let arg_decl arg =
        match arg with
          Wire_verilog_arg w -> wire_name w
        | Bus_verilog_arg (Bus_wires (b,is)) ->
          range_to_string (rev is) ^ " " ^ b in
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
    let verilog_profile th =
        let prof =
            let n = get_margin () in
            let () = set_margin (VERILOG_LINE_LENGTH - 4) in
            let s = hardware_profile_to_string th in
            let () = set_margin n in
            s in
        "\n" ^ comment_box_text prof in
    fun name -> fun primary -> fun th ->
    let th = verilog_wire_names primary th in
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
    verilog_module_end name ^
    verilog_profile th;;

(*** Testing
let name = "montgomery91";;
let primary = `clk : wire` :: frees (concl montgomery91_thm);;
output_string stdout (hardware_to_verilog name primary montgomery91_thm);;
***)

let hardware_to_verilog_file name wires th =
    let file = "opentheory/hardware/" ^ name ^ ".v" in
    let s = hardware_to_verilog name wires th in
    let h = open_out file in
    let () = output_string h s in
    let () = close_out h in
    file;;
