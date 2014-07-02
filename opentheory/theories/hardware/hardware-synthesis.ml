(* ========================================================================= *)
(* HARDWARE SYNTHESIS                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

#load "unix.cma";;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

module String_set = Set.Make(String);;

module String_map = Map.Make(String);;

let current_year () =
    let {Unix.tm_year = y} = Unix.localtime (Unix.time ()) in
    y + 1900;;

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

let find_min lt =
    let f x m = if lt x m then x else m in
    fun xs ->
    match xs with
      [] -> failwith "find_min: empty list"
    | x :: xs -> rev_itlist f xs x;;

let find_max lt =
    let gt x y = lt y x in
    find_min gt;;

let disjoint xs =
    let notmem x = not (mem x xs) in
    forall notmem;;

let is_true =
    let true_tm = `T` in
    fun tm -> tm = true_tm;;

let mk_one_var =
    let one_ty = `:1` in
    fun s -> mk_var (s,one_ty);;

let undisch_bind th =
    let (tm,_) = dest_imp (concl th) in
    (tm, UNDISCH th);;

(* ------------------------------------------------------------------------- *)
(* String operations.                                                        *)
(* ------------------------------------------------------------------------- *)

let is_digit = String.contains "0123456789";;

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

let pp_print_float fmt x = Format.fprintf fmt "%.0g" x;;

let prettify_int s =
    let n = String.length s in
    let rec f acc i =
        let j = i - 3 in
        if j < 0 then String.concat "," (String.sub s 0 (i + 1) :: acc) else
        f (String.sub s (j + 1) 3 :: acc) j in
    if n <= 3 then s else f [] (n - 1);;

let string_of_pretty_int i = prettify_int (string_of_int i);;

let string_of_pretty_num n = prettify_int (string_of_num n);;

let pp_print_pretty_int fmt i =
    Format.pp_print_string fmt (string_of_pretty_int i);;

let string_of_pretty_duration =
    let pr t u =
        let n = truncate t in
        string_of_int n ^ " " ^ u ^ (if n = 1 then "" else "s") in
    fun t ->
    if t < 1.0 then sprintf "%.0g" t ^ " seconds" else
    if t < 200.0 then pr t "second" else
    let t = t /. 60.0 in
    if t < 200.0 then pr t "minute" else
    let t = t /. 60.0 in
    if t < 100.0 then pr t "hour" else
    let t = t /. 24.0 in
    if t < 30.0 then pr t "day" else
    let t = t /. 7.0 in
    pr t "week";;

(* ------------------------------------------------------------------------- *)
(* Profiling functions.                                                      *)
(* ------------------------------------------------------------------------- *)

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
    let () = complain ("- " ^ s ^ ": " ^ string_of_pretty_int t ^ " second" ^ (if t = 1 then "" else "s") ^ " (" ^ string_of_pretty_int m0 ^ "-" ^ string_of_pretty_int mx ^ "Mb)") in
    fx;;

(* ------------------------------------------------------------------------- *)
(* A simple priority queue implementation derived from leftist heaps         *)
(* described in "Purely Functional Data Structures", Chris Okasaki.          *)
(* ------------------------------------------------------------------------- *)

type 'a priority_node =
     Empty_priority_node
   | Priority_node of int * 'a * 'a priority_node * 'a priority_node;;

type 'a priority_queue =
     Priority_queue of ('a -> 'a -> bool) * int * 'a priority_node;;

let rank_priority_node n =
    match n with
      Empty_priority_node -> 0
    | Priority_node (r,_,_,_) -> r;;

let mk_priority_node x a b =
    let ra = rank_priority_node a in
    let rb = rank_priority_node b in
    if rb <= ra then
      Priority_node (rb + 1, x, a, b)
    else
      Priority_node (ra + 1, x, b, a);;

let single_priority_node x =
    Priority_node (1,x,Empty_priority_node,Empty_priority_node);;

let merge_priority_node lt =
    let rec merge n1 n2 =
        match (n1,n2) with
          (Empty_priority_node,_) -> n2
        | (_,Empty_priority_node) -> n1
        | (Priority_node (r1,x1,a1,b1), Priority_node (r2,x2,a2,b2)) ->
          if lt x1 x2 then
            mk_priority_node x2 a2 (merge n1 b2)
          else
            mk_priority_node x1 a1 (merge b1 n2) in
    merge;;

let new_priority_queue lt = Priority_queue (lt,0,Empty_priority_node);;

let size_priority_queue (Priority_queue (_,sz,_)) = sz;;

let null_priority_queue pq = size_priority_queue pq = 0;;

let add_priority_queue x (Priority_queue (lt,sz,node)) =
    let node = merge_priority_node lt (single_priority_node x) node in
    Priority_queue (lt, sz + 1, node);;

let remove_priority_queue (Priority_queue (lt,sz,node)) =
    match node with
      Empty_priority_node -> failwith "remove_priority_queue: empty"
    | Priority_node (_,x,a,b) ->
      (x, Priority_queue (lt, sz - 1, merge_priority_node lt a b));;

(* ------------------------------------------------------------------------- *)
(* Substitution operations.                                                  *)
(* ------------------------------------------------------------------------- *)

let null_subst (sub : (term * term) list) =
    match sub with
      [] -> true
    | _ -> false;;

let norm_sub =
    let pred ((tm : term), v) = tm <> v in
    filter pred;;

let compose_subst old_sub new_sub =
    if null_subst new_sub then old_sub else
    let apply_new_sub (t,v) = (vsubst new_sub t, v) in
    map apply_new_sub old_sub @ new_sub;;

let string_of_subst =
    let maplet (t,v) =
        string_of_term v ^ " |-> " ^ string_of_term t ^ "\n" in
    fun sub ->
    "<sub> [" ^
    (if length sub = 0 then "" else
     ("\n  " ^ String.concat "\n  " (map maplet sub))) ^
    "]";;

(* ------------------------------------------------------------------------- *)
(* Extra conversions.                                                        *)
(* ------------------------------------------------------------------------- *)

let refl_conv tm =
    let (l,r) = dest_eq tm in
    if aconv l r then EQT_INTRO (ALPHA l r) else failwith "refl_conv";;

let simple_conv th =
    let redex = lhs (concl th) in
    fun tm -> if tm = redex then th else failwith "simple_conv";;

let orelse_sym_conv : conv -> conv =
    let rewr = REWR_CONV EQ_SYM_EQ in
    fun c -> c ORELSEC (rewr THENC c);;

(* ------------------------------------------------------------------------- *)
(* Caching frequently-called numeral conversions.                            *)
(* ------------------------------------------------------------------------- *)

let cache_numerals d =
    let int_of_term tm =
        try (Some (int_of_num (dest_numeral (d tm))))
        with Failure _ -> None in
    fun f ->
    let m = ref Int_map.empty in
    fun tm ->
    match int_of_term tm with
      None -> f tm
    | Some n ->
      if Int_map.mem n (!m) then Int_map.find n (!m) else
      let res = f tm in
      let () = m := Int_map.add n res (!m) in
      res;;

let suc_num_conv =
    let suc_tm = `SUC` in
    let dest_suc tm =
        let (tm,n) = dest_comb tm in
        if tm = suc_tm then n else failwith "suc_num_conv.dest_suc" in
    cache_numerals dest_suc NUM_SUC_CONV;;

let num_suc_conv =
    let suc_tm = `SUC` in
    let mk_suc tm = mk_comb (suc_tm,tm) in
    let f tm =
        let n = dest_numeral tm in
        if eq_num n num_0 then failwith "num_suc_conv" else
        let m = mk_suc (mk_numeral (n -/ num_1)) in
        SYM (suc_num_conv m) in
     cache_numerals I f;;

(* ------------------------------------------------------------------------- *)
(* A special exception for synthesis bugs.                                   *)
(* ------------------------------------------------------------------------- *)

exception Synthesis_bug of string;;

(* ------------------------------------------------------------------------- *)
(* Sort wires respecting numbers in their name.                              *)
(* ------------------------------------------------------------------------- *)

type chunk =
     Num_chunk of int
   | Other_chunk of string;;

let string_to_chunks s =
    let n = String.length s in
    let rec mk_chunk b i =
        let i = i + 1 in
        if i = n then i else
        let c = String.get s i in
        if is_digit c = b then mk_chunk b i else i in
    let rec chunk_from xs i =
        if i = n then rev xs else
        let c = String.get s i in
        let b = is_digit c in
        let j = mk_chunk b i in
        let x = String.sub s i (j - i) in
        let x = if b then Num_chunk (int_of_string x) else Other_chunk x in
        chunk_from (x :: xs) j in
    chunk_from [] 0;;

let lt_chunk c1 c2 =
    match (c1,c2) with
      (Num_chunk i1, Num_chunk i2) -> i1 < i2
    | (Num_chunk _, Other_chunk _) -> true
    | (Other_chunk _, Num_chunk _) -> false
    | (Other_chunk s1, Other_chunk s2) -> String.compare s1 s2 < 0;;

let rec lt_chunks cs1 cs2 =
    match cs2 with
      [] -> false
    | c2 :: cs2 ->
      match cs1 with
        [] -> true
      | c1 :: cs1 ->
        lt_chunk c1 c2 or (not (lt_chunk c2 c1) && lt_chunks cs1 cs2);;

let wire_sort =
    let mk w = (string_to_chunks (dest_wire_var w), w) in
    let cmp (c1,_) (c2,_) = lt_chunks c1 c2 in
    fun ws -> map snd (mergesort cmp (map mk ws));;

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
(* Efficiently store sets of wire variables.                                 *)
(* ------------------------------------------------------------------------- *)

type wireset = Wireset of String_set.t;;

let empty_wireset = Wireset String_set.empty;;

let size_wireset (Wireset s) = String_set.cardinal s;;

let null_wireset ws = size_wireset ws = 0;;

let mem_wireset w (Wireset s) = String_set.mem (dest_wire_var w) s;;

let add_wireset w ws =
    if mem_wireset w ws then ws else
    let Wireset s = ws in
    let s = String_set.add (dest_wire_var w) s in
    Wireset s;;

let remove_wireset w ws =
    if mem_wireset w ws then ws else
    let Wireset s = ws in
    let s = String_set.remove (dest_wire_var w) s in
    Wireset s;;

let union_wireset (Wireset s1) (Wireset s2) =
    Wireset (String_set.union s1 s2);;

let add_list_wireset = rev_itlist add_wireset;;

let from_list_wireset wl = add_list_wireset wl empty_wireset;;

let fold_wireset f (Wireset s) =
    let g s x = f (mk_wire_var s) x in
    String_set.fold g s;;

let to_list_wireset =
    let add w acc = w :: acc in
    fun ws -> fold_wireset add ws [];;

(* ------------------------------------------------------------------------- *)
(* Efficient finite maps from wire variables.                                *)
(* ------------------------------------------------------------------------- *)

type 'a wiremap = Wiremap of int * 'a String_map.t;;

let empty_wiremap = Wiremap (0,String_map.empty);;

let size_wiremap (Wiremap (sz,_)) = sz;;

let mem_wiremap w (Wiremap (_,m)) = String_map.mem (dest_wire_var w) m;;

let peek_wiremap w (Wiremap (_,m)) =
    let s = dest_wire_var w in
    if String_map.mem s m then Some (String_map.find s m) else None;;

let find_wiremap w wm =
    match peek_wiremap w wm with
      Some x -> x
    | None -> failwith "find_wiremap: not found";;

let add_wiremap w x (Wiremap (sz,m)) =
    let s = dest_wire_var w in
    let sz = if String_map.mem s m then sz else sz + 1 in
    let m = String_map.add s x m in
    Wiremap (sz,m);;

let fold_wiremap f (Wiremap (_,m)) =
    let g s x z = f (mk_wire_var s) x z in
    String_map.fold g m;;

let map_wiremap f (Wiremap (sz,m)) =
    let g s x = f (mk_wire_var s) x in
    Wiremap (sz, String_map.mapi g m);;

let to_list_wiremap =
    let add w x acc = (w,x) :: acc in
    fun wm ->
    rev (fold_wiremap add wm []);;

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
(* Synthesis rules allow backward reasoning on theorem assumptions.          *)
(* ------------------------------------------------------------------------- *)

type synthesis_result =
     Synthesis_result of term list * thm * (term * term) list * namer
   | Synthesis_accept
   | Synthesis_unchanged;;

type synthesis_rule = Synthesis_rule of (term -> namer -> synthesis_result);;

type synthesis_object =
     Goal_synthesis_object of term
   | Sub_synthesis_object of (term * term) list;;

let accept_synthesis_rule =
    Synthesis_rule (fun _ -> fun _ -> Synthesis_accept);;

let all_synthesis_rule =
    Synthesis_rule (fun _ -> fun _ -> Synthesis_unchanged);;

let no_synthesis_rule =
    Synthesis_rule (fun _ -> fun _ -> failwith "no_synthesis_rule");;

let apply_synthesis_rule (Synthesis_rule pr) goal namer =
    let subgoals_th_sub_namer = pr goal namer in
(* Debugging
    let (subgoals,th,sub,_) = subgoals_th_sub_namer in
    let () =
        let n = length subgoals in
        let msg = "apply_synthesis_rule: reducing goal\n" ^ string_of_term goal ^ "\nto " ^ string_of_int n ^ " subgoal" ^ (if n = 1 then "" else "s") ^ (if n = 0 then "" else ":\n" ^ String.concat "\n" (map string_of_term subgoals)) ^ "\nusing theorem:\n" ^ string_of_thm th ^ "\n" in
        print_string msg in
    let () =
        let goal' = vsubst sub goal in
        if aconv goal' (concl th) then () else
        let () = complain ("using substitution\n" ^ string_of_subst sub ^ "\nconclusion of\n" ^ string_of_thm th ^ "\ndoesn't match goal[substitution]\n" ^ string_of_term goal' ^ "\n") in
        raise (Synthesis_bug "apply_synthesis_rule: conclusion doesn't match goal[substitution]") in
    let () =
        let tms = hyp th in
        let check tm =
            if mem tm tms then () else
            let () = complain ("subgoal\n" ^ string_of_term tm ^ "\nnot a hypothesis in\n" ^ string_of_thm th ^ "\n") in
            raise (Synthesis_bug "apply_synthesis_rule: subgoal not a hypothesis") in
        List.iter check tms in
*)
    subgoals_th_sub_namer;;

let check_synthesis_rule f pr =
    Synthesis_rule
      (fun goal -> fun namer ->
       let () = f goal namer in
       apply_synthesis_rule pr goal namer);;

let cond_synthesis_rule f pr1 pr2 =
    Synthesis_rule
      (fun goal -> fun namer ->
       let pr = if f goal namer then pr1 else pr2 in
       apply_synthesis_rule pr goal namer);;

let subst_synthesis_rule f =
    Synthesis_rule
      (fun goal -> fun namer ->
       let sub = f goal namer in
       if null_subst sub then Synthesis_unchanged else
       let goal = vsubst sub goal in
       Synthesis_result ([goal], ASSUME goal, sub, namer));;

let orelse_synthesis_rule pr1 pr2 =
    Synthesis_rule
      (fun goal -> fun namer ->
       try (apply_synthesis_rule pr1 goal namer)
       with Failure _ -> apply_synthesis_rule pr2 goal namer);;

let try_synthesis_rule pr =
    orelse_synthesis_rule pr all_synthesis_rule;;

let first_synthesis_rule =
    let rec first prs =
        match prs with
          [] -> no_synthesis_rule
        | pr :: prs -> orelse_synthesis_rule pr (first prs) in
    first;;

let prove_hyp_synthesis_rule pr =
    let finalize_asm sub asm acc = vsubst sub asm :: acc in
    let rec finalize_asms acc sub asmsl =
        match asmsl with
          [] -> acc
        | (gsub,asms) :: asmsl ->
          let sub = compose_subst gsub sub in
          let acc = rev_itlist (finalize_asm sub) asms acc in
          finalize_asms acc sub asmsl in
    let rec synthesis_asms asms asmsl th sub namer goals =
        match goals with
          [] -> (finalize_asms (rev asms) [] asmsl, th, sub, namer)
        | goal :: goals ->
          let goal = vsubst sub goal in
          match apply_synthesis_rule pr goal namer with
            Synthesis_result (gasms,gth,gsub,gnamer) ->
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
            synthesis_asms asms asmsl th sub namer goals
          | Synthesis_accept ->
            synthesis_asms asms asmsl th sub namer goals
          | Synthesis_unchanged ->
            let asms = goal :: asms in
            synthesis_asms asms asmsl th sub namer goals in
    fun goals -> fun th -> fun namer ->
    synthesis_asms [] [] th [] namer goals;;

let then_synthesis_rule pr1 pr2 =
    Synthesis_rule
      (fun goal -> fun namer0 ->
       match apply_synthesis_rule pr1 goal namer0 with
         Synthesis_result (asms,th,sub1,namer) ->
         let (asms,th,sub2,namer) =
             prove_hyp_synthesis_rule pr2 asms th namer in
         let sub = compose_subst sub1 sub2 in
         let namer = widen_scope (current_scope namer0) namer in
         Synthesis_result (asms,th,sub,namer)
       | Synthesis_accept -> Synthesis_accept
       | Synthesis_unchanged -> apply_synthesis_rule pr2 goal namer0);;

let rec every_synthesis_rule prl =
    match prl with
      [] -> all_synthesis_rule
    | [pr] -> pr
    | pr :: prl -> then_synthesis_rule pr (every_synthesis_rule prl);;

let rec fold_synthesis_rule pr =
    Synthesis_rule
      (fun goal -> fun namer ->
       let rule =
           try_synthesis_rule
             (then_synthesis_rule pr (fold_synthesis_rule pr)) in
       apply_synthesis_rule rule goal namer);;

let repeat_prove_hyp_synthesis_rule pr =
    let rollback_asm gsub asm goals =
        Goal_synthesis_object (vsubst gsub asm) :: goals in
    let rec rollback_asms gsub gsubdom asms fvs asmsl goals =
        let goals = rev_itlist (rollback_asm gsub) asms goals in
        if disjoint fvs gsubdom then (fvs,asmsl,goals) else
        match asmsl with
          [] ->
          raise (Synthesis_bug "repeat_prove_hyp_synthesis_rule.rollback_asms")
        | (asms,fvs) :: asmsl ->
          rollback_asms gsub gsubdom asms fvs asmsl goals in
    let rec finalize_asms acc asmsl =
        match asmsl with
          [] -> acc
        | (asms,_) :: asmsl ->
          let acc = List.rev_append asms acc in
          finalize_asms acc asmsl in
    let rec synthesis_asms asms fvs asmsl th sub namer goals =
        match goals with
          [] -> (finalize_asms (rev asms) asmsl, th, sub, namer)
        | Sub_synthesis_object oldsub :: goals ->
          let sub = compose_subst oldsub sub in
          synthesis_asms asms fvs asmsl th sub namer goals
        | Goal_synthesis_object goal :: goals ->
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
          match apply_synthesis_rule pr goal namer with
            Synthesis_result (gasms,gth,gsub,gnamer) ->
            let namer = widen_scope (current_scope namer) gnamer in
            if null_subst gsub then
              let th = PROVE_HYP gth th in
              let asms = List.rev_append gasms asms in
              synthesis_asms asms fvs asmsl th sub namer goals
            else
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
                synthesis_asms (rev gasms) fvs' asmsl th sub namer goals
              else
                let goals =
                    map (fun gasm -> Goal_synthesis_object gasm) gasms @
                    Sub_synthesis_object sub ::
                    goals in
                let (fvs,asmsl,goals') =
                    rollback_asms gsub gsubdom asms fvs asmsl goals in
(* Debugging
                let () =
                    let n = length goals' - length goals in
                    let msg = "rolling back " ^ string_of_int n ^ " goal" ^ (if n = 1 then "" else "s") ^ " in scope " ^ scope_to_string (current_scope namer) in
                    complain msg in
*)
                synthesis_asms [] fvs asmsl th [] namer goals'
          | Synthesis_accept ->
            synthesis_asms asms fvs asmsl th sub namer goals
          | Synthesis_unchanged ->
            let asms = goal :: asms in
            synthesis_asms asms fvs asmsl th sub namer goals in
    fun asms -> fun th -> fun namer ->
    let goals = map (fun asm -> Goal_synthesis_object asm) asms in
    synthesis_asms [] [] [] th [] namer goals;;

let then_repeat_synthesis_rule pr1 pr2 =
    Synthesis_rule
      (fun goal -> fun namer0 ->
       match apply_synthesis_rule pr1 goal namer0 with
         Synthesis_result (asms,th,sub1,namer) ->
         let (asms,th,sub2,namer) =
             repeat_prove_hyp_synthesis_rule pr2 asms th namer in
         let sub = compose_subst sub1 sub2 in
         let namer = widen_scope (current_scope namer0) namer in
         Synthesis_result (asms,th,sub,namer)
       | Synthesis_accept -> Synthesis_accept
       | Synthesis_unchanged -> apply_synthesis_rule pr2 goal namer0);;

let rec repeat_synthesis_rule pr =
    Synthesis_rule
      (fun goal -> fun namer ->
       let rule =
           try_synthesis_rule
             (then_repeat_synthesis_rule pr (repeat_synthesis_rule pr)) in
       apply_synthesis_rule rule goal namer);;

let scope_thm_synthesis_rule =
    let mk_synthesis_thm =
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
    let synthesis_thm_rule s (vs,asms,th) =
        let pat = concl th in
        Synthesis_rule
          (fun tm -> fun namer ->
           let (_,sub,_) = term_match [] pat tm in
           let namer = narrow_scope s namer in
           let (vs_sub,namer) = freshen_vars vs namer in
           let sub = vs_sub @ sub in
           let asms = map (vsubst sub) asms in
           let th = INST sub th in
           Synthesis_result (asms,th,[],namer)) in
    fun s -> fun th ->
    synthesis_thm_rule s (mk_synthesis_thm th);;

let thm_synthesis_rule = scope_thm_synthesis_rule "";;

let conv_synthesis_rule (conv : conv) =
    Synthesis_rule
      (fun tm -> fun namer ->
       let eq_th = conv tm in
       let tm' = rhs (concl eq_th) in
       if is_true tm' then
         let th = EQT_ELIM eq_th in
         Synthesis_result ([],th,[],namer)
       else if tm' = tm then
         Synthesis_unchanged
       else
         let th = EQ_MP (SYM eq_th) (ASSUME tm') in
         Synthesis_result ([tm'],th,[],namer));;

let sym_synthesis_rule : synthesis_rule =
    Synthesis_rule
      (fun tm -> fun namer ->
       let (l,r) = dest_eq tm in
       let stm = mk_eq (r,l) in
       Synthesis_result ([stm], SYM (ASSUME stm), [], namer));;

let orelse_sym_synthesis_rule pr =
    orelse_synthesis_rule pr (then_synthesis_rule sym_synthesis_rule pr);;

let subst_var_synthesis_rule =
    orelse_sym_synthesis_rule
      (Synthesis_rule
         (fun tm -> fun namer ->
          let (l,r) = dest_eq tm in
          if is_unfrozen_var namer l then
            Synthesis_result ([], REFL r, [(r,l)], namer)
          else failwith "subst_var_synthesis_rule"));;

(* ------------------------------------------------------------------------- *)
(* A type of synthesized circuit.                                            *)
(* ------------------------------------------------------------------------- *)

type circuit = Circuit of thm;;

let spec_circuit (Circuit th) = concl th;;

let frees_circuit ckt = frees (spec_circuit ckt);;

let pp_print_circuit =
    let count x n = if is_delay x then n + 1 else n in
    let count_delays gates = rev_itlist count gates 0 in
    fun fmt -> fun (Circuit th) ->
    let (gates,spec) = dest_thm th in
    let n = count_delays gates in
    let kind =
        if n = 0 then "combinational circuit" else
        "circuit with " ^ string_of_pretty_int n ^ " register" ^
        (if n = 1 then "" else "s") in
    let () = pp_open_box fmt 0 in
    let () = pp_print_string fmt ("[" ^ kind ^ "]") in
    let () = pp_print_space fmt () in
    let () = pp_open_hbox fmt() in
    let () = pp_print_string fmt "|- " in
    let () = pp_print_term fmt spec in
    let () = pp_close_box fmt () in
    let () = pp_close_box fmt () in
    ();;

let print_circuit = pp_print_circuit std_formatter;;

#install_printer print_circuit;;

(* ------------------------------------------------------------------------- *)
(* Extracting information from a synthesized circuit.                        *)
(* ------------------------------------------------------------------------- *)

type circuit_logic = Circuit_logic of term list;;

type circuit_wires = Circuit_wires of wireset;;

type circuit_defs = Circuit_defs of term wiremap;;

type circuit_primary_inputs = Circuit_primary_inputs of wireset;;

type circuit_primary_outputs = Circuit_primary_outputs of wireset;;

type circuit_registers = Circuit_registers of wireset;;

type circuit_gates = Circuit_gates of term list;;

type circuit_fanins = Circuit_fanins of (wireset * wireset) wiremap;;

type circuit_fanouts = Circuit_fanouts of wireset wiremap;;

let circuit_logic (Circuit th) = Circuit_logic (hyp th);;

let circuit_defs (Circuit_logic logic) =
    let add gate defs =
        let wire = rand gate in
        if not (mem_wiremap wire defs) then add_wiremap wire gate defs else
        failwith ("multiple definitions of wire " ^ dest_wire_var wire) in
    Circuit_defs (rev_itlist add logic empty_wiremap);;

let circuit_def (Circuit_defs defs) wire =
    match peek_wiremap wire defs with
      Some gate -> gate
    | None -> failwith ("no definition found for wire " ^ dest_wire_var wire);;

let circuit_wires (Circuit_logic logic) =
    let add gate ws = add_list_wireset (frees gate) ws in
    Circuit_wires (rev_itlist add logic empty_wireset);;

let circuit_primary_inputs (Circuit_defs defs) (Circuit_wires wires) =
    let add wire acc =
        if mem_wiremap wire defs then acc else
        add_wireset wire acc in
    Circuit_primary_inputs (fold_wireset add wires empty_wireset);;

let circuit_primary_outputs (Circuit_logic logic) =
    let add gate acc =
        if not (is_connect gate) then acc else
        add_wireset (rand gate) acc in
    Circuit_primary_outputs (rev_itlist add logic empty_wireset);;

let circuit_registers (Circuit_logic logic) =
    let add gate acc =
        if not (is_delay gate) then acc else
        add_wireset (rand gate) acc in
    Circuit_registers (rev_itlist add logic empty_wireset);;

let circuit_gates (Circuit_logic logic) =
    let pred gate = not (is_delay gate) && not (is_connect gate) in
    Circuit_gates (filter pred logic);;

let wire_fanin defs (Circuit_primary_inputs primary_inputs) wire =
    let fanin1 gate = frees (rator gate) in
    let rec f fringe cone ws =
        match ws with
          [] -> (fringe,cone)
        | w :: ws ->
          if mem_wireset w fringe then f fringe cone ws else
          if mem_wireset w cone then f fringe cone ws else
          if mem_wireset w primary_inputs then
            f (add_wireset w fringe) cone ws else
          let g = circuit_def defs w in
          if is_delay g then f (add_wireset w fringe) cone ws else
          f fringe (add_wireset w cone) (fanin1 g @ ws) in
    let fringe = empty_wireset in
    let cone = empty_wireset in
    let ws = fanin1 (circuit_def defs wire) in
    f fringe cone ws;;

let circuit_fanins defs primary_inputs
      (Circuit_primary_outputs primary_outputs) (Circuit_registers registers) =
    let add wire wm =
        let fanin = wire_fanin defs primary_inputs wire in
        add_wiremap wire fanin wm in
    let wm = empty_wiremap in
    let wm = fold_wireset add primary_outputs wm in
    let wm = fold_wireset add registers wm in
    Circuit_fanins wm;;

let circuit_fanin (Circuit_fanins fanins) wire =
    match peek_wiremap wire fanins with
      Some fringe_cone -> fringe_cone
    | None -> failwith ("no fan-in found for wire " ^ dest_wire_var wire);;

let circuit_fanouts (Circuit_fanins fanins)
      (Circuit_primary_inputs primary_inputs) (Circuit_registers registers) =
    let init w wm = add_wiremap w empty_wireset wm in
    let add wire (fringe,_) =
        let add1 w wm =
            let ws = find_wiremap w wm in
            add_wiremap w (add_wireset wire ws) wm in
        fold_wireset add1 fringe in
    let wm = empty_wiremap in
    let wm = fold_wireset init primary_inputs wm in
    let wm = fold_wireset init registers wm in
    Circuit_fanouts (fold_wiremap add fanins wm);;

let circuit_fanout (Circuit_fanouts fanouts) wire =
    match peek_wiremap wire fanouts with
      Some fringe -> fringe
    | None -> failwith ("no fan-out found for wire " ^ dest_wire_var wire);;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Debug functions to compute these quantities *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let debug_circuit_logic = circuit_logic;;

let debug_circuit_defs ckt =
    let logic = circuit_logic ckt in
    circuit_defs logic;;

let debug_circuit_wires ckt =
    let logic = circuit_logic ckt in
    circuit_wires logic;;

let debug_circuit_primary_inputs ckt =
    let logic = circuit_logic ckt in
    let defs = circuit_defs logic in
    let wires = circuit_wires logic in
    circuit_primary_inputs defs wires;;

let debug_circuit_primary_outputs ckt =
    let logic = circuit_logic ckt in
    circuit_primary_outputs logic;;

let debug_circuit_registers ckt =
    let logic = circuit_logic ckt in
    circuit_registers logic;;

let debug_circuit_gates ckt =
    let logic = circuit_logic ckt in
    circuit_gates logic;;

let debug_wire_fanin ckt =
    let logic = circuit_logic ckt in
    let defs = circuit_defs logic in
    let wires = circuit_wires logic in
    let primary_inputs = circuit_primary_inputs defs wires in
    wire_fanin defs primary_inputs;;

let debug_circuit_fanins ckt =
    let logic = circuit_logic ckt in
    let defs = circuit_defs logic in
    let wires = circuit_wires logic in
    let primary_inputs = circuit_primary_inputs defs wires in
    let primary_outputs = circuit_primary_outputs logic in
    let registers = circuit_registers logic in
    circuit_fanins defs primary_inputs primary_outputs registers;;

let debug_circuit_fanouts ckt =
    let logic = circuit_logic ckt in
    let defs = circuit_defs logic in
    let wires = circuit_wires logic in
    let primary_inputs = circuit_primary_inputs defs wires in
    let primary_outputs = circuit_primary_outputs logic in
    let registers = circuit_registers logic in
    let fanins = circuit_fanins defs primary_inputs primary_outputs registers in
    circuit_fanouts fanins primary_inputs registers;;

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

let synthesizable_synthesis_rule =
    Synthesis_rule
      (fun tm -> fun namer ->
       if is_synthesizable tm then Synthesis_accept else
       failwith "synthesizable_synthesis_rule");;

let bground_conv =
    let zero_conv = REWR_CONV bground_zero in
    let suc_conv = REWR_CONV bground_suc in
    let rec reduce_conv tm =
        (zero_conv ORELSEC
         (RAND_CONV num_suc_conv THENC
          suc_conv THENC
          RAND_CONV reduce_conv)) tm in
    RAND_CONV NUM_REDUCE_CONV THENC
    reduce_conv;;

let bpower_conv =
    let zero_conv = REWR_CONV bpower_zero in
    let suc_conv = REWR_CONV bpower_suc in
    let rec reduce_conv tm =
        (zero_conv ORELSEC
         (RAND_CONV num_suc_conv THENC
          suc_conv THENC
          RAND_CONV reduce_conv)) tm in
    RAND_CONV NUM_REDUCE_CONV THENC
    reduce_conv;;

let bus_reduce_conv tm =
    if is_bground tm then bground_conv tm else
    if is_bpower tm then bpower_conv tm else
    ALL_CONV tm;;

let width_conv =
    let nil_conv = REWR_CONV bnil_width in
    let cons_conv = REWR_CONV bappend_bwire_width in
    let rec reduce_conv tm =
        (nil_conv ORELSEC
         (cons_conv THENC
          RAND_CONV reduce_conv THENC
          suc_num_conv)) tm in
    RAND_CONV bus_reduce_conv THENC
    reduce_conv;;

let num_simp_conv =
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
    REWRITE_CONV [ZERO_ADD; ADD_0; GSYM ADD_ASSOC] THENC
    push_numeral_conv THENC
    NUM_REDUCE_CONV;;

let num_eq_conv =
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
    TRY_CONV
      (FIRST_CONV
         [refl_conv;
          numeral_eq_add_numeral_conv]);;

let expand_bus_synthesis_rule =
    subst_synthesis_rule
      (fun tm -> fun namer ->
       let (t,n) = dest_eq tm in
       let n = dest_numeral n in
       let v = dest_width t in
       if not_unfrozen_var namer v then
         failwith "expand_bus_synthesis_rule"
       else
         let b = variable_bus (fst (dest_var v)) n in
         [(b,v)]);;

let width_synthesis_rule =
    let is_var goal namer =
        let (t,_) = dest_eq goal in
        let v = dest_width t in
        is_unfrozen_var namer v in
    let var_rule =
        let conv = RAND_CONV num_simp_conv in
        then_synthesis_rule
          (conv_synthesis_rule conv)
          expand_bus_synthesis_rule in
    let nonvar_rule =
        let conv =
            LAND_CONV width_conv THENC
            RAND_CONV num_simp_conv THENC
            num_eq_conv in
        then_synthesis_rule
          (conv_synthesis_rule conv)
          subst_var_synthesis_rule in
    cond_synthesis_rule is_var var_rule nonvar_rule;;

let wire_synthesis_rule =
    let is_wire_goal goal namer =
        let (_,_,w) = dest_wire goal in
        if is_unfrozen_var namer w then () else
        failwith "wire_synthesis_rule.is_wire_goal" in
    let zero_rule =
        then_synthesis_rule
          (thm_synthesis_rule wire_zero)
          subst_var_synthesis_rule in
    let suc_conv =
        LAND_CONV num_suc_conv THENC
        REWR_CONV wire_suc in
    let conv =
        RATOR_CONV
          (LAND_CONV bus_reduce_conv THENC
           RAND_CONV NUM_REDUCE_CONV) THENC
        REPEATC suc_conv in
    check_synthesis_rule
      is_wire_goal
      (then_synthesis_rule
         (conv_synthesis_rule conv)
         zero_rule);;

let bsub_synthesis_rule =
    let is_bsub_goal goal namer =
        let (_,_,_,y) = dest_bsub goal in
        if is_unfrozen_var namer y then () else
        failwith "bsub_synthesis_rule.is_bsub_goal" in
    let drop_conv =
        let suc_thm = prove
            (`!w x k n y.
                bsub (bappend (bwire w) x) (SUC k) n y <=>
                bsub x k n y`,
             REPEAT GEN_TAC THEN
             SUBGOAL_THEN `SUC k = width (bwire w) + k` SUBST1_TAC THENL
             [REWRITE_TAC [bwire_width; ONE; SUC_ADD; ZERO_ADD];
              REWRITE_TAC [bsub_in_suffix]]) in
        let suc_conv =
            RATOR_CONV (LAND_CONV num_suc_conv) THENC
            REWR_CONV suc_thm in
        RATOR_CONV
          (RATOR_CONV
             (LAND_CONV bus_reduce_conv THENC
              RAND_CONV NUM_REDUCE_CONV) THENC
           RAND_CONV NUM_REDUCE_CONV) THENC
        REPEATC suc_conv in
    let take_rule =
        let rec take_bus xs n =
            if eq_num n num_0 then mk_bnil else
            let (x,xs) = dest_bappend xs in
            let n = sub_num n num_1 in
            let xs = take_bus xs n in
            mk_bappend x xs in
        let subst_rule =
            subst_synthesis_rule
              (fun goal -> fun namer ->
               let (x,_,n,y) = dest_bsub goal in
               let n = dest_numeral n in
               let b = take_bus x n in
               [(b,y)]) in
        let zero_thm = prove
            (`!x. bsub x 0 0 bnil`,
             REWRITE_TAC [bsub_zero; LE_0]) in
        let suc_conv =
            LAND_CONV num_suc_conv THENC
            REWR_CONV bsub_bappend_bwire_cancel in
        then_synthesis_rule
          subst_rule
          (then_synthesis_rule
             (conv_synthesis_rule (REPEATC suc_conv))
             (thm_synthesis_rule zero_thm)) in
    check_synthesis_rule
      is_bsub_goal
      (then_synthesis_rule
         (conv_synthesis_rule drop_conv)
         take_rule);;

let brev_synthesis_rule =
    let is_brev_goal goal namer =
        let (_,y) = dest_brev goal in
        if is_unfrozen_var namer y then () else
        failwith "brev_synthesis_rule.is_brev_goal" in
    let init_conv = LAND_CONV bus_reduce_conv in
    let subst_rule =
        let rec rev_bus acc xs =
            if is_bnil xs then acc else
            let (x,xs) = dest_bappend xs in
            let acc = mk_bappend x acc in
            rev_bus acc xs in
        subst_synthesis_rule
          (fun goal -> fun namer ->
           let (x,y) = dest_brev goal in
           let b = rev_bus mk_bnil x in
           [(b,y)]) in
    let reduce_conv =
        RAND_CONV
          (REWR_CONV (GSYM bnil_bappend) THENC
           REWRITE_CONV [GSYM bappend_assoc; bappend_bnil]) THENC
        REPEATC (REWR_CONV brev_bappend_bwire) THENC
        REWR_CONV (EQT_INTRO brev_bnil) in
    check_synthesis_rule
      is_brev_goal
      (every_synthesis_rule
         [conv_synthesis_rule init_conv;
          subst_rule;
          conv_synthesis_rule reduce_conv]);;

let bconnect_synthesis_rule =
    let is_bconnect_goal goal _ =
        if is_bconnect goal then () else
        failwith "bconnect_synthesis_rule.is_bconnect_goal" in
    let init_conv =
        LAND_CONV bus_reduce_conv in
    let reduce_rule =
        fold_synthesis_rule
          (orelse_synthesis_rule
             (thm_synthesis_rule bconnect_bappend_bwire)
             (thm_synthesis_rule bconnect_bnil)) in
    check_synthesis_rule
      is_bconnect_goal
      (every_synthesis_rule
         [conv_synthesis_rule init_conv;
          reduce_rule]);;

let bdelay_synthesis_rule =
    let is_bdelay_goal goal _ =
        if is_bdelay goal then () else
        failwith "bdelay_synthesis_rule.is_bdelay_goal" in
    let init_conv =
        LAND_CONV bus_reduce_conv in
    let reduce_rule =
        fold_synthesis_rule
          (orelse_synthesis_rule
             (thm_synthesis_rule bdelay_bappend_bwire)
             (thm_synthesis_rule bdelay_bnil)) in
    check_synthesis_rule
      is_bdelay_goal
      (every_synthesis_rule
         [conv_synthesis_rule init_conv;
          reduce_rule]);;

let bnot_synthesis_rule =
    let is_bnot_goal goal _ =
        if is_bnot goal then () else
        failwith "bnot_synthesis_rule.is_bnot_goal" in
    let init_conv =
        LAND_CONV bus_reduce_conv in
    let reduce_rule =
        fold_synthesis_rule
          (orelse_synthesis_rule
             (thm_synthesis_rule bnot_bappend_bwire)
             (thm_synthesis_rule bnot_bnil)) in
    check_synthesis_rule
      is_bnot_goal
      (every_synthesis_rule
         [conv_synthesis_rule init_conv;
          reduce_rule]);;

let band2_synthesis_rule =
    let is_band2_goal goal _ =
        if is_band2 goal then () else
        failwith "band2_synthesis_rule.is_band2_goal" in
    let init_conv =
        RATOR_CONV
          (LAND_CONV bus_reduce_conv THENC
           RAND_CONV bus_reduce_conv) in
    let reduce_rule =
        fold_synthesis_rule
          (orelse_synthesis_rule
             (thm_synthesis_rule band2_bappend_bwire)
             (thm_synthesis_rule band2_bnil)) in
    check_synthesis_rule
      is_band2_goal
      (every_synthesis_rule
         [conv_synthesis_rule init_conv;
          reduce_rule]);;

let bor2_synthesis_rule =
    let is_bor2_goal goal _ =
        if is_bor2 goal then () else
        failwith "bor2_synthesis_rule.is_bor2_goal" in
    let init_conv =
        RATOR_CONV
          (LAND_CONV bus_reduce_conv THENC
           RAND_CONV bus_reduce_conv) in
    let reduce_rule =
        fold_synthesis_rule
          (orelse_synthesis_rule
             (thm_synthesis_rule bor2_bappend_bwire)
             (thm_synthesis_rule bor2_bnil)) in
    check_synthesis_rule
      is_bor2_goal
      (every_synthesis_rule
         [conv_synthesis_rule init_conv;
          reduce_rule]);;

let bxor2_synthesis_rule =
    let is_bxor2_goal goal _ =
        if is_bxor2 goal then () else
        failwith "bxor2_synthesis_rule.is_bxor2_goal" in
    let init_conv =
        RATOR_CONV
          (LAND_CONV bus_reduce_conv THENC
           RAND_CONV bus_reduce_conv) in
    let reduce_rule =
        fold_synthesis_rule
          (orelse_synthesis_rule
             (thm_synthesis_rule bxor2_bappend_bwire)
             (thm_synthesis_rule bxor2_bnil)) in
    check_synthesis_rule
      is_bxor2_goal
      (every_synthesis_rule
         [conv_synthesis_rule init_conv;
          reduce_rule]);;

let bcase1_synthesis_rule =
    let is_bcase1_goal goal _ =
        if is_bcase1 goal then () else
        failwith "bcase1_synthesis_rule.is_bcase1_goal" in
    let init_conv =
        RATOR_CONV
          (RATOR_CONV
             (LAND_CONV bus_reduce_conv THENC
              RAND_CONV bus_reduce_conv) THENC
           RAND_CONV bus_reduce_conv) in
    let reduce_rule =
        fold_synthesis_rule
          (orelse_synthesis_rule
             (thm_synthesis_rule bcase1_bappend_bwire)
             (thm_synthesis_rule bcase1_bnil)) in
    check_synthesis_rule
      is_bcase1_goal
      (every_synthesis_rule
         [conv_synthesis_rule init_conv;
          reduce_rule]);;

let elaboration_rule =
    let rules =
        [synthesizable_synthesis_rule;
         width_synthesis_rule;
         wire_synthesis_rule;
         bsub_synthesis_rule;
         brev_synthesis_rule;
         bconnect_synthesis_rule;
         bdelay_synthesis_rule;
         bnot_synthesis_rule;
         band2_synthesis_rule;
         bor2_synthesis_rule;
         bxor2_synthesis_rule;
         bcase1_synthesis_rule] in
    fun syn ->
    let user_rules = map (uncurry scope_thm_synthesis_rule) syn in
    fold_synthesis_rule (first_synthesis_rule (rules @ user_rules));;

let elaborate_circuit =
    let check_elaboration bad =
        let n = length bad in
        if n = 0 then () else
        let s = "term" ^ (if n = 1 then "" else "s") in
        let () = complain ("\n" ^ string_of_int n ^ " unsynthesizable " ^ s ^ ":") in
        let () = List.iter (complain o string_of_term) bad in
        failwith ("couldn't reduce " ^ string_of_int n ^ " " ^ s) in
    fun syn ->
    let rule = elaboration_rule syn in
    fun th -> fun namer ->
    let (tms,th,_,namer) = prove_hyp_synthesis_rule rule (hyp th) th namer in
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
     if null_subst sub then None else
     Some (INST sub th);;

let simplify_synthesis_rule =
    let rules =
        map thm_synthesis_rule
        [connect_refl;
         delay_ground; delay_power;
         not_ground; not_power;
         and2_refl;
         and2_left_ground; and2_right_ground;
         and2_left_power; and2_right_power;
         or2_refl;
         or2_left_ground; or2_right_ground;
         or2_left_power; or2_right_power;
         xor2_refl;
         xor2_left_ground; xor2_right_ground;
         xor2_left_power; xor2_right_power;
         case1_refl;
         case1_left_ground; case1_left_power;
         case1_middle_ground_right_power;
         case1_middle_power_right_ground;
         case1_middle_power;
         case1_right_ground;
         (* The following simplification rules introduce new internal wires, *)
         (* so we put them last in the list *)
         case1_middle_ground;
         case1_right_power] in
    first_synthesis_rule rules;;

let simplify_circuit =
    let rec simplify th namer =
        let (_,th,_,namer) =
            let rule = try_synthesis_rule simplify_synthesis_rule in
            complain_timed "- Simplified gates"
              (prove_hyp_synthesis_rule rule (hyp th) th) namer in
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

let connect_wire_synthesis_rule =
    Synthesis_rule
      (fun tm -> fun namer ->
       let (x,y) = dest_connect tm in
       if is_unfrozen_var namer y then
         Synthesis_result ([], SPEC x connect_refl, [(x,y)], namer)
       else failwith "connect_wire_synthesis_rule");;

let wire_connect_synthesis_rule =
    Synthesis_rule
      (fun tm -> fun namer ->
       let (x,y) = dest_connect tm in
       if is_unfrozen_var namer x then
         Synthesis_result ([], SPEC y connect_refl, [(y,x)], namer)
       else failwith "wire_connect_synthesis_rule");;

let connect_synthesis_rule =
    Synthesis_rule
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
           else failwith "connect_synthesis_rule" in
       Synthesis_result ([], SPEC w2 connect_refl, [(w2,w1)], namer));;

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

let rescue_primary_outputs_synthesis_rule primary_outputs namer =
    let (conv,namer) = rescue_primary_outputs_conv primary_outputs namer in
    (conv_synthesis_rule conv, namer);;

let rescue_primary_outputs =
    let cleanup_rule = try_synthesis_rule connect_wire_synthesis_rule in
    fun primary_outputs -> fun th -> fun namer ->
    let (rescue_rule,namer) =
        rescue_primary_outputs_synthesis_rule primary_outputs namer in
    let (_,th,_,namer) =
        complain_timed "- Interposed wires before primary outputs"
          (prove_hyp_synthesis_rule rescue_rule (hyp th) th) namer in
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
          (repeat_prove_hyp_synthesis_rule cleanup_rule asms th) namer in
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
          (merge_logic primary_inputs) th in
    let th =
        complain_timed "Deleted dead logic"
          (delete_dead_logic primary_inputs primary_outputs) th in
    let th =
        complain_timed "Renamed wires"
          (rename_wires primary) th in
    Circuit th;;

(* ------------------------------------------------------------------------- *)
(* Duplicating registers to reduce fanout load.                              *)
(*                                                                           *)
(* If a given register has been duplicated d times and drives n registers    *)
(* (or primary outputs), then we define the fanout load to be n / d.         *)
(*                                                                           *)
(* Suppose a given register with parameters (d,n) is driven by a register    *)
(* (or primary input) with parameters (d_i,n_i). Then duplicating the given  *)
(* register x_i more times would decrease its fanout load to n / (d + x_i),  *)
(* but increase the fanout load of the driving register (or primary input)   *)
(* to (n_i + x_i) / d_i. We find the x_i that balances these by solving      *)
(*                                                                           *)
(*   (n_i + x_i) / d_i = n / (d + x_i)                                       *)
(*   <=>                                                                     *)
(*   x_i^2 + (n_i + d) * x_i + (n_i * d - d_i * n) = 0                       *)
(*   <=>                                                                     *)
(*   x_i = (-(n_i + d) +/- sqrt{(n_i + d)^2 - 4 * (n_i * d - d_i * n)}) / 2  *)
(*                                                                           *)
(* Note that we always choose + in the +/- above, because choosing - is      *)
(* guaranteed to result in a negative x_i. We are only interested in         *)
(* increases to the duplication because our algorithm initializes all        *)
(* duplications to 1 and finds a fixed point by increasing duplication where *)
(* it would reduce overall fanout load.                                      *)
(*                                                                           *)
(* In detail, the algorithm checks every register in descending order of     *)
(* fanout load, and for a given register finds the x_i that would balance    *)
(* the fanout load with every driving register (or primary input). It then   *)
(* sets x to be the minimum of all the x_i, rounded down to the nearest      *)
(* integer. If x is less than 1 then nothing changes, otherwise we increase  *)
(* the duplication of the delay (and increase the n_i values for the driving *)
(* registers and primary inputs by x). When there are no more fanout load    *)
(* reductions possible, the algorithm terminates.                            *)
(* ------------------------------------------------------------------------- *)

type fanout_load = Fanout_load of int * int * float;;

type fanout_load_priority_queue =
     Fanout_load_priority_queue of (term * fanout_load) priority_queue;;

type circuit_fanout_loads = Circuit_fanout_loads of fanout_load wiremap;;

let mk_fanout_load d n = Fanout_load (d, n, float n /. float d);;

let add_fanout_load x (Fanout_load (d,n,_)) = mk_fanout_load d (n + x);;

let eq_fanout_load (Fanout_load (d1,n1,_)) (Fanout_load (d2,n2,_)) =
    d1 = d2 && n1 = n2;;

let lt_fanout_load (Fanout_load (_,_,l1)) (Fanout_load (_,_,l2)) = l1 < l2;;

let new_fanout_load_priority_queue (Circuit_primary_inputs pis) =
    let add w fl pq =
        if mem_wireset w pis then pq else
        add_priority_queue (w,fl) pq in
    let lt (_,fl1) (_,fl2) = lt_fanout_load fl1 fl2 in
    let empty = new_priority_queue lt in
    fun (Circuit_fanout_loads wm) ->
    Fanout_load_priority_queue (fold_wiremap add wm empty);;

let add_fanout_load_priority_queue primary_inputs flm =
    let Circuit_fanout_loads wm = flm in
    let add w pq =
        let fl = find_wiremap w wm in
        add_priority_queue (w,fl) pq in
    fun ws -> fun (Fanout_load_priority_queue pq) ->
    if size_priority_queue pq > 3 * size_wiremap wm then
      new_fanout_load_priority_queue primary_inputs flm
    else
      Fanout_load_priority_queue (rev_itlist add ws pq);;

let remove_fanout_load_priority_queue (Circuit_fanout_loads wm) =
    let rec remove pq =
        if null_priority_queue pq then None else
        let ((w,fl),pq) = remove_priority_queue pq in
        let fl' = find_wiremap w wm in
        if not (eq_fanout_load fl fl') then remove pq else
        Some ((w,fl), Fanout_load_priority_queue pq) in
    fun (Fanout_load_priority_queue pq) ->
    remove pq;;

let new_circuit_fanout_loads =
    let mk w ws = mk_fanout_load 1 (size_wireset ws) in
    fun (Circuit_fanouts wm) ->
    Circuit_fanout_loads (map_wiremap mk wm);;

let circuit_fanout_load (Circuit_fanout_loads wm) w = find_wiremap w wm;;

let update_circuit_fanout_loads w fl (Circuit_fanout_loads wm) =
    Circuit_fanout_loads (add_wiremap w fl wm);;

let add_circuit_fanout_loads x w fls =
    let fl = circuit_fanout_load fls w in
    let fl = add_fanout_load x fl in
    update_circuit_fanout_loads w fl fls;;

let circuit_fanout_loads =
    let increase_duplication d n =
        let find_balance fd fn =
            let a = 1.0 in
            let b = float (fn + d) in
            let c = float (fn * d - fd * n) in
            let b2 = b *. b in
            let ac4 = 4.0 *. a *. c in
            if b2 < ac4 then failwith "negative discriminant" else
            let x = (sqrt (b2 -. ac4) -. b) /. (2.0 *. a) in
            if x < 0.0 then 0 else truncate x in
        let load_balance (Fanout_load (fd,fn,_)) = find_balance fd fn in
        fun fls ->
        find_min (<) (map load_balance fls) in
    fun primary_inputs ->
    fun fanins ->
    fun fanouts ->
    let fan_in_out =
        let Circuit_primary_inputs pis = primary_inputs in
        let Circuit_fanouts fos = fanouts in
        let is_reg w = not (mem_wireset w pis) && mem_wiremap w fos in
        let is_blk wire w = w <> wire && is_reg w in
        let add_fio w fo fios =
            if mem_wireset w pis then fios else
            let (fi,_) = circuit_fanin fanins w in
            let self = mem_wireset w fi in
            let fi = if self then remove_wireset w fi else fi in
            let () =
                if not (null_wireset fi) then ()
                else failwith ("register " ^ dest_wire_var w ^ " has no fan-in") in
            let blk =
                let ws = union_wireset fi fo in
                filter (is_blk w) (to_list_wireset ws) in
            add_wiremap w (to_list_wireset fi, self, blk) fios in
        fold_wiremap add_fio fos empty_wiremap in
    let rec balance fls work =
        match remove_fanout_load_priority_queue fls work with
          None -> fls
        | Some ((w, Fanout_load (d,n,_)), work) ->
          let (fi,self,blk) = find_wiremap w fan_in_out in
          let fil = map (circuit_fanout_load fls) fi in
          let x = increase_duplication d n fil in
          if x = 0 then balance fls work else
          let d = d + x in
          let n = if self then n + x else n in
          let fl = mk_fanout_load d n in
          let fls = update_circuit_fanout_loads w fl fls in
          let fls = rev_itlist (add_circuit_fanout_loads x) fi fls in
          let work = add_fanout_load_priority_queue primary_inputs fls blk work in
(* Debugging
          let () =
              let msg =
                  "Raising duplication of wire " ^ string_of_term w ^
                  " to " ^ string_of_int d in
              complain msg in
*)
          balance fls work in
    let fls = new_circuit_fanout_loads fanouts in
    let work = new_fanout_load_priority_queue primary_inputs fls in
    balance fls work;;

(* Testing
let ckt = counter_91_ckt;;
let ckt = montgomery_91_ckt;;
let primary_inputs = debug_circuit_primary_inputs ckt;;
let fanins = debug_circuit_fanins ckt;;
let fanouts = debug_circuit_fanouts ckt;;
circuit_fanout_loads primary_inputs fanins fanouts;;
*)

(* ------------------------------------------------------------------------- *)
(* Profiling synthesized hardware.                                           *)
(* ------------------------------------------------------------------------- *)

let pp_print_count fmt (title,i) =
    let () = Format.pp_open_box fmt 2 in
    let () = Format.pp_print_string fmt (title ^ ":") in
    let () = Format.pp_print_space fmt () in
    let () = pp_print_pretty_int fmt i in
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

let pp_print_hardware_profile fmt ckt_info =
    let (primary_inputs,primary_outputs,registers,gates,fanins,fanouts,
         fanout_loads) = ckt_info in
    let duplication =
        let Circuit_primary_inputs pis = primary_inputs in
        let add w (Fanout_load (d,_,_)) acc =
            if mem_wireset w pis then acc else (w,d) :: acc in
        let Circuit_fanout_loads fols = fanout_loads in
        rev (fold_wiremap add fols []) in
    let primary_inputs =
        let Circuit_primary_inputs pis = primary_inputs in
        size_wireset pis in
    let primary_outputs =
        let Circuit_primary_outputs pos = primary_outputs in
        size_wireset pos in
    let registers =
        let Circuit_registers regs = registers in
        size_wireset regs in
    let gates =
        let Circuit_gates tms = gates in
        length tms in
    let (fanins,fanin_cones) =
        let fc w (f,c) z = ((w, size_wireset f), (w, size_wireset c)) :: z in
        let Circuit_fanins fis = fanins in
        unzip (fold_wiremap fc fis []) in
    let fanouts =
        let fc w f z = (w, size_wireset f) :: z in
        let Circuit_fanouts fos = fanouts in
        fold_wiremap fc fos [] in
    let fanout_loads =
        let add w (Fanout_load (_,_,l)) acc = (w, truncate l) :: acc in
        let Circuit_fanout_loads fols = fanout_loads in
        rev (fold_wiremap add fols []) in
    let pp_print_wire_dist =
        pp_print_distribution pp_print_term pp_print_pretty_int in
    let () = Format.pp_open_box fmt 0 in
    let () = pp_print_count fmt ("Primary inputs",primary_inputs) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_count fmt ("Primary outputs",primary_outputs) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_count fmt ("Registers",registers) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_count fmt ("Gates",gates) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_wire_dist fmt ("Fan-in",fanins) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_wire_dist fmt ("Fan-in cone",fanin_cones) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_wire_dist fmt ("Fan-out",fanouts) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_wire_dist fmt ("Duplication",duplication) in
    let () = Format.pp_print_newline fmt () in
    let () = pp_print_wire_dist fmt ("Fan-out load",fanout_loads) in
    let () = Format.pp_close_box fmt () in
    ();;

let hardware_profile_to_string = print_to_string pp_print_hardware_profile;;

(* Testing
print_string ("\n" ^ hardware_profile_to_string counter_91_ckt ^ "\n");;
print_string ("\n" ^ hardware_profile_to_string montgomery_91_ckt ^ "\n");;
*)

(* ------------------------------------------------------------------------- *)
(* Pretty-printing synthesized hardware in Verilog.                          *)
(* ------------------------------------------------------------------------- *)

let VERILOG_LINE_LENGTH = 79;;

type verilog_module = Verilog_module of string;;

type verilog_comment = Verilog_comment of string;;

type verilog_primary = Verilog_primary of term list;;

type verilog_arg =
     Wire_verilog_arg of term
   | Bus_verilog_arg of bus_wires;;

let default_verilog_comment () =
    let y = string_of_int (current_year ()) in
    let a = "Joe Leslie-Hurd" in
    let l = "MIT" in
    Verilog_comment
      ("\n\nCopyright (c) " ^ y ^ " " ^ a ^
       ", distributed under the " ^ l ^ " license");;

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
    let check_distinct =
        let add (w',w) wm =
            match peek_wiremap w' wm with
              None -> add_wiremap w' w wm
            | Some w2 ->
              let msg =
                  "verilog_wire_names: different wire names:\n  " ^
                  dest_wire_var w ^ "\n  " ^ dest_wire_var w2 ^
                  "map to the same verilog wire name:\n  " ^
                  dest_wire_var w' in
              failwith msg in
        fun sub ->
        let _ = rev_itlist add sub empty_wiremap in
        () in
    fun primary ->
    let is_primary =
        let Verilog_primary wl = primary in
        let ws = from_list_wireset wl in
        fun w ->
        mem_wireset w ws in
    let verilog_wire w acc =
        let w' =
            if is_primary w then w else
            let s = dest_wire_var w in
            mk_wire_var (verilog_name s) in
        (w',w) :: acc in
    fun ckt ->
    let (Circuit_wires ws) =
        let logic = circuit_logic ckt in
        circuit_wires logic in
    let sub = fold_wireset verilog_wire ws [] in
    let () = check_distinct sub in
    let Circuit th = ckt in
    Circuit (INST (norm_sub sub) th);;

let hardware_to_verilog =
    let no_comment _ = None in
    let wire_name w =
        if is_ground w then "1'b0" else
        if is_power w then "1'b1" else
        dest_wire_var w in
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
    let verilog_comment_line s = "  // " ^ s in
    let verilog_comment_box (Verilog_module name) comment ckt =
        let Verilog_comment footer = comment in
        let prop =
            let k = get_margin () in
            let () = set_margin (VERILOG_LINE_LENGTH - 4) in
            let s = string_of_term (spec_circuit ckt) in
            let () = set_margin k in
            s in
        comment_box_text
          ("module " ^ name ^ " satisfies the following property:\n\n" ^
           prop ^
           footer) ^ "\n" in
    let verilog_assign w s =
        "assign " ^ wire_name w ^ " = " ^ s ^ ";" in
    let verilog_module_begin (Verilog_module name) args =
        "module " ^ name ^ "(" ^
        String.concat "," (arg_names args) ^
        ");" in
    let verilog_connect tm =
        let (x,y) = dest_connect tm in
        verilog_assign y (wire_name x) in
    let verilog_not tm =
        let (x,y) = dest_not tm in
        verilog_assign y ("~" ^ wire_name x) in
    let verilog_and2 tm =
        let (x,y,z) = dest_and2 tm in
        verilog_assign z (wire_name x ^ " & " ^ wire_name y) in
    let verilog_or2 tm =
        let (x,y,z) = dest_or2 tm in
        verilog_assign z (wire_name x ^ " | " ^ wire_name y) in
    let verilog_xor2 tm =
        let (x,y,z) = dest_xor2 tm in
        verilog_assign z (wire_name x ^ " ^ " ^ wire_name y) in
    let verilog_case1 tm =
        let (w,x,y,z) = dest_case1 tm in
        verilog_assign z
          (wire_name w ^ " ? " ^ wire_name x ^ " : " ^ wire_name y) in
    let verilog_comb comb =
        if is_connect comb then verilog_connect comb
        else if is_not comb then verilog_not comb
        else if is_and2 comb then verilog_and2 comb
        else if is_or2 comb then verilog_or2 comb
        else if is_xor2 comb then verilog_xor2 comb
        else if is_case1 comb then verilog_case1 comb
        else failwith ("weird assumption: " ^ string_of_term comb) in
    let verilog_delay tm =
        let (w,r) = dest_delay tm in
        wire_name r ^ " <= " ^ wire_name w ^ ";" in
    let verilog_module_end (Verilog_module name) =
        "\nendmodule" ^ verilog_comment_line name ^ "\n" in
    let verilog_profile ckt_info =
        let prof =
            let n = get_margin () in
            let () = set_margin (VERILOG_LINE_LENGTH - 4) in
            let s = hardware_profile_to_string ckt_info in
            let () = set_margin n in
            s in
        "\n" ^ comment_box_text prof in
    fun h ->
    let print = output_string h in
    let verilog_declarations kind name comment xs =
        if length xs = 0 then () else
        let print_decl x =
            let n = name x in
            let c =
                match comment x with
                  None -> ""
                | Some s -> verilog_comment_line s in
            print ("  " ^ kind ^ " " ^ n ^ ";" ^ c ^ "\n") in
        let () = print "\n" in
        let () = List.iter print_decl xs in
        () in
    let verilog_wire_declarations kind comment wires =
        verilog_declarations kind wire_name comment wires in
    let verilog_arg_declarations kind args =
        verilog_declarations kind arg_decl no_comment args in
    let verilog_combinational defs wires =
        if length wires = 0 then () else
        let print_comb w =
            let s = verilog_comb (circuit_def defs w) in
            print ("  " ^ s ^ "\n") in
        let () = print "\n" in
        let () = List.iter print_comb wires in
        () in
    let verilog_delays clk defs registers =
        if length registers = 0 then () else
        let print_delay r =
            let s = verilog_delay (circuit_def defs r) in
            print ("      " ^ s ^ "\n") in
        let () = print "\n" in
        let () = print ("  always @(posedge " ^ wire_name clk ^ ")\n") in
        let () = print "    begin\n" in
        let () = List.iter print_delay registers in
        let () = print "    end\n" in
        () in
    let verilog_header name comment ckt =
        print (verilog_comment_box name comment ckt) in
    let verilog_body name primary ckt_info =
        let (defs,registers,gates,fanins,fanouts,fanout_loads) = ckt_info in
        let register_comment r =
            let (fi,fic) = circuit_fanin fanins r in
            let fi = size_wireset fi in
            let fic = size_wireset fic in
            let fo = size_wireset (circuit_fanout fanouts r) in
            let Fanout_load (d,_,fol) = circuit_fanout_load fanout_loads r in
            Some
              (string_of_pretty_int fi ^ ":" ^
               string_of_pretty_int fic ^ "|" ^
               string_of_pretty_int fo ^ "/" ^
               string_of_pretty_int d ^ "=" ^
               string_of_pretty_int (truncate fol)) in
        let registers =
            let Circuit_registers regs = registers in
            wire_sort (to_list_wireset regs) in
        let wires =
            let Circuit_gates gs = gates in
            wire_sort (map rand gs) in
        let (clk,(primary_outputs,primary_inputs)) =
            let Circuit_defs wm = defs in
            let has_def w = mem_wiremap w wm in
            let Verilog_primary ws = primary in
            (hd ws, partition has_def ws) in
        let primary_input_args = collect_verilog_args primary_inputs in
        let primary_output_args = collect_verilog_args primary_outputs in
        let primary_args = primary_input_args @ primary_output_args in
        let () = print (verilog_module_begin name primary_args) in
        let () = verilog_arg_declarations "input" primary_input_args in
        let () = verilog_arg_declarations "output" primary_output_args in
        let () = verilog_wire_declarations "reg" register_comment registers in
        let () = verilog_wire_declarations "wire" no_comment wires in
        let () = verilog_combinational defs (wires @ primary_outputs) in
        let () = verilog_delays clk defs registers in
        let () = print (verilog_module_end name) in
        () in
    let verilog_footer ckt_info = print (verilog_profile ckt_info) in
    fun name -> fun comment -> fun primary -> fun ckt ->
    let ckt =
        complain_timed "- Renamed wires"
          (verilog_wire_names primary) ckt in
    let logic = circuit_logic ckt in
    let wires = circuit_wires logic in
    let defs = circuit_defs logic in
    let primary_inputs = circuit_primary_inputs defs wires in
    let primary_outputs = circuit_primary_outputs logic in
    let registers = circuit_registers logic in
    let gates = circuit_gates logic in
    let fanins = circuit_fanins defs primary_inputs primary_outputs registers in
    let fanouts = circuit_fanouts fanins primary_inputs registers in
    let fanout_loads =
        complain_timed "- Duplicated logic"
          (circuit_fanout_loads primary_inputs fanins) fanouts in
    let () =
        complain_timed "- Generated spec"
          (verilog_header name comment) ckt in
    let () =
        let ckt_info = (defs,registers,gates,fanins,fanouts,fanout_loads) in
        complain_timed "- Generated module"
          (verilog_body name primary) ckt_info in
    let () =
        let ckt_info =
            (primary_inputs,primary_outputs,registers,gates,fanins,fanouts,
             fanout_loads) in
        complain_timed "- Generated profile"
          verilog_footer ckt_info in
    ();;

let hardware_to_verilog_file name comment primary ckt =
    let file =
        let Verilog_module n = name in
        "opentheory/hardware/" ^ n ^ ".v" in
    let h = open_out file in
    let () = hardware_to_verilog h name comment primary ckt in
    let () = close_out h in
    file;;
