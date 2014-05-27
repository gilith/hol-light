(* ========================================================================= *)
(* PROOF TOOLS FOR THE HASKELL BASE                                          *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

module Haskell =
struct

(* ------------------------------------------------------------------------- *)
(* Haskell-in-HOL names.                                                     *)
(* ------------------------------------------------------------------------- *)

let mk_haskell_name s = s ^ "H";;

let dest_haskell_name s =
    let n = String.length s in
    if n <= 1 then None else
    if String.get s (n - 1) <> 'H' then None
    else Some (String.sub s 0 (n - 1));;

(* ------------------------------------------------------------------------- *)
(* Haskell simplifications.                                                  *)
(* ------------------------------------------------------------------------- *)

type haskell_simp_thms =
     Haskell_simp_thms of thm list;;

let empty_haskell_simp_thms =
    Haskell_simp_thms
      [I_THM;
       O_I;
       I_O;
       o_THM;
       o_ASSOC'];;

let add_haskell_simp_thm =
    let o_thm = prove
      (`!(f : B -> A) (g : C -> B) (h : C -> A).
          f o g = h ==>
          (!(j : Z -> C). f o (g o j) = h o j) /\
          (!(x : C). f (g x) = h x)`,
       REPEAT STRIP_TAC THENL
       [ASM_REWRITE_TAC [o_ASSOC];
        CONV_TAC (LAND_CONV (REWR_CONV (GSYM o_THM))) THEN
        ASM_REWRITE_TAC []]) in
    let o_rule th =
        let (th1,th2) = CONJ_PAIR (MATCH_MP o_thm (SPEC_ALL th)) in
        (GEN_ALL th1, GEN_ALL th2) in
    fun st th ->
      match st with
        Haskell_simp_thms ths ->
          let news =
              try let (th1,th2) = o_rule th in
                  [th; th1; th2]
              with Failure _ -> [th] in
          let ths = news @ ths in
          Haskell_simp_thms ths;;

let add_haskell_simp_thms = List.fold_left add_haskell_simp_thm;;

let haskell_simp_thms st =
    match st with
      Haskell_simp_thms ths -> ths;;

let initial_haskell_simp_thms =
    add_haskell_simp_thms empty_haskell_simp_thms
      [map_option_id; map_option_o';
       MAP_I; MAP_o';
       smap_id; smap_o'];;

let the_haskell_thms = ref initial_haskell_simp_thms;;

let add_haskell_thms ths =
    let st = !the_haskell_thms in
    let st = add_haskell_simp_thms st ths in
    let () = the_haskell_thms := st in
    ();;

let add_haskell_thm th = add_haskell_thms [th];;

let haskell_thms () =
    let st = !the_haskell_thms in
    haskell_simp_thms st;;

let HASKELL_TAC ths goal = REWRITE_TAC (ths @ haskell_thms ()) goal;;

let ASM_HASKELL_TAC ths goal = ASM_REWRITE_TAC (ths @ haskell_thms ()) goal;;

(* ------------------------------------------------------------------------- *)
(* Maintaining a mapping from HOL types to Haskell-in-HOL types.             *)
(* ------------------------------------------------------------------------- *)

type haskell_type_data =
     {tyop : (string * string) option;
      vars : (string * bool * bool) list};;

type haskell_type_base =
     Haskell_type_base of haskell_type_data String_map.t;;

let empty_haskell_type_base =
    Haskell_type_base String_map.empty;;

let add_haskell_type_base tb (n,ld,vs) =
    match tb with
      Haskell_type_base m ->
        let td = {tyop = ld; vars = vs} in
        Haskell_type_base (String_map.add n td m);;

let mem_haskell_type_base tb n =
    match tb with
      Haskell_type_base m ->
        String_map.mem n m;;

let find_haskell_type_base tb n =
    match tb with
      Haskell_type_base m ->
        String_map.find n m;;

let peek_haskell_type_base tb n =
    if not (mem_haskell_type_base tb n) then None
    else Some (find_haskell_type_base tb n);;

let to_list_haskell_type_base tb =
    match tb with
      Haskell_type_base m ->
        rev (String_map.fold (fun k -> fun _ -> fun ks -> k :: ks) m []);;

let lift_drop_haskell_type tb =
    let mk_const_at_type (c,ty) =
        try let cty = get_const_type c in
            let theta = type_match cty ty [] in
            mk_const (c,theta)
        with Failure _ ->
          let msg =
              "mk_const_at_type: (" ^ c ^ ", " ^ string_of_type ty ^ ")" in
          failwith msg in
    let mk_i ty =
        let ity = mk_fun_ty ty ty in
        mk_const_at_type ("I",ity) in
    let mk_o (f,g) =
        let fty = type_of f in
        let (_,rng) = dest_fun_ty fty in
        let gty = type_of g in
        let (dom,_) = dest_fun_ty gty in
        let oty = mk_fun_ty fty (mk_fun_ty gty (mk_fun_ty dom rng)) in
        let otm = mk_const_at_type ("o",oty) in
        mk_comb (mk_comb (otm,f), g) in
    let list_mk_o fs =
        match List.rev fs with
          [] -> failwith "Haskell.lift_drop_haskell_type_base.list_mk_o: empty"
        | f :: fs -> List.fold_left (fun t -> fun g -> mk_o (g,t)) f fs in
    let rec lift ty =
        if is_vartype ty then (ty,[]) else
        let (ot,tys) = dest_type ty in
        let () =
            if mem_haskell_type_base tb ot then () else
            failwith ("unknown type op: " ^ ot) in
        let {tyop = ld; vars = vs} = find_haskell_type_base tb ot in
        let (res,tysH) = lift_vars ty ot [] [] vs tys in
        let pty = mk_type (ot,tysH) in
        match ld with
          None -> (pty,res)
        | Some (l,_) ->
          let otH = mk_haskell_name ot in
          let tyH = mk_type (otH,tysH) in
          let lty = mk_fun_ty pty tyH in
          let ltm = mk_const_at_type (l,lty) in
          (tyH, ltm :: res)
    and lift_vars pty ot res tysH vs tys =
        match (vs,tys) with
          ([],[]) -> (res, List.rev tysH)
        | ([], _ :: _) -> failwith "Haskell.lift_drop_haskell_type.lift_vars"
        | (_ :: _, []) -> failwith "Haskell.lift_drop_haskell_type.lift_vars"
        | ((c,l,d) :: vs, ty :: tys) ->
          let (tyH,lifts) = lift ty in
          if List.length lifts = 0 then
            lift_vars pty ot res (tyH :: tysH) vs tys
          else
            let pty' = mk_type (ot, List.rev tysH @ tyH :: tys) in
            let cty =
                let t = mk_fun_ty pty pty' in
                let t = if d then mk_fun_ty (mk_fun_ty tyH ty) t else t in
                let t = if l then mk_fun_ty (mk_fun_ty ty tyH) t else t in
                t in
            let ctm = mk_const_at_type (c,cty) in
            let ctm =
                if not l then ctm else
                mk_comb (ctm, list_mk_o lifts) in
            let ctm =
                if not d then ctm else
                let (_,drops) = drop tyH in
                mk_comb (ctm, list_mk_o drops) in
            lift_vars pty' ot (ctm :: res) (tyH :: tysH) vs tys
    and drop tyH =
        if is_vartype tyH then (tyH,[]) else
        let (otH,tysH) = dest_type tyH in
        let (ot,ld,vs) =
            let (b,ot) =
                match dest_haskell_name otH with
                  Some ot -> (true,ot)
                | None -> (false,otH) in
            let () =
                if mem_haskell_type_base tb ot then () else
                failwith ("unknown type op: " ^ ot) in
            let {tyop = ld; vars = vs} = find_haskell_type_base tb ot in
            let () =
                let b' =
                    match ld with
                      Some _ -> true
                    | None -> false in
                if b = b' then () else
                failwith ("bad primitive type op: " ^ ot) in
            (ot,ld,vs) in
        let (pty,res) =
            match ld with
              None -> (tyH,[])
            | Some (_,d) ->
              let pty = mk_type (ot,tysH) in
              let dty = mk_fun_ty tyH pty in
              let dtm = mk_const_at_type (d,dty) in
              (pty,[dtm]) in
        let (res,tys) = drop_vars pty ot res [] (List.rev vs) (List.rev tysH) in
        let ty = mk_type (ot,tys) in
        (ty,res)
    and drop_vars pty ot res tys vs tysH =
        match (vs,tysH) with
          ([],[]) -> (res,tys)
        | ([], _ :: _) -> failwith "Haskell.lift_drop_haskell_type.drop_vars"
        | (_ :: _, []) -> failwith "Haskell.lift_drop_haskell_type.drop_vars"
        | ((c,l,d) :: vs, tyH :: tysH) ->
          let (ty,drops) = drop tyH in
          if List.length drops = 0 then
            drop_vars pty ot res (ty :: tys) vs tysH
          else
            let pty' = mk_type (ot, List.rev tysH @ ty :: tys) in
            let cty =
                let t = mk_fun_ty pty pty' in
                let t = if d then mk_fun_ty (mk_fun_ty ty tyH) t else t in
                let t = if l then mk_fun_ty (mk_fun_ty tyH ty) t else t in
                t in
            let ctm = mk_const_at_type (c,cty) in
            let ctm =
                if not l then ctm else
                mk_comb (ctm, list_mk_o drops) in
            let ctm =
                if not d then ctm else
                let (_,lifts) = lift ty in
                mk_comb (ctm, list_mk_o lifts) in
            drop_vars pty' ot (ctm :: res) (ty :: tys) vs tysH in
      let lift_ty ty =
          let (tyH,lifts) = lift ty in
          let tm =
              if List.length lifts = 0 then mk_i ty else
              list_mk_o lifts in
          (tyH,tm) in
      let drop_ty tyH =
          let (ty,drops) = drop tyH in
          let tm =
              if List.length drops = 0 then mk_i tyH else
              list_mk_o drops in
          (ty,tm) in
      (lift_ty,drop_ty);;

let initial_haskell_type_base =
    List.fold_left add_haskell_type_base empty_haskell_type_base
    [("bool", None, []);
     ("byte", None, []);
     ("fun", None, [("map_domain", false, true); ("map_range", true, false)]);
     ("list", None, [("MAP", true, false)]);
     ("num", None, []);
     ("option", None, [("map_option", true, false)]);
     ("prod", None, [("map_fst", true, false); ("map_snd", true, false)]);
     ("random", None, []);
     ("stream", None, [("smap", true, false)]);
     ("word16", None, [])];;

let the_haskell_type_base =
    ref initial_haskell_type_base;;

let haskell_types () =
    to_list_haskell_type_base (!the_haskell_type_base);;

let register_haskell_type (n,l,d,vs) =
    let n =
        match dest_haskell_name n with
          None -> failwith ("not a haskell name: " ^ n)
        | Some x -> x in
    let tb = !the_haskell_type_base in
    let tb = add_haskell_type_base tb (n, Some (l,d), vs) in
    let () = the_haskell_type_base := tb in
    ();;

let define_haskell_type ty vs =
    let (ot,tys) = dest_type ty in
    let () =
        if List.length tys = List.length vs then () else
        failwith "define_haskell_type: bad variable list length" in
    let otH = mk_haskell_name ot in
    let mk n = "mkH_" ^ n in
    let dest n = "destH_" ^ n in
    let tybij = define_newtype' (mk,dest) ("h",otH) ("x",ty) in
    let () = register_haskell_type (otH, mk otH, dest otH, vs) in
    let () = add_haskell_thms (CONJUNCTS (prove_newtype_o tybij)) in
    let () = add_haskell_thm (prove_newtype_inj tybij) in
    tybij;;

let lift_haskell_type ty =
    let (lift,_) = lift_drop_haskell_type (!the_haskell_type_base) in
    lift ty;;

let drop_haskell_type tyH =
    let (_,drop) = lift_drop_haskell_type (!the_haskell_type_base) in
    drop tyH;;

(* ------------------------------------------------------------------------- *)
(* Maintaining a mapping from HOL constants to Haskell-in-HOL constants.     *)
(* ------------------------------------------------------------------------- *)

let define_haskell_const =
    let is_i tm =
        try let (s,_) = dest_const tm in
            s = "I"
        with Failure _ -> false in
    fun tm ->
      let (c,ty) = dest_const tm in
      let cH = mk_haskell_name c in
      let (tyH,ltm) = lift_haskell_type ty in
      let def = if is_i ltm then tm else mk_comb (ltm,tm) in
      let def = mk_eq (mk_var (cH,tyH), def) in
      let th = new_definition def in
      let () = add_haskell_thm th in
      th;;

(* ------------------------------------------------------------------------- *)
(* Haskellizing type variables in theorems.                                  *)
(* ------------------------------------------------------------------------- *)

let haskellize_thm =
    let mk_type_map acc v =
        let s = dest_vartype v in
        let s' = String.lowercase s in
        if s = s' then acc else (mk_vartype s', v) :: acc in
    fun th ->
        let vs = type_vars_in_term (concl th) in
        if length vs = 0 then th else
        INST_TYPE (List.fold_left mk_type_map [] vs) th;;

let export_haskell_thm th = export_thm (haskellize_thm th);;

end

(* ------------------------------------------------------------------------- *)
(* The Haskell proof tool interface.                                         *)
(* ------------------------------------------------------------------------- *)

let add_haskell_thm = Haskell.add_haskell_thm
and add_haskell_thms = Haskell.add_haskell_thms
and define_haskell_const = Haskell.define_haskell_const
and define_haskell_type = Haskell.define_haskell_type
and export_haskell_thm = Haskell.export_haskell_thm
and haskell_thms = Haskell.haskell_thms
and haskell_types = Haskell.haskell_types
and ASM_HASKELL_TAC = Haskell.ASM_HASKELL_TAC
and HASKELL_TAC = Haskell.HASKELL_TAC;;
