(* ========================================================================= *)
(* OPENTHEORY OBJECTS                                                        *)
(* Joe Leslie-Hurd and Ramana Kumar                                          *)
(* ========================================================================= *)

module Object =
struct

(* ------------------------------------------------------------------------- *)
(* The original version of values whose names we will override.              *)
(* ------------------------------------------------------------------------- *)

let external_dest_type = dest_type
and external_mk_const = mk_const
and external_mk_type = mk_type
and external_mk_var = mk_var;;

(* ------------------------------------------------------------------------- *)
(* Utility functions.                                                        *)
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

(* ------------------------------------------------------------------------- *)
(* Inference rules used by articles.                                         *)
(* ------------------------------------------------------------------------- *)

let SYM th =
    let AP_TERM tm =
      let rth = REFL tm in
      fun th -> try MK_COMB(rth,th)
                with Failure _ -> failwith "AP_TERM" in
    let tm = concl th in
    let l,r = dest_eq tm in
    let lth = REFL l in
    let res = EQ_MP (MK_COMB(AP_TERM (rator (rator tm)) th,lth)) lth in
    let () = replace_proof res (Sym_proof th) in
    res;;

let PROVE_HYP ath bth =
    let aconv s t = alphaorder s t = 0 in
    if exists (aconv (concl ath)) (hyp bth)
    then let res = EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath in
         let () = replace_proof res (Prove_hyp_proof (ath,bth)) in
         res
    else bth;;

(* ------------------------------------------------------------------------- *)
(* The new principle of constant definition.                                 *)
(* ------------------------------------------------------------------------- *)

let define_const_list =
    let vassoc (v : term) =
        let pred (u, (_ : term)) = u = v in
        fun vm ->
        match partition pred vm with
          ([],vm) -> (None,vm)
        | ([(_,tm)],vm) -> (Some tm, vm)
        | (_ :: _ :: _, _) -> failwith "repeated vars" in
    let add tm vm =
        let (v,tm) = dest_eq tm in
        let () =
            match vassoc v vm with
              (None,_) -> ()
            | (Some _, _) -> failwith "repeated vars in assumptions" in
        (v,tm) :: vm in
    let del (n,v) vm =
        let (tm,vm) =
            match vassoc v vm with
              (None,_) -> failwith "given var not in assumptions"
            | (Some tm, vm) -> (tm,vm) in
        let def = new_basic_definition (mk_eq (mk_var (n, type_of v), tm)) in
        let (c,_) = dest_eq (concl def) in
        (((n,(c,v)),def),vm) in
    fun nvs -> fun th ->
    let vm = rev_itlist add (hyp th) [] in
    let () =
        if subset (frees (concl th)) (map snd nvs) then () else
        failwith "additional free vars in definition theorem" in
    let (cs,sub,defs) =
        let (cs_sub_defs,vm) = maps del nvs vm in
        let () =
            match vm with
              [] -> ()
            | _ :: _ ->
              failwith "additional assumptions in definition theorem" in
        let (cs_sub,defs) = unzip cs_sub_defs in
        let (cs,sub) = unzip cs_sub in
        (cs,sub,defs) in
    let res = rev_itlist PROVE_HYP defs (INST sub th) in
    let () =
        match cs with
          [] -> ()
        | c :: _ -> replace_proof res (Define_const_list_proof c) in
    let () =
        let f c i =
            let cdef = Const_list_definition (((nvs,th),res),i) in
            let () = replace_const_definition c cdef in
            i + 1 in
        let _ = rev_itlist f cs 0 in
        () in
    res;;

(* ------------------------------------------------------------------------- *)
(* Type matching.                                                            *)
(* ------------------------------------------------------------------------- *)

let rec type_match vty cty sofar =
  if is_vartype vty then
     try if rev_assoc vty sofar = cty then sofar else failwith "type_match"
     with Failure "find" -> (cty,vty)::sofar
  else
     let vop,vargs = dest_type vty and cop,cargs = dest_type cty in
     if vop = cop then itlist2 type_match vargs cargs sofar
     else failwith "type_match";;

(* ------------------------------------------------------------------------- *)
(* Variable names.                                                           *)
(* ------------------------------------------------------------------------- *)

let dest_type_var_name n =
    match Name.dest_type_var n with
      Some s -> s
    | None -> failwith ("bad type variable name: " ^ Name.to_string n);;

let dest_var_name n =
    match Name.dest_var n with
      Some s -> s
    | None -> failwith ("bad variable name: " ^ Name.to_string n);;

(* ------------------------------------------------------------------------- *)
(* A type of OpenTheory objects.                                             *)
(* ------------------------------------------------------------------------- *)

type t =
     Num_object of int
   | Name_object of Name.t
   | List_object of t list
   | Type_op_object of string
   | Type_object of hol_type
   | Const_object of string
   | Var_object of term
   | Term_object of term
   | Thm_object of thm;;

(* ------------------------------------------------------------------------- *)
(* A total comparison function.                                              *)
(* ------------------------------------------------------------------------- *)

let compare =
  let rec cmp obj1 obj2 =
      match (obj1,obj2) with
        (Num_object i1, Num_object i2) -> Pervasives.compare i1 i2
      | (Num_object _, _) -> -1
      | (_, Num_object _) -> 1
      | (Name_object n1, Name_object n2) -> Name.compare n1 n2
      | (Name_object _, _) -> -1
      | (_, Name_object _) -> 1
      | (List_object l1, List_object l2) -> cmp_list l1 l2
      | (List_object _, _) -> -1
      | (_, List_object _) -> 1
      | (Type_op_object t1, Type_op_object t2) -> String.compare t1 t2
      | (Type_op_object _, _) -> -1
      | (_, Type_op_object _) -> 1
      | (Type_object t1, Type_object t2) -> Pervasives.compare t1 t2
      | (Type_object _, _) -> -1
      | (_, Type_object _) -> 1
      | (Const_object c1, Const_object c2) -> String.compare c1 c2
      | (Const_object _, _) -> -1
      | (_, Const_object _) -> 1
      | (Var_object v1, Var_object v2) -> Pervasives.compare v1 v2
      | (Var_object _, _) -> -1
      | (_, Var_object _) -> 1
      | (Term_object t1, Term_object t2) -> Pervasives.compare t1 t2
      | (Term_object _, _) -> -1
      | (_, Term_object _) -> 1
      | (Thm_object t1, Thm_object t2) ->
        let c = Pervasives.compare (concl t1) (concl t2) in
        if c <> 0 then c else
        Pervasives.compare (hyp t1) (hyp t2)
  and cmp_list objs1 objs2 =
      match objs1 with
        [] -> (match objs2 with [] -> 0 | _ :: _ -> -1)
      | obj1 :: objs1 ->
        match objs2 with
          [] -> 1
        | obj2 :: objs2 ->
          let c = cmp obj1 obj2 in
          if c <> 0 then c else
          cmp_list objs1 objs2 in
  cmp;;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

let rec to_string obj =
    match obj with
      Num_object n -> string_of_int n
    | Name_object n -> Name.to_string n
    | List_object l -> list_to_string l
    | Type_op_object s -> "TypeOp<" ^ s ^ ">"
    | Type_object t -> "Type"
    | Const_object s -> "Const<" ^ s ^ ">"
    | Var_object _ -> "Var"
    | Term_object _ -> "Term"
    | Thm_object _ -> "Thm"
and list_to_string objs =
    "[" ^ String.concat "; " (List.map to_string objs) ^ "]";;

let option_to_string obj =
    match obj with
      Some ob -> to_string ob
    | None -> "Unknown";;

let option_list_to_string objs =
    "[" ^ String.concat "; " (List.map option_to_string objs) ^ "]";;

(* ------------------------------------------------------------------------- *)
(* Numbers.                                                                  *)
(* ------------------------------------------------------------------------- *)

let mk_num n = Num_object n;;

let dest_num obj =
    match obj with
      Num_object n -> n
    | _ -> failwith "Object.dest_num";;

(* ------------------------------------------------------------------------- *)
(* Names.                                                                    *)
(* ------------------------------------------------------------------------- *)

let mk_name n = Name_object n;;

let dest_name obj =
    match obj with
      Name_object n -> n
    | _ -> failwith "Object.dest_name";;

(* ------------------------------------------------------------------------- *)
(* Lists.                                                                    *)
(* ------------------------------------------------------------------------- *)

let mk_list l = List_object l;;

let dest_list obj =
    match obj with
      List_object l -> l
    | _ -> failwith "Object.dest_list";;

let dest_cons obj =
    match obj with
      List_object (h :: t) -> (h, List_object t)
    | _ -> failwith "Object.dest_cons";;

let mk_nil = mk_list [];;

let mk_cons objH objT =
    let t = dest_list objT in
    mk_list (objH :: t);;

(* ------------------------------------------------------------------------- *)
(* Type operators.                                                           *)
(* ------------------------------------------------------------------------- *)

let mk_type_op t = Type_op_object t;;

let dest_type_op obj =
    match obj with
      Type_op_object t -> t
    | _ -> failwith "Object.dest_type_op";;

(* ------------------------------------------------------------------------- *)
(* Types.                                                                    *)
(* ------------------------------------------------------------------------- *)

let mk_type t = Type_object t;;

let dest_type obj =
    match obj with
      Type_object t -> t
    | _ -> failwith "Object.dest_type";;

(* ------------------------------------------------------------------------- *)
(* Constants.                                                                *)
(* ------------------------------------------------------------------------- *)

let mk_const c = Const_object c;;

let dest_const obj =
    match obj with
      Const_object c -> c
    | _ -> failwith "Object.dest_const";;

(* ------------------------------------------------------------------------- *)
(* Variables.                                                                *)
(* ------------------------------------------------------------------------- *)

let mk_var v = Var_object v;;

let dest_var obj =
    match obj with
      Var_object v -> v
    | _ -> failwith "Object.dest_var";;

(* ------------------------------------------------------------------------- *)
(* Terms.                                                                    *)
(* ------------------------------------------------------------------------- *)

let mk_term t = Term_object t;;

let dest_term obj =
    match obj with
      Term_object t -> t
    | _ -> failwith "Object.dest_term";;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

let mk_thm t = Thm_object t;;

let dest_thm obj =
    match obj with
      Thm_object t -> t
    | _ -> failwith "Object.dest_thm";;

(* ------------------------------------------------------------------------- *)
(* Pairs.                                                                    *)
(* ------------------------------------------------------------------------- *)

let mk_pair (a,b) = List_object [a; b];;

let dest_pair obj =
    match dest_list obj with
      [a; b] -> (a,b)
    | _ -> failwith "Object.dest_pair";;

(* ------------------------------------------------------------------------- *)
(* Name lists.                                                               *)
(* ------------------------------------------------------------------------- *)

let mk_name_list ns = List_object (List.map mk_name ns);;

let dest_name_list obj = List.map dest_name (dest_list obj);;

(* ------------------------------------------------------------------------- *)
(* Type lists.                                                               *)
(* ------------------------------------------------------------------------- *)

let mk_type_list ts = List_object (List.map mk_type ts);;

let dest_type_list obj = List.map dest_type (dest_list obj);;

(* ------------------------------------------------------------------------- *)
(* Term lists.                                                               *)
(* ------------------------------------------------------------------------- *)

let mk_term_list ts = List_object (List.map mk_term ts);;

let dest_term_list obj = List.map dest_term (dest_list obj);;

(* ------------------------------------------------------------------------- *)
(* Sequents.                                                                 *)
(* ------------------------------------------------------------------------- *)

let mk_sequent (Sequent.Sequent (h,c)) = (mk_term_list h, mk_term c);;

let dest_sequent (objH,objC) =
    Sequent.Sequent (dest_term_list objH, dest_term objC);;

(* ------------------------------------------------------------------------- *)
(* Type variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let mk_type_var v = Name_object (Name.mk_type_var v);;

let dest_type_var obj = dest_type_var_name (dest_name obj);;

(* ------------------------------------------------------------------------- *)
(* Type substitutions.                                                       *)
(* ------------------------------------------------------------------------- *)

let mk_type_subst =
    let mk (ty,v) = mk_pair (mk_type_var (dest_vartype v), Type_object ty) in
    fun sub ->
    List_object (List.map mk sub);;

let dest_type_subst =
    let dest obj =
        let (v_obj,ty_obj) = dest_pair obj in
        (dest_type ty_obj, mk_vartype (dest_type_var v_obj)) in
    fun obj ->
    List.map dest (dest_list obj);;

(* ------------------------------------------------------------------------- *)
(* Term substitutions.                                                       *)
(* ------------------------------------------------------------------------- *)

let mk_term_subst =
    let mk (tm,v) = mk_pair (Var_object v, Term_object tm) in
    fun sub ->
    List_object (List.map mk sub);;

let dest_term_subst =
    let dest obj =
        let (v_obj,tm_obj) = dest_pair obj in
        (dest_term tm_obj, dest_var v_obj) in
    fun obj ->
    List.map dest (dest_list obj);;

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

let mk_subst (ty_sub,tm_sub) =
    mk_pair (mk_type_subst ty_sub, mk_term_subst tm_sub);;

let dest_subst obj =
    let (ty_obj,tm_obj) = dest_pair obj in
    (dest_type_subst ty_obj, dest_term_subst tm_obj);;

(* ------------------------------------------------------------------------- *)
(* Commands.                                                                 *)
(* ------------------------------------------------------------------------- *)

let mkAbsTerm objV objB =
    let v = dest_var objV in
    let b = dest_term objB in
    Term_object (mk_abs (v,b));;

let mkAbsThm objV objB =
    let v = dest_var objV in
    let b = dest_thm objB in
    Thm_object (ABS v b);;

let mkAppTerm objF objX =
    let f = dest_term objF in
    let x = dest_term objX in
    Term_object (mk_comb (f,x));;

let mkAppThm objF objX =
    let f = dest_thm objF in
    let x = dest_thm objX in
    Thm_object (MK_COMB (f,x));;

let mkAssume objT =
    let t = dest_term objT in
    Thm_object (ASSUME t);;

let mkBetaConv objT =
    let t = dest_term objT in
    let (f,x) = dest_comb t in
    let (v,_) = dest_abs f in
    let th = INST [(x,v)] (BETA (mk_comb (f,v))) in
    Thm_object th;;

let mkConst const_context objN =
    let n = dest_name objN in
    Const_object (const_context n);;

let mkConstTerm objC objT =
    let c = dest_const objC in
    let ty = dest_type objT in
    let cty =
        try get_const_type c
        with Failure _ -> let () = new_constant (c,aty) in aty in
    let theta = type_match cty ty [] in
    Term_object (external_mk_const (c,theta));;

let mkDeductAntisym obj1 obj2 =
    let t1 = dest_thm obj1 in
    let t2 = dest_thm obj2 in
    Thm_object (DEDUCT_ANTISYM_RULE t1 t2);;

let mkDefineConst const_context objN objT =
    let n = dest_name objN in
    let c = const_context n in
    let t = dest_term objT in
    let tm = mk_eq (external_mk_var (c, type_of t), t) in
    let th = new_basic_definition tm in
    (Const_object c, Thm_object th);;

let mkDefineConstList const_context objL objT =
    let f nv =
        let (n,v) = dest_pair nv in
        (const_context (dest_name n), dest_var v) in
    let g (c,_) = Const_object c in
    let l = map f (dest_list objL) in
    let th = dest_thm objT in
    let def = define_const_list l th in
    (mk_list (map g l), Thm_object def);;

let mkDefineTypeOp type_op_context const_context objN objA objR objL objT =
    let n = dest_name objN in
    let a = dest_name objA in
    let r = dest_name objR in
    let l = dest_name_list objL in
    let t = dest_thm objT in
    let n = type_op_context n in
    let a = const_context a in
    let r = const_context r in
    let l = List.map dest_type_var_name l in
    let (ra,ar) = new_basic_type_definition n (a,r) t in
    let () =
        let (_,v) = dest_eq (concl ra) in
        let (_,l') = external_dest_type (type_of v) in
        let l' = List.map dest_vartype l' in
        if l' = l then () else
        failwith "type variable list does not match specification" in
    let ra =
        let (_,v) = dest_eq (concl ra) in
        ABS v ra in
    let ar =
        let (p,_) = dest_eq (concl ar) in
        let (_,v) = dest_comb p in
        ABS v (SYM ar) in
    let n = Type_op_object n in
    let a = Const_object a in
    let r = Const_object r in
    let ra = Thm_object ra in
    let ar = Thm_object ar in
    (n,a,r,ra,ar);;

let mkEqMp obj1 obj2 =
    let t1 = dest_thm obj1 in
    let t2 = dest_thm obj2 in
    Thm_object (EQ_MP t1 t2);;

let mkHdTl objL = dest_cons objL;;

let mkOpType objT objL =
    let t = dest_type_op objT in
    let l = dest_type_list objL in
    let n = List.length l in
    let tn =
        try get_type_arity t
        with Failure _ -> let () = new_type (t,n) in n in
    let () =
        if n = tn then ()
        else failwith ("arity mismatch for type operator " ^ t) in
    Type_object (external_mk_type (t,l));;

let mkProveHyp obj1 obj2 =
    let t1 = dest_thm obj1 in
    let t2 = dest_thm obj2 in
    Thm_object (PROVE_HYP t1 t2) ;;

let mkRefl objT =
    let t = dest_term objT in
    Thm_object (REFL t);;

let mkSubst objS objT =
    let (tys,tms) = dest_subst objS in
    let t = dest_thm objT in
    Thm_object (INST tms (INST_TYPE tys t));;

let mkSym obj1 =
    let t1 = dest_thm obj1 in
    Thm_object (SYM t1);;

let mkTrans obj1 obj2 =
    let t1 = dest_thm obj1 in
    let t2 = dest_thm obj2 in
    Thm_object (TRANS t1 t2);;

let mkTypeOp type_op_context objN =
    let n = dest_name objN in
    Type_op_object (type_op_context n);;

let mkVar objN objT =
    let n = dest_name objN in
    let s = dest_var_name n in
    let t = dest_type objT in
    Var_object (external_mk_var (s,t));;

let mkVarTerm objV =
    let v = dest_var objV in
    Term_object v;;

let mkVarType objN =
    let n = dest_name objN in
    let s = dest_type_var_name n in
    Type_object (mk_vartype s);;

end

module Object_map = Map.Make(Object);;
