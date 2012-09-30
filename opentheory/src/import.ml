(* ========================================================================= *)
(* OPENTHEORY ARTICLE READING FOR HOL LIGHT                                  *)
(* Ramana Kumar and Joe Leslie-Hurd                                          *)
(* ========================================================================= *)

module Int_map = Map.Make (struct type t = int let compare = compare end);;

module Import =
struct

(* ------------------------------------------------------------------------- *)
(* Alpha conversion.                                                         *)
(* ------------------------------------------------------------------------- *)

let ALPHA tm1 tm2 =
  try TRANS (REFL tm1) (REFL tm2)
  with Failure _ -> failwith "Import.ALPHA";;

let alpha_rule =
    let alpha_hyp th h =
        let hs' = hyp th in
        if mem h hs' then th else
        let th0 = ASSUME h in
        let th1 = DEDUCT_ANTISYM_RULE th0 th in
        EQ_MP th1 th0 in
    fun (hs,c) th ->
    let c' = concl th in
    let th = if c = c' then th else EQ_MP (ALPHA c' c) th in
    List.fold_left alpha_hyp th hs;;

(* ------------------------------------------------------------------------- *)
(* A type of import states.                                                  *)
(* ------------------------------------------------------------------------- *)

type context =
  {const_context : Name.t -> string;
   type_op_context : Name.t -> string;
   axiom_context : term list * term -> thm option};;

type state =
  {stack : Object.t option list;
   dict : Object.t option Int_map.t;
   asms : (term list * term) list;
   thms : (thm option * (term list * term)) option list};;

let is_digit = function
  | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> true
  | _ -> false;;

let initial_state =
  {stack = [];
   dict = Int_map.empty;
   asms = [];
   thms = []};;

let process_num state cmd =
    let {stack = stack; dict = dict; asms = asms; thms = thms} = state in
    let obj = Some (Object.Num_object (int_of_string cmd)) in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms};;

let process_name state cmd =
    match Name.from_string cmd with
      Some n ->
      let {stack = stack; dict = dict; asms = asms; thms = thms} = state in
      let obj = Some (Object.Name_object n) in
      let stack = obj :: stack in
      {stack = stack; dict = dict; asms = asms; thms = thms}
    | None ->
      failwith ("bad name format in article: " ^ cmd);;

let process_command context state cmd =
  if String.length cmd = 0 then state else
  let c = String.get cmd 0 in
  if c = '#' then state else
  if c = '\"' then process_name state cmd else
  if is_digit c then process_num state cmd else
  let {stack = stack; dict = dict; asms = asms; thms = thms} = state in
  match (cmd,stack) with
    ("absTerm", objB :: objV :: stack) ->
    let obj =
        match (objV,objB) with
          (Some v, Some b) -> Some (Object.mkAbsTerm v b)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("absThm", objB :: objV :: stack) ->
    let obj =
        match (objV,objB) with
          (Some v, Some b) -> Some (Object.mkAbsThm v b)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("appTerm", objX :: objF :: stack) ->
    let obj =
        match (objF,objX) with
          (Some f, Some x) -> Some (Object.mkAppTerm f x)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("appThm", objX :: objF :: stack) ->
    let obj =
        match (objF,objX) with
          (Some f, Some x) -> Some (Object.mkAppThm f x)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("assume", objT :: stack) ->
    let obj =
        match objT with
          Some t -> Some (Object.mkAssume t)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("axiom", objC :: objH :: stack) ->
    let (h,c) =
      match (objH,objC) with
        (Some h, Some c) -> (h,c)
      | (Some _, None) -> failwith "unknown conclusion"
      | (None, Some _) -> failwith "unknown hypotheses"
      | (None, None) -> failwith "unknown hypotheses and conclusion" in
    let h = Object.dest_term_list h in
    let c = Object.dest_term c in
    (match context.axiom_context (h,c) with
       Some th ->
       let stack = Some (Object.Thm_object th) :: stack in
       {stack = stack; dict = dict; asms = asms; thms = thms}
     | None ->
       let stack = None :: stack in
       let asms = asms @ [(h,c)] in
       {stack = stack; dict = dict; asms = asms; thms = thms})
  | ("betaConv", objT :: stack) ->
    let obj =
        match objT with
          Some t -> Some (Object.mkBetaConv t)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("cons", objT :: objH :: stack) ->
    let obj =
        match (objH,objT) with
          (Some h, Some t) -> Some (Object.mk_cons h t)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("const", objN :: stack) ->
    let obj =
        match objN with
          Some n -> Some (Object.mkConst (context.const_context) n)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("constTerm", objT :: objC :: stack) ->
    let obj =
        match (objC,objT) with
          (Some c, Some t) -> Some (Object.mkConstTerm c t)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("deductAntisym", objU :: objT :: stack) ->
    let obj =
        match (objT,objU) with
          (Some t, Some u) -> Some (Object.mkDeductAntisym t u)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("def", Some (Object.Num_object k) :: (obj :: _ as stack)) ->
    let dict = Int_map.add k obj dict in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("defineConst", objT :: objN :: stack) ->
    let (objC,objD) =
        match (objN,objT) with
          (Some n, Some t) ->
          let (c,d) = Object.mkDefineConst (context.const_context) n t in
          (Some c, Some d)
        | _ -> (None,None) in
    let stack = objD :: objC :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("defineTypeOp", objT :: objL :: objR :: objA :: objN :: stack) ->
    let (objT,objA,objR,objRA,objAR) =
        match (objN,objA,objR,objL,objT) with
          (Some n, Some a, Some r, Some l, Some t) ->
          let (t,a,r,ra,ar) =
              Object.mkDefineTypeOp (context.type_op_context)
                (context.const_context) n a r l t in
          (Some t, Some a, Some r, Some ra, Some ar)
        | _ -> (None,None,None,None,None) in
    let stack = objAR :: objRA :: objR :: objA :: objT :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("eqMp", objU :: objT :: stack) ->
    let obj =
        match (objT,objU) with
          (Some t, Some u) -> Some (Object.mkEqMp t u)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("nil", _) ->
    let stack = Some Object.mk_nil :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("opType", objL :: objT :: stack) ->
    let obj =
        match (objT,objL) with
          (Some t, Some l) -> Some (Object.mkOpType t l)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("pop", _ :: stack) ->
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("ref", Some (Object.Num_object k) :: stack) ->
    let obj = Int_map.find k dict in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("refl", objT :: stack) ->
    let obj =
        match objT with
          Some t -> Some (Object.mkRefl t)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("remove", Some (Object.Num_object k) :: stack) ->
    let obj = Int_map.find k dict in
    let dict = Int_map.remove k dict in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("subst", objT :: objS :: stack) ->
    let obj =
        match (objS,objT) with
          (Some s, Some t) -> Some (Object.mkSubst s t)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("thm", objC :: objH :: objT :: stack) ->
    let thm =
      match (objH,objC) with
        (Some h, Some c) ->
        let h_c = Object.dest_sequent (h,c) in
        let t =
            match objT with
              Some t -> Some (alpha_rule h_c (Object.dest_thm t))
            | None -> None in
        Some (t,h_c)
      | _ -> None in
    let thms = thms @ [thm] in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("typeOp", objN :: stack) ->
    let obj =
        match objN with
          Some n -> Some (Object.mkTypeOp (context.type_op_context) n)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("var", objT :: objN :: stack) ->
    let obj =
        match (objN,objT) with
          (Some n, Some t) -> Some (Object.mkVar n t)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("varTerm", objV :: stack) ->
    let obj =
        match objV with
          Some v -> Some (Object.mkVarTerm v)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("varType", objN :: stack) ->
    let obj =
        match objN with
          Some n -> Some (Object.mkVarType n)
        | _ -> None in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | _ -> failwith ("unhandled article line: " ^ cmd);;

let read_article context name h =
    let rec loop line_number state =
        try let line = input_line h in
            let state =
                try process_command context state line
                with Failure f ->
                     failwith ("in article " ^ name ^ " at line " ^
                               string_of_int line_number ^ ": " ^ line ^
                               "\nstack = " ^
                               Object.option_list_to_string (state.stack) ^
                               "\n" ^ f) in
            loop (line_number + 1) state
        with End_of_file -> state in
    let {stack = _; dict = _; asms = asms; thms = thms} = loop 1 initial_state in
    (asms,thms);;

end

let import_context =
    let const_context n =
        let n =
            match import_const_from_the_interpretation n with
              [] -> n
            | n :: _ -> n in
        match Name.dest_const n with
          Some s -> s
        | None -> failwith ("unknown constant " ^ Name.to_string n) in
    let type_op_context n =
        let n =
            match import_type_op_from_the_interpretation n with
              [] -> n
            | n :: _ -> n in
        match Name.dest_type_op n with
          Some s -> s
        | None -> failwith ("unknown type operator " ^ Name.to_string n) in
    let axiom_context (hs,c) =
        peek_the_exported_thms (Sequent.Sequent (hs,c)) in
    {Import.const_context = const_context;
     Import.type_op_context = type_op_context;
     Import.axiom_context = axiom_context};;

let import_article filename =
  let h = open_in filename in
  let r = Import.read_article import_context filename h in
  let _ = close_in h in
  r
