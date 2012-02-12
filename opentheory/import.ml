(* ========================================================================= *)
(* OPENTHEORY ARTICLE READING FOR HOL LIGHT                                  *)
(* Ramana Kumar and Joe Hurd                                                 *)
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
   axiom_context : term list * term -> thm};;

type state =
  {stack : Object.t list;
   dict : Object.t Int_map.t;
   thms : thm list};;

let is_digit = function
  | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> true
  | _ -> false;;

let initial_state =
  {stack = [];
   dict = Int_map.empty;
   thms = []};;

let process_num state cmd =
    let {stack = stack; dict = dict; thms = thms} = state in
    let stack = Object.Num_object (int_of_string cmd) :: stack in
    {stack = stack; dict = dict; thms = thms};;

let process_name state cmd =
    match Name.from_string cmd with
      Some n ->
      let {stack = stack; dict = dict; thms = thms} = state in
      let stack = Object.Name_object n :: stack in
      {stack = stack; dict = dict; thms = thms}
    | None ->
      failwith ("bad name format in article: " ^ cmd);;

let process_command context state cmd =
  if String.length cmd = 0 then state else
  let c = String.get cmd 0 in
  if c = '#' then state else
  if c = '\"' then process_name state cmd else
  if is_digit c then process_num state cmd else
  let {stack = stack; dict = dict; thms = thms} = state in
  match (cmd,stack) with
    ("absTerm", objB :: objV :: stack) ->
    let stack = Object.mkAbsTerm objV objB :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("absThm", objB :: objV :: stack) ->
    let stack = Object.mkAbsThm objV objB :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("appTerm", objX :: objF :: stack) ->
    let stack = Object.mkAppTerm objF objX :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("appThm", objX :: objF :: stack) ->
    let stack = Object.mkAppThm objF objX :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("assume", objT :: stack) ->
    let stack = Object.mkAssume objT :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("axiom", objC :: objH :: stack) ->
    let stack = Object.mkAxiom (context.axiom_context) objH objC :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("betaConv", objT :: stack) ->
    let stack = Object.mkBetaConv objT :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("cons", objT :: objH :: stack) ->
    let stack = Object.mk_cons objH objT :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("const", objN :: stack) ->
    let stack = Object.mkConst (context.const_context) objN :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("constTerm", objT :: objC :: stack) ->
    let stack = Object.mkConstTerm objC objT :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("deductAntisym", obj2 :: obj1 :: stack) ->
    let stack = Object.mkDeductAntisym obj1 obj2 :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("def", Object.Num_object k :: (obj :: _ as stack)) ->
    let dict = Int_map.add k obj dict in
    {stack = stack; dict = dict; thms = thms}
  | ("defineConst", objT :: objN :: stack) ->
    let (objC,objD) = Object.mkDefineConst (context.const_context) objN objT in
    let stack = objD :: objC :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("defineTypeOp", objT :: objL :: objR :: objA :: objN :: stack) ->
    let (objT,objA,objR,objRA,objAR) =
      Object.mkDefineTypeOp (context.type_op_context)
        (context.const_context) objN objA objR objL objT in
    let stack = objAR :: objRA :: objR :: objA :: objT :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("eqMp", obj2 :: obj1 :: stack) ->
    let stack = Object.mkEqMp obj1 obj2 :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("nil", _) ->
    let stack = Object.mk_nil :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("opType", objL :: objT :: stack) ->
    let stack = Object.mkOpType objT objL :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("pop", _ :: stack) ->
    {stack = stack; dict = dict; thms = thms}
  | ("ref", Object.Num_object k :: stack) ->
    let obj = Int_map.find k dict in
    let stack = obj :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("refl", objT :: stack) ->
    let stack = Object.mkRefl objT :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("remove", Object.Num_object k :: stack) ->
    let obj = Int_map.find k dict in
    let dict = Int_map.remove k dict in
    let stack = obj :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("subst", objT :: objS :: stack) ->
    let stack = Object.mkSubst objS objT :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("thm", objC :: objH :: objT :: stack) ->
    let h_c = Object.dest_sequent (objH,objC) in
    let t = Object.dest_thm objT in
    let thms = thms @ [alpha_rule h_c t] in
    {stack = stack; dict = dict; thms = thms}
  | ("typeOp", objN :: stack) ->
    let stack = Object.mkTypeOp (context.type_op_context) objN :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("var", objT :: objN :: stack) ->
    let stack = Object.mkVar objN objT :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("varTerm", objV :: stack) ->
    let stack = Object.mkVarTerm objV :: stack in
    {stack = stack; dict = dict; thms = thms}
  | ("varType", objN :: stack) ->
    let stack = Object.mkVarType objN :: stack in
    {stack = stack; dict = dict; thms = thms}
  | _ -> failwith ("unhandled article line: " ^ cmd);;

let read_article context filename =
    let file = open_in filename in
    let rec loop line_number state =
        try let line = input_line file in
            let state =
                try process_command context state line
                with Failure f ->
                     failwith ("in article " ^ filename ^ " at line " ^
                               string_of_int line_number ^ ": " ^ line ^
                               "\nstack = " ^
                               Object.list_to_string (state.stack) ^
                               "\n" ^ f) in
            loop (line_number + 1) state
        with End_of_file -> state in
    let {stack = _; dict = _; thms = thms} = loop 1 initial_state in
    let () = close_in file in
    thms;;

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
        match peek_the_exported_thms (Sequent.Sequent (hs,c)) with
          Some th -> th
        | None -> failwith "import_context: unknown theorem" in
    {Import.const_context = const_context;
     Import.type_op_context = type_op_context;
     Import.axiom_context = axiom_context};;

let import_article = Import.read_article import_context;;
