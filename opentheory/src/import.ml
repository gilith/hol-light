(* ========================================================================= *)
(* OPENTHEORY ARTICLE READING FOR HOL LIGHT                                  *)
(* Ramana Kumar, Joe Leslie-Hurd and Robert White                            *)
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
    fun (Sequent.Sequent (hs,c)) th ->
    let c' = concl th in
    let th = if c = c' then th else EQ_MP (ALPHA c' c) th in
    List.fold_left alpha_hyp th hs;;

(* ------------------------------------------------------------------------- *)
(* Miscellaneous syntax transformations to convert OpenTheory theorems into  *)
(* native HOL Light theorems.                                                *)
(* ------------------------------------------------------------------------- *)

let the_go_native_conv = ref REFL;;

let go_native_conv tm =
    let th = (!the_go_native_conv) tm in
    let (_,tm') = dest_eq (concl th) in
    if tm' = tm then None else Some th;;

let go_native_term tm =
    match go_native_conv tm with
      None -> (tm,None)
    | Some th -> let (_,tm') = dest_eq (concl th) in (tm', Some th);;

let go_native_term_list =
    let f tm ths =
        let (tm,tho) = go_native_term tm in
        let ths =
            match tho with
              None -> ths
            | Some th -> th :: ths in
        (tm,ths) in
    fun tms -> Object.maps f tms [];;

let (go_native_sequent,go_native_thm) =
    let sequent_convert s =
        let Sequent.Sequent (h,c) = s in
        let (h,aths) = go_native_term_list h in
        let (c,cth) = go_native_term c in
        let cvt = (aths,cth) in
        let seq =
            match cvt with
              ([],None) -> s
            | _ -> Sequent.Sequent (h,c) in
        (seq,cvt) in
    let reverse_convert (aths,cth) =
        let aths = map Object.SYM aths in
        let cth =
            match cth with
              Some th -> Some (Object.SYM th)
            | None -> None in
        (aths,cth) in
    let convert_thm =
        let convert_asm ath th =
            let ath = Object.SYM ath in
            let (asm,_) = dest_eq (concl ath) in
            Object.PROVE_HYP (EQ_MP ath (ASSUME asm)) th in
        let convert_concl cth th =
            match cth with
              Some eq -> EQ_MP eq th
            | None -> th in
        fun (aths,cth) th ->
        convert_concl cth (rev_itlist convert_asm aths th) in
    let go_sequent s =
        let (s,cvt) = sequent_convert s in
        (s, convert_thm (reverse_convert cvt)) in
    let go_thm th =
        let (_,cvt) = sequent_convert (Sequent.from_thm th) in
        convert_thm cvt th in
    (go_sequent,go_thm);;

(* ------------------------------------------------------------------------- *)
(* A type of import contexts.                                                *)
(* ------------------------------------------------------------------------- *)

type context =
  {const_context : Name.t -> string;
   type_op_context : Name.t -> string;
   axiom_context : Sequent.t -> thm};;

let default_context =
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
    let axiom_context s =
        match peek_the_exported_thms s with
          Some (th,_) -> th
        | None -> failwith ("unknown assumption:\n" ^ Sequent.to_string s) in
    {const_context = const_context;
     type_op_context = type_op_context;
     axiom_context = axiom_context};;

(* ------------------------------------------------------------------------- *)
(* A type of import states.                                                  *)
(* ------------------------------------------------------------------------- *)

type state =
  {stack : Object.t list;
   dict : Object.t Int_map.t;
   asms : thm list;
   thms : thm list};;

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
    let obj = Object.Num_object (int_of_string cmd) in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms};;

let process_name state cmd =
    match Name.from_string cmd with
      Some n ->
      let {stack = stack; dict = dict; asms = asms; thms = thms} = state in
      let obj = Object.Name_object n in
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
    let obj = Object.mkAbsTerm objV objB in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("absThm", objB :: objV :: stack) ->
    let obj = Object.mkAbsThm objV objB in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("appTerm", objX :: objF :: stack) ->
    let obj = Object.mkAppTerm objF objX in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("appThm", objX :: objF :: stack) ->
    let obj = Object.mkAppThm objF objX in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("assume", objT :: stack) ->
    let obj = Object.mkAssume objT in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("axiom", objC :: objH :: stack) ->
    let (s,r) = go_native_sequent (Object.dest_sequent (objH,objC)) in
    let th = context.axiom_context s in
    let obj = Object.mk_thm (r th) in
    let stack = obj :: stack in
    let asms = th :: asms in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("betaConv", objT :: stack) ->
    let obj = Object.mkBetaConv objT in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("cons", objT :: objH :: stack) ->
    let obj = Object.mk_cons objH objT in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("const", objN :: stack) ->
    let obj = Object.mkConst (context.const_context) objN in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("constTerm", objT :: objC :: stack) ->
    let obj = Object.mkConstTerm objC objT in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("deductAntisym", objU :: objT :: stack) ->
    let obj = Object.mkDeductAntisym objT objU in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("def", Object.Num_object k :: (obj :: _ as stack)) ->
    let dict = Int_map.add k obj dict in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("defineConst", objT :: objN :: stack) ->
    let (objC,objD) = Object.mkDefineConst (context.const_context) objN objT in
    let stack = objD :: objC :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("defineConstList", objT :: objL :: stack) ->
    let (objC,objD) =
        Object.mkDefineConstList (context.const_context) objL objT in
    let stack = objD :: objC :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("defineTypeOp", objT :: objL :: objR :: objA :: objN :: stack) ->
    let (objT,objA,objR,objRA,objAR) =
        Object.mkDefineTypeOp
          (context.type_op_context) (context.const_context)
          objN objA objR objL objT in
    let stack = objAR :: objRA :: objR :: objA :: objT :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("eqMp", objU :: objT :: stack) ->
    let obj = Object.mkEqMp objT objU in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("hdTl", objL :: stack) ->
    let (objH,objT) = Object.mkHdTl objL in
    let stack = objT :: objH :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("nil", _) ->
    let stack = Object.mk_nil :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("opType", objL :: objT :: stack) ->
    let obj = Object.mkOpType objT objL in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("pop", _ :: stack) ->
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("pragma", _ :: stack) ->
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("proveHyp", objU :: objT :: stack) ->
    let obj = Object.mkProveHyp objT objU in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("ref", Object.Num_object k :: stack) ->
    let obj = Int_map.find k dict in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("refl", objT :: stack) ->
    let obj = Object.mkRefl objT in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("remove", Object.Num_object k :: stack) ->
    let obj = Int_map.find k dict in
    let dict = Int_map.remove k dict in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("subst", objT :: objS :: stack) ->
    let obj = Object.mkSubst objS objT in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("sym", objU :: stack) ->
    let obj = Object.mkSym objU in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("thm", objC :: objH :: objT :: stack) ->
    let s = Object.dest_sequent (objH,objC) in
    let th = go_native_thm (alpha_rule s (Object.dest_thm objT)) in
    let () = export_thm th in
    let thms = th :: thms in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("trans", objU :: objT :: stack) ->
    let obj = Object.mkTrans objT objU in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("typeOp", objN :: stack) ->
    let obj = Object.mkTypeOp (context.type_op_context) objN in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("var", objT :: objN :: stack) ->
    let obj = Object.mkVar objN objT in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("varTerm", objV :: stack) ->
    let obj = Object.mkVarTerm objV in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("varType", objN :: stack) ->
    let obj = Object.mkVarType objN in
    let stack = obj :: stack in
    {stack = stack; dict = dict; asms = asms; thms = thms}
  | ("version", _ :: stack) ->
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
                               Object.list_to_string (state.stack) ^
                               "\n" ^ f) in
            loop (line_number + 1) state
        with End_of_file -> state in
    let {stack = _; dict = _; asms = asms; thms = thms} =
        loop 1 initial_state in
    (rev asms, rev thms);;

end

let import_article filename =
  let h = open_in filename in
  let thy = Import.read_article Import.default_context filename h in
  let _ = close_in h in
  thy;;
