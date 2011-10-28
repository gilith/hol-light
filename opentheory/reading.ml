(* ========================================================================= *)
(* OPENTHEORY ARTICLE READING FOR HOL LIGHT                                  *)
(* Ramana Kumar                                                              *)
(* ========================================================================= *)

(* for the moment, we only read term-forming commands and axiom proofs *)

needs "basics.ml";;
needs "equal.ml";;

module Intmap = Map.Make(struct type t = int let compare = compare end);;

type state =
  { stack:opentheory_object list
  ; thms:thm list
  ; dict:opentheory_object Intmap.t
  }

type reader =
  { axiom:thm list -> term list * term -> thm
  }

let unwrap_term_list =
  List.map (function Term_object t -> t | _ -> failwith "unwrap_term_list")
let unwrap_type_list =
  List.map (function Type_object t -> t | _ -> failwith "unwrap_type_list")

let is_digit = function
  | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> true
  | _ -> false

let read_article_from {axiom=axiom} h =
  let step = function
    | ("absTerm",({stack=Term_object b::Var_object v::os} as st))
      -> {st with stack=Term_object(mk_abs(v,b))::os}
    | ("appTerm",({stack=Term_object x::Term_object f::os} as st))
      -> {st with stack=Term_object(mk_comb(f,x))::os}
    | ("axiom",({stack=Term_object t::List_object ts::os; thms=thms} as st))
      -> {st with stack=Thm_object (axiom thms (unwrap_term_list ts,t))::os}
    | ("cons",({stack=List_object t::h::os} as st))
      -> {st with stack=List_object (h::t)::os}
    | ("const",({stack=Name_object n::os} as st))
      -> {st with stack=Const_object n::os}
    | ("constTerm",({stack=Type_object ty::Const_object c::os} as st))
      -> {st with stack=Term_object(mk_mconst(c,ty))::os}
    | ("def",({stack=Num_object k::x::os;dict=dict} as st))
      -> {st with stack=x::os;dict=Intmap.add k x dict}
    | ("nil",({stack=os} as st))
      -> {st with stack=List_object []::os}
    | ("opType",({stack=List_object ts::Type_op_object t::os} as st))
      -> {st with stack=Type_object (mk_type (t, unwrap_type_list ts))::os}
    | ("pop",({stack=_::os} as st))
      -> {st with stack=os}
    | ("ref",({stack=Num_object k::os;dict=dict} as st))
      -> {st with stack=Intmap.find k dict::os}
    | ("remove",({stack=Num_object k::os;dict=dict} as st))
      -> {st with stack=Intmap.find k dict::os;dict=Intmap.remove k dict}
    | ("thm",({stack=Term_object c::List_object hs::Thm_object th::os;thms=thms} as st))
      -> let th = EQ_MP (ALPHA (concl th) c) th in
         let ft th = function
          | Term_object h ->
              let c  = concl th in
              let th = DISCH h th in
              let c' = concl th in
              if aconv c c' then
                ADD_ASSUM h th
              else
                UNDISCH (EQ_MP (LAND_CONV (C ALPHA h) c') th)
          | _ -> failwith "thm: not a list of terms" in
         let th = List.fold_left ft th hs in
      {st with stack=os;thms=th::thms}
    | ("typeOp",({stack=Name_object n::os} as st))
      -> {st with stack=Type_op_object n::os}
    | ("var",({stack=Type_object t::Name_object n::os} as st))
      -> {st with stack=Var_object(mk_var(n,t))::os}
    | ("varTerm",({stack=Var_object t::os} as st))
      -> {st with stack=Term_object t::os}
    | ("varType",({stack=Name_object n::os} as st))
      -> {st with stack=Type_object(mk_vartype n)::os}
    | (s,({stack=os} as st)) ->
      let c = s.[0] in
      if c = '"' then
        {st with stack=Name_object(String.sub s 1 (String.length s - 2))::os}
      else if c = '#' then
        st
      else if is_digit c then
        {st with stack=Num_object(int_of_string s)::os}
      else failwith ("unhandled article line: "^s)
    in
  let rec loop st = try loop (step (input_line h,st)) with End_of_file -> st in
  (loop {stack=[];dict=Intmap.empty;thms=[]}).thms;;
