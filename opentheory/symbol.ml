(* ========================================================================= *)
(* MAPPING SYMBOLS BETWEEN NAMESPACES                                        *)
(* Ramana Kumar and Joe Hurd                                                 *)
(* ========================================================================= *)

#load "str.cma";;

(* ------------------------------------------------------------------------- *)
(* Parser functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let parse_regexp re line i =
  if not (Str.string_match re line i) then None
  else Some (Str.matched_string line, Str.match_end ());;

let parse_everything parse line =
    match parse line 0 with
      None -> None
    | Some (x,i) -> if i = String.length line then Some x else None;;

(* ------------------------------------------------------------------------- *)
(* Names.                                                                    *)
(* ------------------------------------------------------------------------- *)

module Name =
struct

type t = Name of string list * string;;

let mk_global n = Name ([],n);;

let dest_global (Name (ns,n)) =
    match ns with
      [] -> Some n
    | _ -> None;;

let mk_hol_light n = Name (["HOLLight"],n);;

let dest_hol_light (Name (ns,n)) =
    match ns with
      [s] -> if s = "HOLLight" then Some n else None
    | _ -> None;;

let mk_type_var = mk_global
and dest_type_var = dest_global
and mk_type_op = mk_hol_light
and dest_type_op = dest_hol_light
and mk_const = mk_hol_light
and dest_const = dest_hol_light
and mk_var = mk_global
and dest_var = dest_global;;

let compare =
  let rec compare_comps ns1 ns2 =
      match ns1 with
        [] -> (match ns2 with [] -> 0 | _ :: _ -> -1)
      | n1 :: ns1 ->
        match ns2 with
          [] -> 1
        | n2 :: ns2 ->
          let c = String.compare n1 n2 in
          if c <> 0 then c else
          compare_comps ns1 ns2 in
  fun (Name (ns1,n1)) (Name (ns2,n2)) ->
  let c = compare_comps ns1 ns2 in
  if c <> 0 then c else
  String.compare n1 n2;;

let parse =
  let str_dot = "[.]" in
  let str_quote = "\"" in
  let str_escape = "[\\]\\([.\"\\]\\)" in
  let str_component = "\\([^.\"\\]\\|" ^ str_escape ^ "\\)*" in
  let re_dot = Str.regexp str_dot in
  let re_quote = Str.regexp str_quote in
  let re_escape = Str.regexp str_escape in
  let re_component = Str.regexp str_component in
  fun line ->
  let parse_dot i =
    match parse_regexp re_dot line i with
      None -> None
    | Some (_,i) -> Some ((),i) in
  let parse_quote i =
    match parse_regexp re_quote line i with
      None -> None
    | Some (_,i) -> Some ((),i) in
  let parse_component i =
    match parse_regexp re_component line i with
      None -> None
    | Some (s,i) -> Some (Str.global_replace re_escape "\\1" s, i) in
  let rec parse_unquoted_name i =
    match parse_component i with
      None -> None
    | Some (s,i) ->
        match parse_dot i with
          None -> Some (([],s),i)
        | Some ((),i) ->
            match parse_unquoted_name i with
              None -> None
            | Some ((ns,n),i) -> Some ((s :: ns, n), i) in
  fun i ->
  match parse_quote i with
    None -> None
  | Some ((),i) ->
    match parse_unquoted_name i with
      None -> None
    | Some ((ns,n),i) ->
      match parse_quote i with
        None -> None
      | Some ((),i) -> Some (Name (ns,n), i);;

let from_string = parse_everything parse;;

let to_string =
  let quote = "\"" in
  let dot = "." in
  let escape = "\\" in
  let escapes = ".\"\\" in
  let component_to_string s =
      let rec f acc n =
          let n = n - 1 in
          if n < 0 then acc else
          let c = String.get s n in
          let acc = String.make 1 c :: acc in
          let acc = if String.contains escapes c then escape :: acc else acc in
          f acc n in
      String.concat "" (f [] (String.length s)) in
  fun (Name (ns,n)) ->
  quote ^
  String.concat dot (List.map component_to_string (ns @ [n])) ^
  quote;;

end

module Name_map = Map.Make(Name);;

(* ------------------------------------------------------------------------- *)
(* Interpretations.                                                          *)
(* ------------------------------------------------------------------------- *)

module Interpretation =
struct

type symbol = Const_symbol | Type_op_symbol;;

type translation =
     {to_opentheory : Name.t list Name_map.t;
      from_opentheory : Name.t list Name_map.t};;

type t =
     {const_translation : translation;
      type_op_translation : translation};;

let parse_symbol =
  let str_const = "const" in
  let str_type_op = "type" in
  let re_const = Str.regexp str_const in
  let re_type_op = Str.regexp str_type_op in
  fun line ->
  let parse_const = parse_regexp re_const line in
  let parse_type_op = parse_regexp re_type_op line in
  fun i ->
  match parse_const i with
    Some (_,i) -> Some (Const_symbol,i)
  | None ->
    match parse_type_op i with
      Some (_,i) -> Some (Type_op_symbol,i)
    | None -> None;;

let empty_translation : translation =
    {to_opentheory = Name_map.empty;
     from_opentheory = Name_map.empty};;

let add_translation =
    let add_relation nlm (n1 : Name.t) (n2 : Name.t) =
        let l2 = if Name_map.mem n1 nlm then Name_map.find n1 nlm else [] in
        Name_map.add n1 (l2 @ [n2]) nlm in
    fun {to_opentheory = to_tr; from_opentheory = from_tr} n1 n2 ->
    {to_opentheory = add_relation to_tr n1 n2;
     from_opentheory = add_relation from_tr n2 n1};;

let export_translation {to_opentheory = to_tr; from_opentheory = _} n =
    if Name_map.mem n to_tr then Name_map.find n to_tr else [];;

let import_translation {to_opentheory = _; from_opentheory = from_tr} n =
    if Name_map.mem n from_tr then Name_map.find n from_tr else [];;

let empty : t =
    {const_translation = empty_translation;
     type_op_translation = empty_translation};;

let add_const int n1 n2 =
    let {const_translation = const; type_op_translation = type_op} = int in
    {const_translation = add_translation const n1 n2;
     type_op_translation = type_op};;

let add_type_op int n1 n2 =
    let {const_translation = const; type_op_translation = type_op} = int in
    {const_translation = const;
     type_op_translation = add_translation type_op n1 n2};;

let export_const int =
    let {const_translation = const; type_op_translation = _} = int in
    export_translation const;;

let export_type_op int =
    let {const_translation = _; type_op_translation = type_op} = int in
    export_translation type_op;;

let import_const int =
    let {const_translation = const; type_op_translation = _} = int in
    import_translation const;;

let import_type_op int =
    let {const_translation = _; type_op_translation = type_op} = int in
    import_translation type_op;;

let parse =
  let str_space = " " in
  let str_space_as_space = " as " in
  let re_space = Str.regexp str_space in
  let re_space_as_space = Str.regexp str_space_as_space in
  fun line ->
  let parse_space i =
    match parse_regexp re_space line i with
      None -> None
    | Some (_,i) -> Some ((),i) in
  let parse_space_as_space i =
    match parse_regexp re_space_as_space line i with
      None -> None
    | Some (_,i) -> Some ((),i) in
  fun i ->
  match parse_symbol line i with
    None -> None
  | Some (s,i) ->
    match parse_space i with
      None -> None
    | Some ((),i) ->
      match Name.parse line i with
        None -> None
      | Some (n1,i) ->
        match parse_space_as_space i with
          None -> None
        | Some ((),i) ->
          match Name.parse line i with
            None -> None
          | Some (n2,i) -> Some ((s,n1,n2),i);;

let extend int file =
  let is_comment line =
      (* parser.ml redefines || *)
      Pervasives.(||) (String.length line = 0) (String.get line 0 = '#') in
  let intfile = open_in file in
  let rec read acc =
    try let line = input_line intfile in
        if is_comment line then read acc else
        match parse_everything parse line with
          None -> failwith ("bad line in interpretation file " ^ file ^
                            ":\n" ^ line)
        | Some (s,n1,n2) ->
          let acc =
              match s with
                Const_symbol -> add_const acc n1 n2
              | Type_op_symbol -> add_type_op acc n1 n2 in
          read acc
    with End_of_file -> acc in
  let int = read int in
  let () = close_in intfile in
  int;;

end

let the_interpretation = ref Interpretation.empty;;

let export_const_from_the_interpretation n =
    Interpretation.export_const (!the_interpretation) n;;

let export_type_op_from_the_interpretation n =
    Interpretation.export_type_op (!the_interpretation) n;;

let import_const_from_the_interpretation n =
    Interpretation.import_const (!the_interpretation) n;;

let import_type_op_from_the_interpretation n =
    Interpretation.import_type_op (!the_interpretation) n;;

let extend_the_interpretation file =
    let int = !the_interpretation in
    let int = Interpretation.extend int file in
    the_interpretation := int;;

extend_the_interpretation "opentheory/interpretations/stdlib.int";;
