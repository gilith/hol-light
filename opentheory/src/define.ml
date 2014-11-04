(* ========================================================================= *)
(* TRACKING DEFINITIONS                                                      *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

type type_op_definition =
     Type_op_definition of (thm * (thm * thm));;

type const_definition =
     Const_definition of thm
   | Const_list_definition of ((((string * term) list * thm) * thm) * int)
   | Abs_type_definition of string
   | Rep_type_definition of string;;

let (peek_type_op_definition,
     add_type_op_definition,
     delete_type_op_definition,
     list_type_op_definition) =
    let the_defs = ref ([] : (string * type_op_definition) list) in
    let mem ty = List.mem_assoc ty (!the_defs) in
    let peek ty = if mem ty then Some (List.assoc ty (!the_defs)) else None in
    let add ty def =
        if mem ty then failwith "redefinition of type op" else
        let () = the_defs := (ty,def) :: !the_defs in
        () in
    let delete tys =
        let pred (ty,_) = not (List.mem ty tys) in
        let () = the_defs := List.filter pred (!the_defs) in
        () in
    let list () = !the_defs in
    (peek,add,delete,list);;

let (peek_const_definition,
     add_const_definition,
     delete_const_definition,
     replace_const_definition,
     list_const_definition) =
    let the_defs = ref ([] : (string * const_definition) list) in
    let mem c = List.mem_assoc c (!the_defs) in
    let peek c = if mem c then Some (List.assoc c (!the_defs)) else None in
    let add c def =
        if mem c then failwith "redefinition of const" else
        let () = the_defs := (c,def) :: !the_defs in
        () in
    let delete cs =
        let pred (c,_) = not (List.mem c cs) in
        let () = the_defs := List.filter pred (!the_defs) in
        () in
    let replace c def =
        if not (mem c) then failwith "no definition of const" else
        let () = delete [c] in
        let () = add c def in
        () in
    let list () = !the_defs in
    (peek,add,delete,replace,list);;

let new_basic_definition tm =
    let th = new_basic_definition tm in
    let (c,_) = dest_eq (concl th) in
    let (c,_) = dest_const c in
    let () = add_const_definition c (Const_definition th) in
    th;;

let new_basic_type_definition ty (abs,rep) exists_th =
    let ar_ra = new_basic_type_definition ty (abs,rep) exists_th in
    let () = add_type_op_definition ty (Type_op_definition (exists_th,ar_ra)) in
    let () = add_const_definition abs (Abs_type_definition ty) in
    let () = add_const_definition rep (Rep_type_definition ty) in
    ar_ra;;
