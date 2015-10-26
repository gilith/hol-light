(* ========================================================================= *)
(* A TYPE OF THEORIES                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

module Theory =
struct

type t = Theory of string * thm list option * thm list;;

let name th =
    match th with
      Theory (n,_,_) -> n;;

let assumptions th =
    match th with
      Theory (_,a,_) -> a;;

let theorems th =
    match th with
      Theory (_,_,t) -> t;;

let from_current_state n =
    let a = Some (axioms ()) in
    let t = map fst (list_the_exported_thms ()) in
    Theory (n,a,t);;

let to_string th =
    let string_of_list x =
        let s = match x with
                  Some l -> string_of_int (length l)
                | None -> "?" in
        "{" ^ s ^ "}" in
    name th ^ " : " ^
    string_of_list (assumptions th) ^ " |> " ^
    string_of_list (Some (theorems th));;

let pp fmt th =
    let () = Format.pp_open_hbox fmt () in
    let () = Format.pp_print_string fmt (to_string th) in
    let () = Format.pp_close_box fmt () in
    ();;

end

let print_theory = Theory.pp Format.std_formatter;;
#install_printer print_theory;;
