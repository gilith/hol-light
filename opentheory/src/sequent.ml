(* ========================================================================= *)
(* A TYPE OF SEQUENTS                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

module type Sequent =
sig

type t

val mk : term list * term -> t

val dest : t -> term list * term

val compare : t -> t -> int

val from_thm : thm -> t

val to_string : t -> string

val install_to_string : (t -> string) -> unit

end;;

module Sequent : Sequent =
struct

let unique cmp =
    let rec uniq l =
        match l with
          [] -> l
        | x1 :: l1 ->
          let l2 = uniq l1 in
          match l2 with
            [] -> l
          | x2 :: _ ->
            if cmp x1 x2 = 0 then l2 else
            if l2 == l1 then l else x1 :: l2 in
    uniq;;

let sort_uniq cmp l = unique cmp (List.sort cmp l);;

let lex_compare cmp =
    let rec lex l1 l2 =
        match (l1,l2) with
          ([],[]) -> 0
        | ([],l2) -> -1
        | (l1,[]) -> 1
        | (h1 :: t1, h2 :: t2) ->
          let c = cmp h1 h2 in if c <> 0 then c else lex t1 t2 in
    lex;;

type t = Sequent of term list * term;;

let mk (h,c) = Sequent (sort_uniq alphaorder h, c);;

let dest (Sequent (h,c)) = (h,c);;

let compare (Sequent (h1,c1)) (Sequent (h2,c2)) =
    let c = alphaorder c1 c2 in
    if c <> 0 then c else lex_compare alphaorder h1 h2;;

let from_thm th = Sequent (hyp th, concl th);;

let to_string_function =
    ref (fun (Sequent (_,_)) -> "default Sequent.to_string_function");;

let to_string s = (!to_string_function) s;;

let install_to_string f = to_string_function := f;;

end

module Sequent_map = Map.Make(Sequent);;

let add_sequent_map seqs (th,x) =
    Sequent_map.add (Sequent.from_thm th) (th,x) seqs;;

let add_list_sequent_map = List.fold_left add_sequent_map;;

let from_list_sequent_map = add_list_sequent_map Sequent_map.empty;;

let peek_sequent_map seqs seq =
    if not (Sequent_map.mem seq seqs) then None
    else Some (Sequent_map.find seq seqs);;
