(* ========================================================================= *)
(* A TYPE OF SEQUENTS                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

module Sequent =
struct

type t = Sequent of term list * term;;

let compare (Sequent (h1,c1)) (Sequent (h2,c2)) =
    let c = Pervasives.compare c1 c2 in
    if c <> 0 then c else
    Pervasives.compare h1 h2;;

let from_thm th = Sequent (hyp th, concl th);;

let to_string_function =
    ref (fun (Sequent (_,_)) -> "default Sequent.to_string_function");;

let to_string s = (!to_string_function) s;;

end

module Sequent_map = Map.Make(Sequent);;

let add_sequent_map seqs (th,x) =
    Sequent_map.add (Sequent.from_thm th) (th,x) seqs;;

let add_list_sequent_map = List.fold_left add_sequent_map;;

let from_list_sequent_map = add_list_sequent_map Sequent_map.empty;;

let peek_sequent_map seqs seq =
    if not (Sequent_map.mem seq seqs) then None
    else Some (Sequent_map.find seq seqs);;
