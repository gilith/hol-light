(*BEGIN-PARAMETRIC*)
let group_add_comm' = new_axiom
   `!x y z. group_add x (group_add y z) = group_add y (group_add x z)`;;
(*END-PARAMETRIC*)
