(*BEGIN-PARAMETRIC*)
let ring_add_comm' = new_axiom
   `!x y z. ring_add x (ring_add y z) = ring_add y (ring_add x z)`;;
(*END-PARAMETRIC*)
