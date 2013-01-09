(*BEGIN-PARAMETRIC*)
let group_comm_left_zero = new_axiom
   `!x. group_add group_zero x = group_add x group_zero`;;

let group_comm_right_zero = new_axiom
   `!x. group_add x group_zero = group_add group_zero x`;;

let group_comm_left_add = new_axiom
   `!x y z.
      group_add x z = group_add z x /\
      group_add y z = group_add z y ==>
      group_add (group_add x y) z = group_add z (group_add x y)`;;

let group_comm_right_add = new_axiom
   `!x y z.
      group_add z x = group_add x z /\
      group_add z y = group_add y z ==>
      group_add z (group_add x y) = group_add (group_add x y) z`;;
(*END-PARAMETRIC*)
