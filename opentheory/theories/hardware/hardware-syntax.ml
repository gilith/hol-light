(* ========================================================================= *)
(* SYNTAX OPERATIONS FOR THE HARDWARE MODEL                                  *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Cycles are the primitive time steps.                                      *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("cycle",`:num`);;

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

let wire_ty = `:wire`;;

let mk_wire_var n = mk_var (n,wire_ty);;

let dest_wire_var w =
    let (n,ty) = dest_var w in
    if ty = wire_ty then n else
    failwith "dest_wire_var";;

let is_wire_var = can dest_wire_var;;

let mk_ground = `ground`;;

let is_ground =
    let ground_tm = `ground` in
    fun tm -> tm = ground_tm;;

let mk_power = `power`;;

let is_power =
    let power_tm = `power` in
    fun tm -> tm = power_tm;;

let bit_to_wire b = if b then mk_power else mk_ground;;

let mk_bnil = `bnil`;;

let is_bnil =
    let bnil_tm = `bnil` in
    fun tm -> tm = bnil_tm;;

let mk_bwire =
    let bwire_tm = `bwire` in
    fun w -> mk_comb (bwire_tm,w);;

let dest_bwire =
    let bwire_tm = `bwire` in
    fun tm ->
    let (tm,w) = dest_comb tm in
    if tm = bwire_tm then w else failwith "dest_bwire";;

let is_bwire = can dest_bwire;;

let mk_bappend =
    let bappend_tm = `bappend` in
    fun x -> fun y -> mk_comb (mk_comb (bappend_tm,x), y);;

let dest_bappend =
    let bappend_tm = `bappend` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = bappend_tm then (x,y) else failwith "dest_bappend";;

let is_bappend = can dest_bappend;;

let mk_width =
    let width_tm = `width` in
    fun x -> mk_comb (width_tm,x);;

let dest_width =
    let width_tm = `width` in
    fun tm ->
    let (tm,x) = dest_comb tm in
    if tm = width_tm then x else failwith "dest_width";;

let mk_bsub =
    let bsub_tm = `bsub` in
    fun x -> fun k -> fun n -> fun y ->
    mk_comb (mk_comb (mk_comb (mk_comb (bsub_tm,x), k), n), y);;

let dest_bsub =
    let bsub_tm = `bsub` in
    fun tm ->
    let (tm,y) = dest_comb tm in
    let (tm,n) = dest_comb tm in
    let (tm,k) = dest_comb tm in
    let (tm,x) = dest_comb tm in
    if tm = bsub_tm then (x,k,n,y) else failwith "dest_bsub";;

let dest_bground =
    let bground_tm = `bground` in
    fun tm ->
    let (tm,n) = dest_comb tm in
    if tm = bground_tm then n else failwith "dest_bground";;

let is_bground = can dest_bground;;

let dest_bpower =
    let bpower_tm = `bpower` in
    fun tm ->
    let (tm,n) = dest_comb tm in
    if tm = bpower_tm then n else failwith "dest_bpower";;

let is_bpower = can dest_bpower;;

(* ------------------------------------------------------------------------- *)
(* Bus wires.                                                                *)
(* ------------------------------------------------------------------------- *)

type bus_wires = Bus_wires of string * num list;;

let bits_to_bus l =
    let f h t = mk_bappend (mk_bwire (bit_to_wire h)) t in
    itlist f l mk_bnil;;

let mk_bus_wire x i = mk_wire_var (x ^ "[" ^ string_of_num i ^ "]");;

let dest_bus_wire =
    let is_digit = function
      | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> true
      | _ -> false in
    let parse_var s =
        let rec parse_digits n =
            if n < 2 then failwith "eos" else
            let n = n - 1 in
            let c = String.get s n in
            if is_digit c then parse_digits n
            else if c <> '[' then failwith "no '[' char"
            else n in
        let parse_end n =
            if n < 4 then failwith "eos" else
            let n = n - 1 in
            let c = String.get s n in
            if c <> ']' then failwith "not a ']' char" else
            parse_digits n in
        let b = String.length s in
        let a = parse_end b in
        let n = b - (a + 2) in
        if n = 0 then failwith "no digits"
        else if n > 1 && String.get s (a + 1) = '0' then failwith "leading 0"
        else (String.sub s 0 a, num_of_string (String.sub s (a + 1) n)) in
    fun v ->
    parse_var (dest_wire_var v);;

let variable_bus x =
    let rec mk_bus i n =
        if eq_num n num_0 then mk_bnil else
        let w = mk_bus_wire x i in
        let b = mk_bus (i +/ num_1) (n -/ num_1) in
        mk_bappend (mk_bwire w) b in
    mk_bus num_0;;

let dest_variable_bus =
    let rec dest_bus x =
        if is_bnil x then [] else
        let (h,t) = dest_bappend x in
        dest_bwire h :: dest_bus t in
    fun x ->
    let (xs,is) = unzip (map dest_bus_wire (dest_bus x)) in
    match xs with
      [] -> failwith "no bus wires"
    | x :: xs ->
      if exists ((<>) x) xs then failwith "different bus wires" else
      Bus_wires (x,is);;

let range_to_string =
    let single_to_string m = string_of_num m in
    let mono_to_string m n = single_to_string m ^ ":" ^ single_to_string n in
    let rec rising m n xs =
        match xs with
          [] -> mono_to_string m n
        | x :: xs ->
          if x = add_num n num_1 then rising m x xs else
          mono_to_string m n ^ "," ^ single x xs
    and falling m n xs =
        match xs with
          [] -> mono_to_string m n
        | x :: xs ->
          if x = sub_num n num_1 then falling m x xs else
          mono_to_string m n ^ "," ^ single x xs
    and single n xs =
        match xs with
          [] -> single_to_string n
        | x :: xs ->
          if x = add_num n num_1 then rising n x xs else
          if x = sub_num n num_1 then falling n x xs else
          single_to_string n ^ "," ^ single x xs in
    fun xs ->
    match xs with
      [] -> failwith "empty range"
    | x :: xs -> "[" ^ single x xs ^ "]";;

let bus_wires_to_string bw =
    match bw with Bus_wires (x,is) -> x ^ range_to_string is;;

let variable_bus_to_string tm = bus_wires_to_string (dest_variable_bus tm);;

install_user_printer
   ("variable_bus",
    fun fmt -> fun tm -> pp_print_string fmt (variable_bus_to_string tm));;

let genvar_bus =
    let rec mk_bus n =
        if eq_num n num_0 then mk_bnil else
        let w = genvar wire_ty in
        let b = mk_bus (n -/ num_1) in
        mk_bappend (mk_bwire w) b in
    mk_bus;;
