(* ========================================================================= *)
(* A MONTGOMERY MULTIPLICATION CIRCUIT TO OPEN A CRYPTO TIMELOCK             *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The Miller-Rabin primality test.                                          *)
(* ------------------------------------------------------------------------- *)

let random_num =
    let gen m = bit_cons_num (Random.bool ()) m in
    fun n ->
    let w = int_of_num (bit_width_num n) in
    let rec loop () =
        let m = funpow w gen num_0 in
        if le_num m n then m else loop () in
    loop ();;

let rec factor_twos_num n =
    if bit_hd_num n then (0,n) else
    let (r,s) = factor_twos_num (bit_tl_num n) in
    (r + 1, s);;

let modexp_num n a =
    let rec modexp b =
        if eq_num b num_0 then num_1 else
        let r = modexp (bit_tl_num b) in
        let r2 = mod_num (mult_num r r) n in
        if bit_hd_num b then mod_num (mult_num r2 a) n else r2 in
    modexp;;

let miller_rabin t n =
    let rec witness a r =
        if r = 0 then not (eq_num a num_1) else
        let a2 = mod_num (mult_num a a) n in
        if not (eq_num a2 num_1) then witness a2 (r - 1) else
        not (eq_num a num_1) && not (eq_num (add_num a num_1) n) in
    if eq_num n num_2 then true else
    if eq_num n num_1 or not (bit_hd_num n) then false else
    let composite_witness =
        let (r,s) = factor_twos_num (sub_num n num_1) in
        fun a -> witness (modexp_num n a s) r in
    let random_range =
        let m = sub_num n (num_of_int 3) in
        fun () -> add_num (random_num m) num_2 in
    let rec trial i =
        if i = 0 then true else
        let a = random_range () in
        if composite_witness a then false else
        trial (i - 1) in
    trial t;;

let is_prime = miller_rabin 100;;

let rec previous_prime n =
    if is_prime n then n else previous_prime (sub_num n num_2);;

let random_prime w =
    let rec gen () =
        let n = random_odd_num w in
        if is_prime n then n else gen () in
    gen ();;

(* Testing
funpow 100 (fun l -> random_num (num_of_int 1) :: l) [];;
is_prime (num_of_int 3);;
is_prime (num_of_int 5);;
is_prime (dest_numeral `91`);;
is_prime (dest_numeral `257`);;
is_prime (dest_numeral `65537`);;
random_prime 8;;
random_prime 16;;
random_prime 32;;
random_prime 64;;
*)

(* ------------------------------------------------------------------------- *)
(* LCS35 Time Capsule Crypto-Puzzle [1].                                     *)
(*                                                                           *)
(* 1. http://people.csail.mit.edu/rivest/lcs35-puzzle-description.txt        *)
(* ------------------------------------------------------------------------- *)

let timelock_modulus_def = new_definition
  `timelock_modulus =
   6314466083072888893799357126131292332363298818330841375588990772701957128924885547308446055753206513618346628848948088663500368480396588171361987660521897267810162280557475393838308261759713218926668611776954526391570120690939973680089721274464666423319187806830552067951253070082020241246233982410737753705127344494169501180975241890667963858754856319805507273709904397119733614666701543905360152543373982524579313575317653646331989064651402133985265800341991903982192844710212464887459388853582070318084289023209710907032396934919962778995323320184064522476463966355937367009369212758092086293198727008292431243681`;;

let timelock_modulus_num = dest_numeral (rhs (concl timelock_modulus_def));;

let timelock_t_def = new_definition
  `timelock_t = 79685186856218`;;

let timelock_z_def = new_definition
  `timelock_z =
   4273385266812394147070994861525419078076239304748427595531276995752128020213613672254516516003537339494956807602382848752586901990223796385882918398855224985458519974818490745795238804226283637519132355620865854807750610249277739682050363696697850022630763190035330004501577720670871722527280166278354004638073890333421755189887803390706693131249675969620871735333181071167574435841870740398493890811235683625826527602500294010908702312885095784549814408886297505226010693375643169403606313753753943664426620220505295457067077583219793772829893613745614142047193712972117251792879310395477535810302267611143659071382`;;

(* Testing
bit_width_num timelock_modulus_num;;
is_prime timelock_modulus_num;;
*)

(* ------------------------------------------------------------------------- *)
(* A 58-bit prime number to use as a checksum during the calculation.        *)
(* ------------------------------------------------------------------------- *)

let checksum_prime_def = new_definition
  `checksum_prime = 201301130512090183`;;

let checksum_prime_num = dest_numeral (rhs (concl checksum_prime_def));;

(* Testing
bit_width_num checksum_prime_num;;
bit_width_num (mult_num timelock_modulus_num checksum_prime_num);;
mod_num (bit_width_num (mult_num timelock_modulus_num checksum_prime_num)) (num_of_int 8);;
is_prime checksum_prime_num;;
let secret =
    let s = String.sub (string_of_num checksum_prime_num) 4 12 in
    let rec decode ds =
        match ds with
          [] -> []
        | [_] -> failwith "odd number of digits"
        | d1 :: d2 :: ds ->
          let c = Char.chr (int_of_string (d1 ^ d2) + 64) in
          String.make 1 c :: decode ds in
    implode (decode (explode s));;
*)

(* ------------------------------------------------------------------------- *)
(* A 127-bit modulus to use for testing.                                     *)
(* ------------------------------------------------------------------------- *)

let test_prime_one_num = dest_numeral `9990113051209019899`;;

let test_prime_two_num = dest_numeral `9999011305120901971`;;

let test_modulus_num = mult_num test_prime_one_num test_prime_two_num;;

(* Testing
bit_width_num test_prime_one_num;;
bit_width_num test_prime_two_num;;
bit_width_num test_modulus_num;;
bit_width_num (mult_num test_modulus_num checksum_prime_num);;
mod_num (bit_width_num (mult_num test_modulus_num checksum_prime_num)) (num_of_int 8);;
is_prime test_prime_one_num;;
is_prime test_prime_two_num;;
is_prime test_modulus_num;;
*)

(* ------------------------------------------------------------------------- *)
(* Synthesizing a circuit to open the time capsule crypto-puzzle.            *)
(* ------------------------------------------------------------------------- *)

let (synthesize_test_timelock,synthesize_timelock) =
    let mk_n_rw def =
        let conv =
            LAND_CONV (REWR_CONV def) THENC
            RAND_CONV (REWR_CONV checksum_prime_def) THENC
            NUM_REDUCE_CONV in
        let tm =
            list_mk_comb
              (`( * ) : num -> num -> num`,
               [lhs (concl def); `checksum_prime`]) in
        SYM (conv tm) in
    let mk_m_rw d =
        let conv =
            NUM_REDUCE_CONV in
        let tm =
            list_mk_comb
              (`( EXP ) : num -> num -> num`,
               [`10`; mk_numeral (num_of_int d)]) in
        SYM (conv tm) in
    let mk_rws def d =
        let n_rw =
            complain_timed "- Multiplied modulus and checksum"
              mk_n_rw def in
        let m_rw =
            complain_timed "- Computed power of ten"
              mk_m_rw d in
        let rws = [n_rw; m_rw] in
        let n = dest_numeral (lhs (concl n_rw)) in
        let m = dest_numeral (lhs (concl m_rw)) in
        (rws,n,m) in
    let synthesize prefix def d =
        let name = prefix ^ "timelock_" ^ string_of_int d in
        let () = complain ("Synthesizing " ^ name ^ ":") in
        let (rws,n,m) =
            complain_timed "Calculated spec rewrites"
              (mk_rws def) d in
        let ckt = synthesize_montgomery_double_exp rws n m in
        (name,ckt) in
    (synthesize "test_" (REFL (mk_numeral test_modulus_num)),
     synthesize "" timelock_modulus_def);;

(* Testing
disable_proof_logging ();;
let (name,test_timelock_3_ckt) = synthesize_test_timelock 3;;
let (name,timelock_9_ckt) = synthesize_timelock 9;;
*)

(* ------------------------------------------------------------------------- *)
(* Generating Verilog time capsule crypto-puzzle circuits.                   *)
(* ------------------------------------------------------------------------- *)

let (synthesize_test_timelock_verilog_file,
     synthesize_timelock_verilog_file) =
    let mk_comment test d =
        let (reset_cycles,compute_cycles) =
            let r =
                bit_width_num
                  (mult_num
                     (if test then test_modulus_num
                      else timelock_modulus_num)
                     checksum_prime_num) in
            let m = funpow d (mult_num (num_of_int 10)) num_1 in
            let (d0,d1,d2,d3,d4) =
                let d = add_num (quo_num (bit_width_num r) num_2) num_1 in
                (d,d,d,d,d) in
            let l = add_num d3 (add_num d4 num_1) in
            let reset = add_num l num_1 in  (* l + 1 *)
            let compute =  (* l + 1 + (d0 + d1 + d2 + d4 + r + 4) * m *)
                add_num l
                  (mult_num m
                     (add_num (add_num d0 (add_num d1 (add_num d2 d4)))
                        (add_num r (num_of_int 4)))) in
            (reset,compute) in
        let time =
            let cycles = add_num reset_cycles compute_cycles in
            string_of_pretty_duration (float_of_num cycles /. 1e9) in
        let lines =
["where " ^
 (if test then "" else
  let f c = if c = '\n' then "\n  " else String.make 1 c in
  let k = get_margin () in
  let () = set_margin 61 in
  let s = string_of_term (mk_numeral timelock_modulus_num) in
  let () = set_margin k in
  "timelock_modulus =\n  " ^ translate f s ^ "\n\nand ") ^
  string_of_term (concl checksum_prime_def) ^ ".";
 "";
 "How to use the module:";
 "";
 "  1. Hold the ld signal high for at least " ^ string_of_pretty_num reset_cycles ^ " cycles.";
 "     Load the input into the xs and xc buses.";
 "  2. Drop the ld signal low.";
 "  3. Wait " ^ string_of_pretty_num compute_cycles ^ " cycles for the dn signal to go high.";
 "  4. Read the result from the ys and yc buses.";
 "";
 "Assuming the circuit is clocked at 1GHz, the above computation will take";
 "~" ^ time ^ "."] in
        let Verilog_comment footer = default_verilog_comment () in
        Verilog_comment ("\n\n" ^ String.concat "\n" lines ^ footer) in
    let verilog test d =
        let (name,ckt) =
            if test then synthesize_test_timelock d
            else synthesize_timelock d in
        let name = Verilog_module name in
        let comment = mk_comment test d in
        let primary = Verilog_primary (`clk : wire` :: frees_circuit ckt) in
        complain_timed "Generated Verilog module"
          (hardware_to_verilog_file name comment primary) ckt in
    let timed_verilog test d =
        complain_timed "TOTAL" (verilog test) d in
    (timed_verilog true,
     timed_verilog false);;

(* Testing
disable_proof_logging ();;
synthesize_test_timelock_verilog_file 3;;
synthesize_timelock_verilog_file 9;;
*)
