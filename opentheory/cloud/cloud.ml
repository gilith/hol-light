(* ========================================================================= *)
(* CLOUD TACTICS                                                             *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

#load "unix.cma";;

(* ------------------------------------------------------------------------- *)
(* The interpretation for the cloud tactics.                                 *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/cloud/cloud.int";;

(* ------------------------------------------------------------------------- *)
(* A general interface for calling cloud tactics.                            *)
(* ------------------------------------------------------------------------- *)

let CLOUD_TAC url =
  let tac (asl,g) =
      let goal_file = Filename.temp_file "goal" ".art" in
      let proof_file = Filename.temp_file "proof" ".art" in
      let asl = List.map (concl o snd) asl in
      let () = export_goal goal_file (asl,g) in
      let cmd =
          "curl --silent --show-error " ^ url ^
          " --form \"article=@" ^ goal_file ^ "\"" ^
          " --output " ^ proof_file in
      try let curl = Sys.command cmd in
          let () =
              if curl = 0 then ()
              else failwith ("CLOUD_TAC: curl exit code nonzero: " ^
                             string_of_int curl) in
          let (asms,thms) = import_article proof_file in
          let th =
              match thms with
                [] -> failwith "CLOUD_TAC: no theorems in resulting article"
              | [th] -> th
              | _ :: _ :: _ ->
                failwith "CLOUD_TAC: multiple theorems in resulting article" in
          let (th,(asl',g')) =
              match th with
                Some x -> x
              | None -> failwith "CLOUD_TAC: proof of unknown goal" in
          let () =
              if g' = g then ()
              else failwith ("CLOUD_TAC: proved different goal:\nasked for " ^
                             string_of_term g ^ "\n received " ^
                             string_of_term g') in
          let () =
              if asl' = asl then ()
              else failwith "CLOUD_TAC: proof of different assumptions" in
          match th with
            Some th -> ACCEPT_TAC th
          | None -> failwith "CLOUD_TAC: subgoals not implemented"
      with Failure f ->
           failwith ("in CLOUD_TAC running command:\n" ^ cmd ^ "\n" ^ f) in
  W tac;;

(* ------------------------------------------------------------------------- *)
(* Known instances of cloud tactics.                                         *)
(* ------------------------------------------------------------------------- *)

let QBF_TAC = CLOUD_TAC "http://cam.xrchz.net/holqbf.cgi"
and SKICO_TAC = CLOUD_TAC "http://cam.xrchz.net/skico.cgi";;

(* ------------------------------------------------------------------------- *)
(* A general interface for making tactics available to the cloud.            *)
(* ------------------------------------------------------------------------- *)

let CLOUDIFY_TAC tac goal_file =
  let (asms,thms) = import_article goal_file in
  let th =
      match thms with
        [] -> failwith "CLOUDIFY_TAC: no theorems in goal article"
      | [th] -> th
      | _ :: _ :: _ ->
        failwith "CLOUDIFY_TAC: multiple theorems in goal article" in
  let (hs,c) =
      match th with
        Some (_,x) -> x
      | None -> failwith "CLOUDIFY_TAC: unknown goal" in
  let goal = List.fold_right (curry mk_imp) hs c in
  let th = prove (goal, tac THEN CHEAT_TAC) in
  let th = funpow (List.length hs) UNDISCH th in
  export_proof stdout th;;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*
let th = prove
  (`?x. x`,
   QBF_TAC);;

let th = prove
  (`?x. !y. ?z. (~x \/ ~y) /\ (~z \/ ~y)`,
   QBF_TAC);;

let th = prove
  (`!y. (?x. x /\ y) \/ (!x. y ==> x)`,
   QBF_TAC);;

let th = prove
  (`?x. !y. ?z. (~x \/ ~y) /\ (~z \/ ~y)`,
   SKICO_TAC);;
*)

let meson_main () =
  let goal_file = Sys.getenv "OPENTHEORY_GOAL" in
  CLOUDIFY_TAC (MESON_TAC []) goal_file;;

(* ------------------------------------------------------------------------- *)
(* An interface for calling cloud conversions.                               *)
(* ------------------------------------------------------------------------- *)

let CLOUD_CONV url ths =
    let context =
        let seqs = from_list_sequent_map ths in
        let {Import.const_context = const_context;
             Import.type_op_context = type_op_context;
             Import.axiom_context = axiom_context} = import_context in
        let axiom_context (hs,c) =
            match peek_sequent_map seqs (Sequent.Sequent (hs,c)) with
              Some th -> Some th
            | None ->
              match axiom_context (hs,c) with
                Some th -> Some th
              | None ->
                failwith ("CLOUD_CONV: unsatisfied assumption:\n" ^
                          string_of_thm (mk_thm (hs,c))) in
        {Import.const_context = const_context;
         Import.type_op_context = type_op_context;
         Import.axiom_context = axiom_context} in
    fun tm ->
    let goal_file = Filename.temp_file "goal" ".art" in
    let proof_file = Filename.temp_file "proof" ".art" in
    let goal = mk_icomb (mk_icomb (`K : A -> B -> A`,`F`), tm) in
    let t0 = Unix.gettimeofday () in
    let () = export_goal goal_file ([],goal) in
    let t1 = Unix.gettimeofday () in
    let goal_time = t1 -. t0 in
    let goal_size = (Unix.stat goal_file).Unix.st_size in
    let cmd =
        "curl --silent --show-error " ^ url ^
        " --form \"article=@" ^ goal_file ^ "\"" ^
        " --output " ^ proof_file in
    try let curl = Sys.command cmd in
        let t2 = Unix.gettimeofday () in
        let curl_time = t2 -. t1 in
        let () =
            if curl = 0 then ()
            else failwith ("CLOUD_CONV: curl exit code nonzero: " ^
                           string_of_int curl) in
        let (asms,thms) = Import.read_article context proof_file in
        let t3 = Unix.gettimeofday () in
        let proof_time = t3 -. t2 in
        let proof_size = (Unix.stat proof_file).Unix.st_size in
        let () =
            let size_to_string n = string_of_int n in
            let time_to_string t = string_of_int (truncate (1000.0 *. t)) in
            let total_time = goal_time +. curl_time +. proof_time in
            report (" & " ^
                    size_to_string goal_size ^ " & " ^
                    time_to_string goal_time ^ " & " ^
                    time_to_string curl_time ^ " & " ^
                    size_to_string proof_size ^ " & " ^
                    time_to_string proof_time ^ " & " ^
                    time_to_string total_time ^ " \\\\") in
        let th =
            match thms with
              [] -> failwith "CLOUD_CONV: no theorems in resulting article"
            | [th] -> th
            | _ :: _ :: _ ->
              failwith "CLOUD_CONV: multiple theorems in resulting article" in
        let (th,_) =
            match th with
              Some x -> x
            | None -> failwith "CLOUD_CONV: proof of unknown goal" in
        match th with
          None -> failwith "CLOUD_CONV: subgoals not implemented"
        | Some th -> th
    with Failure f ->
         failwith ("in CLOUD_CONV running command:\n" ^ cmd ^ "\n" ^ f);;

(* ------------------------------------------------------------------------- *)
(* Known instances of cloud conversions.                                     *)
(* ------------------------------------------------------------------------- *)

(* A QBF tactic *)

let QBF_CONV =
    CLOUD_CONV "http://cam.xrchz.net/holqbf.cgi"
    [prove (`(!) = (\P. P = (\ (x:A). T))`, ACCEPT_TAC FORALL_DEF);
     prove (`!b1 b2. b1 /\ b2 <=> b1 /\ b2`, REWRITE_TAC []);
     prove (`!A B C. A \/ B \/ C <=> (A \/ B) \/ C`, ACCEPT_TAC DISJ_ASSOC);
     prove (`!A B. A \/ B <=> B \/ A`, ACCEPT_TAC DISJ_SYM);
     prove (`(?) = (\P. !q. (!(x:A). P x ==> q) ==> q)`, ACCEPT_TAC EXISTS_DEF);
     prove (`(~) = (\t. t ==> F)`, ACCEPT_TAC NOT_DEF);
     TAUT `(~A ==> F) ==> (A ==> F) ==> F`;
     TAUT `~(A \/ B) ==> F <=> (A ==> F) ==> ~B ==> F`;
     TAUT `!A. A ==> ~A ==> F`;
     TAUT `(p <=> ~q) <=> (p \/ q) /\ (~q \/ ~p)`;
     TAUT `~(p ==> q) ==> p`;
     TAUT `~(p ==> q) ==> ~q`;
     TAUT `~(~A \/ B) ==> F <=> A ==> ~B ==> F`;
     TAUT `(p <=> q <=> r) <=>
           (p \/ q \/ r) /\ (p \/ ~r \/ ~q) /\
           (q \/ ~r \/ ~p) /\ (r \/ ~q \/ ~p)`;
     TAUT `!t. ((T <=> t) <=> t) /\ ((t <=> T) <=> t) /\
               ((F <=> t) <=> ~t) /\ ((t <=> F) <=> ~t)`;
     TAUT `(p <=> q \/ r) <=> (p \/ ~q) /\ (p \/ ~r) /\ (q \/ r \/ ~p)`;
     TAUT `(p <=> q /\ r) <=> (p \/ ~q \/ ~r) /\ (q \/ ~p) /\ (r \/ ~p)`;
     TAUT `!x. x \/ ~x`;
     TAUT `!t1 t2 t3. t1 /\ t2 /\ t3 <=> (t1 /\ t2) /\ t3`;
     TAUT `!P Q. (?(x:A). P /\ Q x) <=> P /\ (?x. Q x)`;
     prove (`!P Q. (!(x:A). P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)`,
            ACCEPT_TAC FORALL_AND_THM);
     prove (`F <=> (!x. x)`, ACCEPT_TAC F_DEF);
     TAUT `!t1 t2. (t1 ==> t2) ==> (t2 ==> t1) ==> (t1 <=> t2)`;
     TAUT `~(t /\ ~t)`;
     TAUT `!t. F ==> t`;
     TAUT `!t. (T ==> t <=> t) /\ (t ==> T <=> T) /\ (F ==> t <=> T) /\
               (t ==> t <=> T) /\ (t ==> F <=> ~t)`;
     prove (`(\/) = (\t1 t2. !t. (t1 ==> t) ==> (t2 ==> t) ==> t)`,
            ACCEPT_TAC OR_DEF)];;

(* QBF_CONV `!x y z. (x \/ y) /\ (x \/ z)`;; Broken *)
QBF_CONV `x \/ ~x`;;
QBF_CONV `x /\ ~x`;;
(* QBF_CONV `(x /\ x) \/ !y. x ==> y`;; Broken *)
QBF_CONV `!x. x \/ ~x`;;
QBF_CONV `?p. (!q. (p \/ ~q)) /\ !q:bool. ?r. r`;;
QBF_CONV `?x. !y. ?z. (~x \/ ~y) /\ (~z \/ ~y)`;;

(* A SKICO conversion *)

let SKICO_CONV =
    CLOUD_CONV "http://cam.xrchz.net/skico.cgi"
    [prove (`(!) = (\P. P = (\ (x:A). T))`, ACCEPT_TAC FORALL_DEF);
     TAUT `!t1 t2. (t1 ==> t2) ==> (t2 ==> t1) ==> (t1 <=> t2)`;
     prove (`!(x:A). x = x <=> T`, REWRITE_TAC []);
     prove (`!(f : C -> B) (g : A -> C). f o g = (\x. f (g x))`,
            MATCH_ACCEPT_TAC o_DEF);
     prove (`(K : A -> B -> A) = (\x v. x)`, ACCEPT_TAC K_DEF)];;

SKICO_CONV `!x. x \/ ~x`;;
SKICO_CONV `?p. (!q. (p \/ ~q)) /\ !q:bool. ?r. r`;;
SKICO_CONV `?x. !y. ?z. (~x \/ ~y) /\ (~z \/ ~y)`;;

(* A Norrish numeral conversion *)

let BIT2 = new_definition
  `!n. BIT2 n = SUC (SUC (n + n))`;;

let NORRISH_CONV =
    CLOUD_CONV "http://cam.xrchz.net/n2b.cgi"
    [prove (`(!) = (\P. P = (\ (x:A). T))`, ACCEPT_TAC FORALL_DEF);
     prove (`!n. SUC (BIT0 n) = BIT1 n`, ACCEPT_TAC (GSYM BIT1_DEF));
     prove (`!n. SUC (BIT1 n) = BIT0 (SUC n)`, REWRITE_TAC [ARITH_SUC]);
     prove (`SUC _0 = BIT1 _0`, REWRITE_TAC [ARITH_SUC]);
     prove (`!n. BIT2 n = SUC (BIT1 n)`, REWRITE_TAC [BIT1; BIT2])];;

RAND_CONV NORRISH_CONV `NUMERAL _0`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT1 _0)`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT2 _0)`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT1 (BIT1 _0))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT2 (BIT1 _0))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT1 (BIT2 _0))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT2 (BIT2 _0))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT1 (BIT1 (BIT1 _0)))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT2 (BIT1 (BIT1 _0)))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT1 (BIT2 (BIT1 _0)))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT2 (BIT2 (BIT1 _0)))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT1 (BIT1 (BIT2 _0)))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT2 (BIT1 (BIT2 _0)))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT1 (BIT2 (BIT2 _0)))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT2 (BIT2 (BIT2 _0)))`;;
RAND_CONV NORRISH_CONV `NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 _0))))`;;
