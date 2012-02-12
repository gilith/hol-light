(* ========================================================================= *)
(* CLOUD TACTICS                                                             *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

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
