(* ------------------------------------------------------------------------- *)
(* A general cloud tactic.                                                   *)
(* ------------------------------------------------------------------------- *)

let CLOUD_TAC url =
  let tac (asl,g) =
      let goal_file = Filename.temp_file "goal" ".art" in
      let proof_file = Filename.temp_file "proof" ".art" in
      let () = export_goal goal_file (List.map (concl o snd) asl, g) in
      let cmd =
          "curl --silent --show-error " ^ url ^
          " --form \"article=@" ^ goal_file ^ "\"" ^
          " --output " ^ proof_file in
      let curl = Sys.command cmd in
      let () =
          if curl = 0 then ()
          else failwith ("CLOUD_TAC: curl exit code nonzero: " ^
                         string_of_int curl) in
      let th =
          match import_article proof_file with
            [] -> failwith "CLOUD_TAC: no theorems in resulting article"
          | [th] -> th
          | _ :: _ :: _ ->
            failwith "CLOUD_TAC: multiple theorems in resulting article" in
      ACCEPT_TAC th in
  W tac;;

(* ------------------------------------------------------------------------- *)
(* Known instances of cloud tactics.                                         *)
(* ------------------------------------------------------------------------- *)

let QBF_TAC = CLOUD_TAC "http://cam.xrchz.net/holqbf.cgi"
and SKICO_TAC = CLOUD_TAC "http://cam.xrchz.net/skico.cgi";;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*
let th = prove
  (`?x. !y. ?z. (~x \/ ~y) /\ (~z \/ ~y)`,
   QBF_TAC);;

let th = prove
  (`?x. !y. ?z. (~x \/ ~y) /\ (~z \/ ~y)`,
   SKICO_TAC);;
*)
