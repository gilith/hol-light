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
(* A general interface for making tactics available to the cloud.            *)
(* ------------------------------------------------------------------------- *)

let CLOUDIFY_TAC tac goal_file =
  let (hs,c) =
      match import_article goal_file with
        [] -> failwith "CLOUDIFY_TAC: no theorems in goal article"
      | [th] -> (hyp th, concl th)
      | _ :: _ :: _ ->
        failwith "CLOUDIFY_TAC: multiple theorems in goal article" in
  let goal = List.fold_right (curry mk_imp) hs c in
  let th = prove (goal, tac THEN CHEAT_TAC) in
  let th = funpow (List.length hs) UNDISCH th in
  export_proof stdout th;;

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
