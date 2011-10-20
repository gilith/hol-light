exception Tm of term
let t = try
  let _ = read_article_from {axiom=fun _ (_,c) -> raise (Tm c)} stdin in
  failwith "no theorem"
  with Tm t -> t in
let () = start_logging_to stdout in
let th = PROVER9 t in
let () = export_thm th in
let () = stop_logging_to () in
()
