exception Tm of term
let t = try
  let ctxt = {import_context with Import.axiom_context=fun (_,c) -> raise (Tm c)} in
  let _ = Import.read_article ctxt "stdin" stdin in
  failwith "no theorem"
  with Tm t -> rand t in
let () = export_proof stdout (PROVER9 t) in
()
