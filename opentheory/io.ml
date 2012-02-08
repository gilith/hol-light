let thm_to_article h th =
  let () = start_logging_to h in
  let () = export_thm(th ()) in
  let () = stop_logging_to () in
  ();;

let term_to_article h t =
  thm_to_article h (fun () -> mk_thm([],mk_icomb(mk_icomb(`K`,`F`),t)));;

exception Term_from_article of term;;

let article_to_term h =
  try
    ignore(read_article_from {axiom=fun _ ([],t) -> raise (Term_from_article t)} h);
    failwith "article produces no theorem"
  with Term_from_article t -> rand t;;
