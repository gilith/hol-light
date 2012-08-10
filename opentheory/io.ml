let term_to_article h t =
  export_proof h (mk_thm([],mk_icomb(mk_icomb(`K`,`F`),t)));;

exception Term_from_article of term;;

let article_to_term h =
  try
    ignore(Import.read_article
      {import_context with
        Import.axiom_context=fun (_,c) -> raise (Term_from_article c)}
      "article_to_term" h);
    failwith "article produces no theorem"
  with Term_from_article t -> rand t;;
