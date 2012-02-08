let t = article_to_term stdin in thm_to_article stdout (fun () -> SAT_PROVE t);;
