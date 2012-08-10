#use "hol.ml";;
needs "opentheory/io.ml";;
needs "minisatmake.ml";;
let t = article_to_term stdin in export_proof stdout (sat_prove t);;
