#use "hol.ml";;
needs "opentheory/io.ml";;
needs "prover9make.ml";;
let t = article_to_term stdin in export_proof stdout (prover9 t);;
