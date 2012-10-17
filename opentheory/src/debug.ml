(* ========================================================================= *)
(* OPENTHEORY DEBUGGING                                                      *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Printing terms.                                                           *)
(* ------------------------------------------------------------------------- *)

let debug_print_term_with pp =
    let rec to_string level tm =
        if is_const tm then
          let (s,ty) = dest_const tm in
          [(level, "CONST \"" ^ s ^ "\" : " ^ string_of_type ty)]
        else if is_var tm then
          let (s,ty) = dest_var tm in
          [(level, "VAR \"" ^ s ^ "\" : " ^ string_of_type ty)]
        else if is_comb tm then
          let (f,x) = dest_comb tm in
          let level' = level + 1 in
          (level, "APP") :: to_string level' f @ to_string level' x
        else if is_abs tm then
          let (v,b) = dest_abs tm in
          let level' = level + 1 in
          (level, "ABS") :: to_string level' v @ to_string level' b
        else
          failwith "debug_term_to_string" in
    let rec print_indent level =
        if level = 0 then () else
        let () = pp " " in
        print_indent (level - 1) in
    let print_line (level,s) =
        let () = print_indent level in
        let () = pp s in
        pp "\n" in
    fun tm ->
        let lines = to_string 0 tm in
        List.iter print_line lines;;

let debug_print_term = debug_print_term_with Format.print_string;;

let debug_print_term_to_file file tm =
    let h = open_out file in
    let () = debug_print_term_with (output_string h) tm in
    let () = close_out h in
    ();;
