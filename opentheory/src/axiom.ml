(* ========================================================================= *)
(* OPENTHEORY AXIOMS IN HOL LIGHT                                            *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

let normalize_axiom =
    let name =
        let base = Char.code 'a' in
        let rec f n =
            if n = 0 then "" else
            let n = n - 1 in
            f (n / 26) ^ (String.make 1 (Char.chr (base + (n mod 26)))) in
        f in
    let my_find p l =
        (try (Some (List.find p l))
         with Not_found -> None) in
    let rec check tm acc n =
        match (my_find (aconv tm) acc) with
          Some tm -> (tm,acc,n)
        | None -> let (tm,acc,n) = rename tm acc n in (tm, tm :: acc, n)
    and rename tm acc n =
        if is_abs tm then
          let (v,tm) = dest_abs tm in
          let n = n + 1 in
          let w = mk_var (name n, snd (dest_var v)) in
          let tm = vsubst [(w,v)] tm in
          let (tm,acc,n) = check tm acc n in
          (mk_abs (w,tm), acc, n)
        else if is_comb tm then
          let (f,x) = dest_comb tm in
          let (f,acc,n) = check f acc n in
          let (x,acc,n) = check x acc n in
          (mk_comb (f,x), acc, n)
        else
          (tm,acc,n) in
    fun tm ->
        let (tm,_,_) = check tm [] 0 in
        tm;;

let ocaml_print_axiom =
    let thing_ops prefix =
        let pr n = prefix ^ string_of_int n in
        let empty = (-1,[],"") in
        let add x d (k,xs,acc) =
            let k = k + 1 in
            let xs = x :: xs in
            let s = pr k in
            let acc = acc ^ "      let " ^ s ^ " = " ^ d ^ " in\n" in
            (s,(k,xs,acc)) in
        let peek x =
            let rec pk n xs =
                match xs with
                  [] -> None
                | x' :: xs ->
                  if x = x' then Some (pr n) else
                  pk (n - 1) xs in
            fun (k,xs,_) -> pk k xs in
        (empty,add,peek) in
    let type_empty,type_add,type_peek = thing_ops "ty" in
    let term_empty,term_add,term_peek = thing_ops "tm" in
    let rec print_ty ty tys =
        match type_peek ty tys with
          None -> construct_ty ty tys
        | Some s -> (s,tys)
    and construct_ty ty tys =
        if is_fun_ty ty then
          let (f,x) = dest_fun_ty ty in
          let (fs,tys) = print_ty f tys in
          let (xs,tys) = print_ty x tys in
          let d = "mk_fun_ty " ^ fs ^ " " ^ xs in
          type_add ty d tys
        else if is_vartype ty then
          let s = dest_vartype ty in
          let d = "mk_vartype \"" ^ s ^ "\"" in
          type_add ty d tys
        else
          let (s,l) = dest_type ty in
          let () =
              (match l with
                 [] -> ()
               | _ -> failwith "non-nullary type operator") in
          let d = "mk_type (\"" ^ s ^ "\",[])" in
          type_add ty d tys in
    let rec print_tm tm tms tys =
        match term_peek tm tms with
          None -> construct_tm tm tms tys
        | Some s -> (s,tms,tys)
    and construct_tm tm tms tys =
        if is_abs tm then
          let (v,b) = dest_abs tm in
          let (vs,tms,tys) = print_tm v tms tys in
          let (bs,tms,tys) = print_tm b tms tys in
          let d = "mk_abs (" ^ vs ^ "," ^ bs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,tys)
        else if is_eq tm then
          let (f,x) = dest_eq tm in
          let (fs,tms,tys) = print_tm f tms tys in
          let (xs,tms,tys) = print_tm x tms tys in
          let d = "mk_eq (" ^ fs ^ "," ^ xs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,tys)
        else if is_comb tm then
          let (f,x) = dest_comb tm in
          let (fs,tms,tys) = print_tm f tms tys in
          let (xs,tms,tys) = print_tm x tms tys in
          let d = "mk_comb (" ^ fs ^ "," ^ xs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,tys)
        else if is_var tm then
          let (n,t) = dest_var tm in
          let (ts,tys) = print_ty t tys in
          let d = "mk_var (\"" ^ n ^ "\"," ^ ts ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,tys)
        else if tm = `(@):(A->bool)->A` then
          let d = "mk_const (\"@\",[])" in
          let (s,tms) = term_add tm d tms in
          (s,tms,tys)
        else
          failwith "unknown constant" in
    fun tm ->
      let (s,(_,_,tms),(_,_,tys)) = print_tm tm term_empty type_empty in
      let () = print (tys ^ tms ^ "      " ^ s ^ "\n") in
      ();;

let opentheory_print_axiom =
    let thing_ops prefix =
        let pr n = prefix ^ string_of_int n in
        let empty = (-1,[],"") in
        let add x d (k,xs,acc) =
            let k = k + 1 in
            let xs = x :: xs in
            let s = pr k in
            let acc = acc ^ "      val " ^ s ^ " = " ^ d ^ "\n" in
            (s,(k,xs,acc)) in
        let peek x =
            let rec pk n xs =
                match xs with
                  [] -> None
                | x' :: xs ->
                  if x = x' then Some (pr n) else
                  pk (n - 1) xs in
            fun (k,xs,_) -> pk k xs in
        (empty,add,peek) in
    let type_empty,type_add,type_peek = thing_ops "ty" in
    let var_empty,var_add,var_peek = thing_ops "v" in
    let term_empty,term_add,term_peek = thing_ops "tm" in
    let rec print_ty ty tys =
        match type_peek ty tys with
          None -> construct_ty ty tys
        | Some s -> (s,tys)
    and construct_ty ty tys =
        if is_fun_ty ty then
          let (f,x) = dest_fun_ty ty in
          let (fs,tys) = print_ty f tys in
          let (xs,tys) = print_ty x tys in
          let d = "Type.mkFun (" ^ fs ^ "," ^ xs ^ ")" in
          type_add ty d tys
        else if is_vartype ty then
          let s = dest_vartype ty in
          let d = "Type.mkVar (Name.mkGlobal \"" ^ s ^ "\")" in
          type_add ty d tys
        else if ty = bool_ty then
          let d = "Type.bool" in
          type_add ty d tys
        else if ty = `:ind` then
          let d = "Type.ind" in
          type_add ty d tys
        else
          failwith "unknown type operator" in
    let rec print_var v vars tys =
        match var_peek v vars with
          None -> construct_var v vars tys
        | Some s -> (s,vars,tys)
    and construct_var v vars tys =
        let (n,t) = dest_var v in
        let (ts,tys) = print_ty t tys in
        let d = "Var.mk (Name.mkGlobal \"" ^ n ^ "\", " ^ ts ^ ")" in
        let (s,vars) = var_add v d vars in
        (s,vars,tys) in
    let rec print_tm tm tms vars tys =
        match term_peek tm tms with
          None -> construct_tm tm tms vars tys
        | Some s -> (s,tms,vars,tys)
    and construct_tm tm tms vars tys =
        if is_abs tm then
          let (v,b) = dest_abs tm in
          let (vs,vars,tys) = print_var v vars tys in
          let (bs,tms,vars,tys) = print_tm b tms vars tys in
          let d = "mkAbs (" ^ vs ^ "," ^ bs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,vars,tys)
        else if is_eq tm then
          let (f,x) = dest_eq tm in
          let (fs,tms,vars,tys) = print_tm f tms vars tys in
          let (xs,tms,vars,tys) = print_tm x tms vars tys in
          let d = "mkEq (" ^ fs ^ "," ^ xs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,vars,tys)
        else if is_comb tm then
          let (f,x) = dest_comb tm in
          let (fs,tms,vars,tys) = print_tm f tms vars tys in
          let (xs,tms,vars,tys) = print_tm x tms vars tys in
          let d = "mkApp (" ^ fs ^ "," ^ xs ^ ")" in
          let (s,tms) = term_add tm d tms in
          (s,tms,vars,tys)
        else if is_var tm then
          let (vs,vars,tys) = print_var tm vars tys in
          let d = "mkVar " ^ vs in
          let (s,tms) = term_add tm d tms in
          (s,tms,vars,tys)
        else
          let (n,t) = dest_const tm in
          if n <> "@" then failwith "unknown constant" else
          let (_,t) = dest_fun_ty t in
          let (ts,tys) = print_ty t tys in
          let d = "mkSelect " ^ ts in
          let (s,tms) = term_add tm d tms in
          (s,tms,vars,tys) in
    fun tm ->
      let (s,(_,_,tms),(_,_,vars),(_,_,tys)) =
          print_tm tm term_empty var_empty type_empty in
      let () = print ("    let\n" ^ tys ^ vars ^ tms ^ "    in\n" ^
                      "      " ^ s ^ "\n" ^ "    end\n") in
      ();;
