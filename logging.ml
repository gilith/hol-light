(* ========================================================================= *)
(* OPENTHEORY PROOF LOGGING FOR HOL LIGHT                                    *)
(* Copyright (c) 2009 Joe Hurd, distributed under the GNU GPL version 2      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Helper functions                                                          *)
(* ------------------------------------------------------------------------- *)

let curry3 f x y z = f (x,y,z);;

let curry4 f w x y z = f (w,x,y,z);;

let uncurry3 f (x,y,z) = f x y z;;

let uncurry4 f (w,x,y,z) = f w x y z;;

(* ------------------------------------------------------------------------- *)
(* Setting up the log files: part 1                                          *)
(* ------------------------------------------------------------------------- *)

type log_state =
     Not_logging
   | Ready_logging
   | Active_logging of out_channel;;

let log_state = ref Not_logging;;

let log_raw s =
    match (!log_state) with
      Active_logging h -> output_string h (s ^ "\n")
    | _ -> ();;

(* ------------------------------------------------------------------------- *)
(* Logging primitive types                                                   *)
(* ------------------------------------------------------------------------- *)

let log_num n = log_raw (string_of_int n);;

let log_name s = log_raw ("\"" ^ String.escaped s ^ "\"");;

let log_command s = log_raw s;;

(* ------------------------------------------------------------------------- *)
(* The dictionary                                                            *)
(* ------------------------------------------------------------------------- *)

let (log_dict_next_key,log_dict_reset_key) =
    let key = ref 0 in
    let next () = let k = !key in (key := k + 1; k) in
    let reset () = key := 0 in
    (next,reset);;

let (log_dict_reset,log_dict_reset_register) =
    let resets = ref [] in
    let register r = resets := r :: !resets in
    let reset_all () = List.iter (fun r -> r ()) (!resets) in
    let reset () = (reset_all (); log_dict_reset_key ()) in
    (reset,register);;

let log_dict_all (f : ('a -> unit) -> 'a -> unit) =
    let hashtbl = Hashtbl.create 10000 in
    let reset () = Hashtbl.clear hashtbl in
    let () = log_dict_reset_register reset in
    let mem x = Hashtbl.mem hashtbl x in
    let peek x = if mem x then Some (Hashtbl.find hashtbl x) else None in
    let save x =
        (let n = log_dict_next_key () in
         Hashtbl.add hashtbl x n;
         log_num n;
         log_command "def") in
    let rec log x =
        match (peek x) with
          Some n ->
          (log_num n;
           log_command "ref")
        | None ->
          (f log x;
           save x) in
    (mem,save,log);;

let log_dict (f : ('a -> unit) -> 'a -> unit) =
    match (log_dict_all f) with
      (_,_,log) -> log;;

(* ------------------------------------------------------------------------- *)
(* Setting up the log files: part 2                                          *)
(* ------------------------------------------------------------------------- *)

let logfile_end () =
    match (!log_state) with
      Active_logging h ->
      (close_out h;
       log_state := Ready_logging)
    | _ -> ();;

let logfile f =
    logfile_end ();
    match (!log_state) with
      Ready_logging ->
      (log_dict_reset ();
       log_state := Active_logging (open_out (f ^ ".art")))
    | _ -> ();;

let is_logging () =
    match (!log_state) with
      Not_logging -> false
    | _ -> true;;

let start_logging () =
    match (!log_state) with
      Not_logging -> log_state := Ready_logging
    | _ -> ();;

let stop_logging () =
    logfile_end ();
    match (!log_state) with
      Ready_logging -> log_state := Not_logging
    | _ -> ();;

(* ------------------------------------------------------------------------- *)
(* Logging complex types                                                     *)
(* ------------------------------------------------------------------------- *)

(***
let log_map (f : 'a -> 'b) (log_b : 'b -> unit) a = log_b (f a);;
***)

let log_nil () = log_command "nil";;

let log_list (f : 'a -> unit) =
    let rec logl l =
        match l with
          [] -> log_nil ()
        | h :: t -> (f h; logl t; log_command "cons") in
    logl;;

let log_unit () = log_nil ();;

let log_sing (f : 'a -> unit) x =
    f x; log_nil (); log_command "cons";;

let log_pair (f : 'a -> unit) (g : 'b -> unit) (x,y) =
    f x; log_sing g y; log_command "cons";;

let log_triple (f : 'a -> unit) (g : 'b -> unit) (h : 'c -> unit) (x,y,z) =
    f x; log_pair g h (y,z); log_command "cons";;

let log_quadruple (f : 'a -> unit) (g : 'b -> unit) (h : 'c -> unit)
      (j : 'd -> unit) (w,x,y,z) =
    f w; log_triple g h j (x,y,z); log_command "cons";;

(***
let log_function n log_arg log_ret func arg =
    if not (is_logging ()) then func arg else
    try
      (log_arg arg;
       log_call n;
       let ret = func arg in
       log_ret ret;
       log_return n;
       ret)
    with Failure err ->
      (log_error ();
       log_return n;
       raise (Failure err));;

let log_function2 n log_arg1 log_arg2 log_ret func =
    curry (log_function n (log_pair log_arg1 log_arg2) log_ret (uncurry func));;

let log_function3 n log_arg1 log_arg2 log_arg3 log_ret func =
    curry3 (log_function n (log_triple log_arg1 log_arg2 log_arg3) log_ret
    (uncurry3 func));;

let log_function4 n log_arg1 log_arg2 log_arg3 log_arg4 log_ret func =
    curry4 (log_function n (log_quadruple log_arg1 log_arg2 log_arg3 log_arg4)
    log_ret (uncurry4 func));;
***)

let (log_type_op_mem,log_type_op_save,log_type_op) =
    let log _ n =
        (log_name n;
         log_command "typeOp") in
    log_dict_all log;;

let log_type_var n = log_name n;;

let log_type =
    let rec log f ty =
        if is_type ty then
          let (n,l) = dest_type ty in
          (log_type_op n; log_list f l; log_command "opType")
        else
          (log_type_var (dest_vartype ty); log_command "varType") in
    log_dict log;;

let (log_const_mem,log_const_save,log_const) =
    let log _ n =
        (log_name n;
         log_command "const") in
    log_dict_all log;;

let log_var v =
    let (n,ty) = dest_var v in
    (log_name n; log_type ty; log_command "var");;

let log_term =
    let rec log f tm =
        if is_const tm then
          let (n,ty) = dest_const tm in
          (log_const n; log_type ty; log_command "constTerm")
        else if is_var tm then
          (log_var tm; log_command "varTerm")
        else if is_comb tm then
          let (a,b) = dest_comb tm in
          (f a; f b; log_command "appTerm")
        else
          let (v,b) = dest_abs tm in
          (log_var v; f b; log_command "absTerm") in
    log_dict log;;

let log_type_inst = log_list (log_pair log_type log_type);;

let log_inst = log_list (log_pair log_term log_term);;

let (log_thm_mem,log_thm_save,log_thm) =
    let log _ th =
        (log_list log_term (hyp th);
         log_term (concl th);
         log_command "axiom") in
    log_dict_all log;;

(* ------------------------------------------------------------------------- *)
(* Logged version of the logical kernel                                      *)
(* ------------------------------------------------------------------------- *)

let REFL tm =
    let th = REFL tm in
    let () =
        if log_thm_mem th then ()
        else (log_term tm;
              log_command "refl";
              log_thm_save th;
              log_command "pop") in
    th;;

let MK_COMB (th1,th2) =
    let th = MK_COMB (th1,th2) in
    let () =
        if log_thm_mem th then ()
        else (log_thm th1;
              log_thm th2;
              log_command "app";
              log_thm_save th;
              log_command "pop") in
    th;;

let ABS tm1 th2 =
    let th = ABS tm1 th2 in
    let () =
        if log_thm_mem th then ()
        else (log_term tm1;
              log_thm th2;
              log_command "abs";
              log_thm_save th;
              log_command "pop") in
    th;;

let BETA tm =
    let th = BETA tm in
    let () =
        if log_thm_mem th then ()
        else (log_term tm;
              log_command "betaConv";
              log_thm_save th;
              log_command "pop") in
    th;;

let ASSUME tm =
    let th = ASSUME tm in
    let () =
        if log_thm_mem th then ()
        else (log_term tm;
              log_command "assume";
              log_thm_save th;
              log_command "pop") in
    th;;

let EQ_MP th1 th2 =
    let th = EQ_MP th1 th2 in
    let () =
        if log_thm_mem th then ()
        else (log_thm th1;
              log_thm th2;
              log_command "eqMp";
              log_thm_save th;
              log_command "pop") in
    th;;

let DEDUCT_ANTISYM_RULE th1 th2 =
    let th = DEDUCT_ANTISYM_RULE th1 th2 in
    let () =
        if log_thm_mem th then ()
        else (log_thm th1;
              log_thm th2;
              log_command "deductAntisym";
              log_thm_save th;
              log_command "pop") in
    th;;

let INST_TYPE i1 th2 =
    let th = INST_TYPE i1 th2 in
    let () =
        if log_thm_mem th then ()
        else (log_type_inst i1;
              log_thm th2;
              log_command "subst";
              log_thm_save th;
              log_command "pop") in
    th;;

let INST i1 th2 =
    let th = INST i1 th2 in
    let () =
        if log_thm_mem th then ()
        else (log_inst i1;
              log_thm th2;
              log_command "subst";
              log_thm_save th;
              log_command "pop") in
    th;;

let new_axiom tm =
    let th = new_axiom tm in
    let () = (log_thm th;
              log_command "pop") in
    th;;

let new_basic_definition tm =
    let th = new_basic_definition tm in
    let (n,tm) = dest_eq (concl th) in
    let (n,_) = dest_const n in
    let () = (log_name n;
              log_term tm;
              log_command "defineConst";
              log_thm_save th;
              log_command "pop";
              log_const_save n;
              log_command "pop") in
    th;;

let new_basic_type_definition ty (abs,rep) th =
    let (ar,ra) = new_basic_type_definition ty (abs,rep) th in
    let (absTm,repTm) = dest_comb (lhs (concl ar)) in
    let (repTm,_) = dest_const (rator repTm) in
    let (absTm,newTy) = dest_const absTm in
    let (_,newTy) = dest_fun newTy in
    let (newTy,tyVars) = dest_type newTy in
    let tyVars = map dest_vartype tyVars in
    let () = (log_name ty;
              log_name abs;
              log_name rep;
              log_list log_type_var tyVars;
              log_thm th;
              log_command "defineTypeOp";
              log_thm_save ra;
              log_command "pop";
              log_thm_save ar;
              log_command "pop";
              log_const_save repTm;
              log_command "pop";
              log_const_save absTm;
              log_command "pop";
              log_type_op_save newTy;
              log_command "pop") in
    (ar,ra);;

let TRANS th1 th2 = log_function2 "TRANS" log_thm log_thm log_thm TRANS;;

(* ------------------------------------------------------------------------- *)
(* Exporting theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

let export_thm th =
    (log_thm th;
     log_list log_term (hyp th);
     log_term (concl th);
     log_command "thm";
     th);;
