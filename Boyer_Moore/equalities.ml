(******************************************************************************)
(* FILE          : equalities.ml                                              *)
(* DESCRIPTION   : Using equalities.                                          *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 19th June 1991                                             *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 7th August 1992                                            *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : 2008                                                       *)
(******************************************************************************)

(*----------------------------------------------------------------------------*)
(* is_explicit_value_template : term -> bool                                  *)
(*                                                                            *)
(* Function to compute whether a term is an explicit value template.          *)
(* An explicit value template is a non-variable term composed entirely of     *)
(* T or F or variables or applications of shell constructors.                 *)
(* A `bottom object' corresponds to an application to no arguments. I have    *)
(* also made numeric constants valid components of explicit value templates,  *)
(* since they are equivalent to some number of applications of SUC to 0.      *)
(*----------------------------------------------------------------------------*)

let is_explicit_value_template tm =
   let rec is_explicit_value_template' constructors tm =
      (is_T tm) or (is_F tm) or ((is_const tm) & (type_of tm = `:num`)) or
      (is_var tm) or (is_numeral tm) or
      (let (f,args) = strip_comb tm
       in  (try(mem (fst (dest_const f)) constructors) with Failure _ -> false) &
           (forall (is_explicit_value_template' constructors) args))
   in (not (is_var tm)) &
      (is_explicit_value_template' (all_constructors ()) tm);;

(*----------------------------------------------------------------------------*)
(* subst_conv : thm -> conv                                                   *)
(*                                                                            *)
(* Substitution conversion. Given a theorem |- l = r, it replaces all         *)
(* occurrences of l in the term with r.                                       *)
(*----------------------------------------------------------------------------*)

let subst_conv th tm = SUBST_CONV [(th,lhs (concl th))] tm tm;;

(*----------------------------------------------------------------------------*)
(* use_equality_subst : bool -> bool -> thm -> conv                           *)
(*                                                                            *)
(* Function to perform substitution when using equalities. The first argument *)
(* is a Boolean that controls which side of an equation substitution is to    *)
(* take place on. The second argument is also a Boolean, indicating whether   *)
(* or not we have decided to cross-fertilize. The third argument is a         *)
(* substitution theorem of the form:                                          *)
(*                                                                            *)
(*    t' = s' |- t' = s'                                                      *)
(*                                                                            *)
(* If we are not cross-fertilizing, s' is substituted for t' throughout the   *)
(* term. If we are cross-fertilizing, the behaviour depends on the structure  *)
(* of the term, tm:                                                           *)
(*                                                                            *)
(*    (a) if tm is "l = r", substitute s' for t' in either r or l.            *)
(*    (b) if tm is "~(l = r)", substitute s' for t' throughout tm.            *)
(*    (c) otherwise, do not substitute.                                       *)
(*----------------------------------------------------------------------------*)

(* The heuristic above is modified so that in case (c) a substitution does    *)
(* take place. This reduces the chances of an invalid subgoal (clause) being  *)
(* generated, and has been shown to be a better option for certain examples.  *)

let use_equality_subst right cross_fert th tm =
 try (if cross_fert
  then if (is_eq tm) then
          (if right
           then RAND_CONV (subst_conv th) tm
           else RATOR_CONV (RAND_CONV (subst_conv th)) tm)
       else if ((is_neg tm) & (try(is_eq (rand tm)) with Failure _ -> false)) then subst_conv th tm
       else (* ALL_CONV tm *) subst_conv th tm
  else subst_conv th tm
 ) with Failure _ -> failwith "use_equality_subst";;

(*----------------------------------------------------------------------------*)
(* EQ_EQ_IMP_DISJ_EQ =                                                        *)
(* |- !x x' y y'. (x = x') /\ (y = y') ==> (x \/ y = x' \/ y')                *)
(*----------------------------------------------------------------------------*)

let EQ_EQ_IMP_DISJ_EQ =
 prove
  (`!x x' y y'. (x = x') /\ (y = y') ==> ((x \/ y) = (x' \/ y'))`,
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

(*----------------------------------------------------------------------------*)
(* DISJ_EQ : thm -> thm -> thm                                                *)
(*                                                                            *)
(*     |- x = x'    |- y = y'                                                 *)
(*    ------------------------                                                *)
(*    |- (x \/ y) = (x' \/ y')                                                *)
(*----------------------------------------------------------------------------*)

let DISJ_EQ th1 th2 =
try
 (let (x,x') = dest_eq (concl th1)
  and (y,y') = dest_eq (concl th2)
  in  MP (SPECL [x;x';y;y'] EQ_EQ_IMP_DISJ_EQ) (CONJ th1 th2)
 ) with Failure _ -> failwith "DISJ_EQ";;

(*----------------------------------------------------------------------------*)
(* use_equality_heuristic : (term # bool) -> ((term # bool) list # proof)     *)
(*                                                                            *)
(* Heuristic for using equalities, and in particular for cross-fertilizing.   *)
(* Given a clause, the function looks for a literal of the form ~(s' = t')    *)
(* where t' occurs in another literal and is not an explicit value template.  *)
(* If no such literal is present, the function looks for a literal of the     *)
(* form ~(t' = s') where t' occurs in another literal and is not an explicit  *)
(* value template. If a substitution literal of one of these two forms is     *)
(* found, substitution takes place as follows.                                *)
(*                                                                            *)
(* If the clause is an induction step, and there is an equality literal       *)
(* mentioning t' on the RHS (or LHS if the substitution literal was           *)
(* ~(t' = s')), and s' is not an explicit value, the function performs a      *)
(* cross-fertilization. The substitution function is called for each literal  *)
(* other than the substitution literal. Each call results in a theorem of the *)
(* form:                                                                      *)
(*                                                                            *)
(*    t' = s' |- old_lit = new_lit                                            *)
(*                                                                            *)
(* If the clause is an induction step and s' is not an explicit value, the    *)
(* substitution literal is rewritten to F, and so will subsequently be        *)
(* eliminated. Otherwise this literal is unchanged. The theorems for each     *)
(* literal are recombined using the DISJ_EQ rule, and the new clause is       *)
(* returned. See the comments for the substitution heuristic for a            *)
(* description of how the original clause is proved from the new clause.      *)
(*----------------------------------------------------------------------------*)

let use_equality_heuristic (tm,(ind:bool)) =
try (let checkx (tml1,tml2) t' =
     (not (is_explicit_value_template t')) &
     ((exists (is_subterm t') tml1) or (exists (is_subterm t') tml2))
  in  let rec split_disjuncts side prevl tml =
         if (can (check (checkx (prevl,tl tml)) o side o dest_neg) (hd tml))
         then (prevl,tml)
         else split_disjuncts side ((hd tml)::prevl) (tl tml)
  in  let is_subterm_of_side side subterm tm =
         (try(is_subterm subterm (side tm)) with Failure _ -> false)
  in  let literals = disj_list tm
  in  let (right,(overs,neq'::unders)) =
        try (true,(hashI rev) (split_disjuncts rhs [] literals)) with Failure _ ->
         (false,(hashI rev) (split_disjuncts lhs [] literals))
  in  let side = if right then rhs else lhs
  in  let flipth = if right then ALL_CONV neq' else RAND_CONV SYM_CONV neq'
  in  let neq = rhs (concl flipth)
  in  let eq = dest_neg neq
  in  let (s',t') = dest_eq eq
  in  let delete = ind & (not (is_explicit_value s'))
  in  let cross_fert = delete &
                       ((exists (is_subterm_of_side side t') overs) or
                        (exists (is_subterm_of_side side t') unders))
  in  let sym_eq = mk_eq (t',s')
  in  let sym_neq = mk_neg sym_eq
  in  let ass1 = EQ_MP (SYM flipth) (NOT_EQ_SYM (ASSUME sym_neq))
      and ass2 = ASSUME sym_eq
  in  let subsfun = use_equality_subst right cross_fert ass2
  in  let overths = map subsfun overs
      and neqth =
         if delete
         then TRANS (RAND_CONV (RAND_CONV (subst_conv ass2)) neq)
              (ISPEC s' NOT_EQ_F)
         else ADD_ASSUM sym_eq (REFL neq)
      and underths = map subsfun unders
  in  let neqth' = TRANS flipth neqth
  in  let th1 = itlist DISJ2 overs (try DISJ1 ass1 (list_mk_disj unders) with Failure _ -> ass1)
      and th2 = itlist DISJ_EQ overths (end_itlist DISJ_EQ (neqth'::underths))
      and th3 = SPEC sym_eq EXCLUDED_MIDDLE
  in  let tm' = rhs (concl th2)
  in  let proof th = DISJ_CASES th3 (EQ_MP (SYM th2) th) th1
  in  (proof_print_string_l "-> Use Equality Heuristic" () ; ([(tm',ind)],apply_proof (proof o hd) [tm']))
 ) with Failure _ -> failwith "use_equality_heuristic`";
