(* COMPLETE TODO *)

(***********************************************************************
 * Proofs of Refinement Rules for Pancake Statements                   *
 ***********************************************************************)

Theory panRefinement
Ancestors pred_set panPredicate panSem panWeakestPrecondition

(* Helper-tactic for multiple calls of Cases_on followed by gvs[], *)
(* i.e. when eliminating non-trivial but contradictory cases       *)
fun elim_cases []      = all_tac
  | elim_cases (x::xs) = (Cases_on x >> gvs[] >> elim_cases xs);


(***************************************************************
 * 1. Rewritten Versions of State Predicates                   *
 ***************************************************************)

Definition with_eval_def:
  with_eval P e = P ∩ pred_eval e
End

Definition with_compl_def:
  with_compl P e = P ∩ pred_compl e
End


(***************************************************************
 * 2. Definitions and Theorems about Contracts and Refinements *
 ***************************************************************)

Datatype:
  Contract = HoareC (('a, 'ffi) state -> bool) (('a, 'ffi) state -> bool) ('a result option)
           | SeqC   Contract Contract
           | IfC    ('a panLang$exp) Contract Contract
           | WhileC ('a panLang$exp) Contract
           | PanC   ('a panLang$prog)
           | DCC
End

Definition sat_def:
  sat contr prog = case (contr, prog) of
                   | ((HoareC P Q res), prog)      => hoare P prog Q res
                   | ((SeqC c1 c2), (Seq p1 p2))   => sat c1 p1 ∧ sat c2 p2
                   | ((IfC l c1 c2), (If r p1 p2)) => l = r ∧ sat c1 p1 ∧ sat c2 p2
                   | ((WhileC l c), (While r p))   => l = r ∧ sat c p
                   | ((PanC l), r)                 => l = r
                   | (DCC, _)                      => T
                   | _                             => F
End

Definition refine_def:
  refine c1 c2 ⇔ ∀prog. sat c2 prog ⇒ sat c1 prog
End

Theorem refine_reflexive:
  ∀A. refine A A
Proof
  rw[refine_def]
QED

Theorem refine_transitive:
  ∀A B C. refine A B ∧ refine B C ⇒ refine A C
Proof
  rw[refine_def]
QED


(***************************************************************
 * 3. Refinement Rules for Pancake                             *
 ***************************************************************)

Theorem strengthen_postcondition_refinement_rule:
  Q' ⊆ Q ⇒ refine (HoareC P Q res) (HoareC P Q' res)
Proof
  rw[refine_def,sat_def,hoare_def]
  >> first_x_assum $ (drule_then assume_tac)
  >> pairarg_tac
  >> gvs[]
  >> ASM_SET_TAC[]
QED

Theorem weaken_precondition_refinement_rule:
  P ⊆ P' ⇒ refine (HoareC P Q res) (HoareC P' Q res)
Proof
  rw[refine_def,sat_def,hoare_def]
  >> ‘s ∈ P'’ by (ASM_SET_TAC[])
  >> gvs[]
QED

Theorem skip_refinement_rule_pan:
  P ⊆ Q ⇒ refine (HoareC P Q NONE) (PanC Skip)
Proof
  rw[refine_def,sat_def]
  >> ‘P ⊆ wp Skip Q NONE’ suffices_by (simp[all_preconditions_in_wp])
  >> gvs[wp_skip]
QED

Theorem assign_refinement_rule_none_pan:
  P ⊆ valid_value v src ∩ subst v src Q ⇒ refine (HoareC P Q NONE) (PanC (Assign v src))
Proof
  rw[refine_def,sat_def]
  >> ‘P ⊆ wp (Assign v src) Q NONE’ suffices_by (simp[all_preconditions_in_wp])
  >> gvs[wp_assign]
QED

Theorem assign_refinement_rule_error_pan:
  P ⊆ Q DIFF valid_value v src ⇒ refine (HoareC P Q (SOME Error)) (PanC (Assign v src))
Proof
  rw[refine_def,sat_def]
  >> ‘P ⊆ wp (Assign v src) Q (SOME Error)’ suffices_by (simp[all_preconditions_in_wp])
  >> gvs[wp_assign]
QED

Theorem seq_refinement_rule_pan:
  refine (SeqC (PanC l) (PanC r)) (PanC (Seq l r))
Proof
  rw[refine_def,sat_def]
QED

Theorem seq_refinement_rule_none:
  refine (HoareC P Q NONE) (SeqC (HoareC P M NONE) (HoareC M Q NONE))
Proof
  rw[refine_def,sat_def]
  >> elim_cases [‘prog’]
  >> ‘P ⊆ wp (Seq p p0) Q NONE’ suffices_by (simp[all_preconditions_in_wp])
  >> ‘P ⊆ wp p M NONE ∧ M ⊆ wp p0 Q NONE’ by (gvs[all_preconditions_in_wp])
  >> ‘wp p M NONE ⊆ wp p (wp p0 Q NONE) NONE’ by (gvs[wp_monotonic])
  >> ‘P ⊆ wp p (wp p0 Q NONE) NONE’ by (ASM_SET_TAC[])
  >> gvs[wp_seq]
QED

Theorem seq_refinement_rule_some_left:
  res ≠ NONE ⇒ refine (HoareC P Q res) (SeqC (HoareC P Q res) DCC)
Proof
  rw[refine_def,sat_def]
  >> elim_cases [‘prog’]
  >> ‘P ⊆ wp (Seq p p0) Q res’ suffices_by (simp[all_preconditions_in_wp])
  >> ‘P ⊆ wp p Q res’ by (gvs[all_preconditions_in_wp])
  >> gvs[wp_seq]
  >> ASM_SET_TAC[]
QED

Theorem seq_refinement_rule_some_right:
  res ≠ NONE ⇒ refine (HoareC P Q res) (SeqC (HoareC P M NONE) (HoareC M Q res))
Proof
  rw[refine_def,sat_def]
  >> elim_cases [‘prog’]
  >> ‘P ⊆ wp (Seq p p0) Q res’ suffices_by (simp[all_preconditions_in_wp])
  >> ‘P ⊆ wp p M NONE ∧ M ⊆ wp p0 Q res’ by (gvs[all_preconditions_in_wp])
  >> ‘wp p M NONE ⊆ wp p (wp p0 Q res) NONE’ by (gvs[wp_monotonic])
  >> ‘P ⊆ wp p (wp p0 Q res) NONE’ by (ASM_SET_TAC[])
  >> gvs[wp_seq]
  >> ASM_SET_TAC[]
QED

Theorem if_refinement_rule_pan:
  refine (IfC e (PanC p1) (PanC p2)) (PanC (If e p1 p2))
Proof
  rw[refine_def,sat_def]
QED

Theorem if_refinement_rule_success:
  res ≠ SOME Error ∧ P ⊆ will_evaluate e ⇒ refine (HoareC P Q res)
                                                  (IfC e (HoareC (with_eval P e) Q res)
                                                         (HoareC (with_compl P e) Q res))
Proof
  rw[refine_def,sat_def]
  >> elim_cases [‘prog’]
  >> ‘P ⊆ wp (If e p p0) Q res’ suffices_by (simp[all_preconditions_in_wp])
  >> ‘with_eval P e ⊆ wp p Q res ∧ with_compl P e ⊆ wp p0 Q res’ by (gvs[all_preconditions_in_wp])
  >> gvs[wp_if,with_eval_def,with_compl_def]
  >> elim_cases [‘res’]
  >- ASM_SET_TAC[pred_eval_lem]
  >> elim_cases [‘x’]
  >> ASM_SET_TAC[pred_eval_lem]
QED

Theorem if_refinement_rule_error_guard:
  P ⊆ COMPL (will_evaluate e) ∩ Q ⇒ refine (HoareC P Q (SOME Error)) (IfC e DCC DCC)
Proof
  rw[refine_def,sat_def]
  >> elim_cases [‘prog’]
  >> ‘P ⊆ wp (If e p p0) Q (SOME Error)’ suffices_by (simp[all_preconditions_in_wp])
  >> gvs[wp_if]
  >> ASM_SET_TAC[]
QED

Theorem if_refinement_rule_error_body:
  P ⊆ will_evaluate e ⇒ refine (HoareC P Q (SOME Error))
                               (IfC e (HoareC (with_eval P e) Q (SOME Error))
                                      (HoareC (with_compl P e) Q (SOME Error)))
Proof
  rw[refine_def,sat_def]
  >> elim_cases [‘prog’]
  >> ‘P ⊆ wp (If e p p0) Q (SOME Error)’ suffices_by (simp[all_preconditions_in_wp])
  >> ‘with_eval P e ⊆ wp p Q (SOME Error)’ by (gvs[all_preconditions_in_wp])
  >> ‘with_compl P e ⊆ wp p0 Q (SOME Error)’ by (gvs[all_preconditions_in_wp])
  >> gvs[wp_if,with_eval_def,with_compl_def]
  >> ASM_SET_TAC[pred_eval_lem]
QED

Theorem while_refinement_rule_pan:
  refine (WhileC e (PanC prog)) (PanC (While e prog))
Proof
  rw[refine_def,sat_def]
QED

(* TODO WHILE RULES *)

Theorem dcc_refinement_rule_pan:
  refine DCC (PanC prog)
Proof
  rw[refine_def,sat_def]
QED

val _ = export_theory();
