(***********************************************************************)
(* Proves about Weakest Preconditions for Pancake Statements           *)
(*                                                                     *)
(* These proves are based on cakeml/pancake/semantics/panSemScript.sml *)
(***********************************************************************)

(* Helper-tactic for multiple calls of Cases_on followed by gvs[], *)
(* i.e. when eliminating non-trivial but contradictory cases       *)
fun elim_cases []      = all_tac
  | elim_cases (x::xs) = (Cases_on x >> gvs[] >> elim_cases xs);





(***************************************************************)
(* 1. Definitions and Theorems about Expressions as Predicates *)
(***************************************************************)

(* An expression is a predicate at a given state, if it evaluates to a ValWord *)
Definition is_pred_def:
  is_pred expr = λs. ∃w. eval s expr = SOME (ValWord w)
End

(* A predicate evaluates to true, if this ValWord is not zero *)
Definition pred_eval_def:
  pred_eval expr = λs. case (eval s expr) of
                       | SOME (ValWord w) => w ≠ 0w
                       | _                => F
End

(* Syntactic Lemma: A predicate evaluates to true, iff it evaluates to a non-zero value *)
Theorem pred_eval_elem:
  ∀s expr. s ∈ pred_eval expr ⇔ ∃w. eval s expr = SOME (ValWord w) ∧ w ≠ 0w
Proof
  simp[pred_eval_def]
  >> elim_cases [‘eval s expr’, ‘x’, ‘w’]
QED

(* A predicates complement evaluates to true, if the expression is a predicate, but does not evaluate to true *)
Definition pred_compl_def:
  pred_compl expr = {s | s ∈ is_pred expr ∧ s ∉ pred_eval expr}
End

(* Law of excluded middle, if the expression is a predicate *)
Theorem pred_eval_lem:
  ∀s expr. s ∈ is_pred expr ⇒ (s ∈ pred_eval expr ∨ s ∈ pred_compl expr)
Proof
  rw[is_pred_def,pred_eval_def,pred_compl_def]
QED

(* Syntactic Lemma: A predicate-complement evaluates to true, iff it evaluates to a zero *)
Theorem pred_compl_elem:
  ∀s expr. s ∈ pred_compl expr ⇔ ∃w. eval s expr = SOME (ValWord w) ∧ w = 0w
Proof
  rpt strip_tac
  >> iff_tac
  >> rw[pred_compl_def,pred_eval_def,is_pred_def]
  >> gvs[]
QED





(***********************************************************)
(* 2. Definitions and Theorems about Weakest Preconditions *)
(***********************************************************)

(* A hoare triple holds, if the state being fulfilling the precondition causes termination and a state fulfilling the postcondition *)
Definition hoare_def:
  hoare P prog Q ⇔ ∀s. s ∈ P ⇒ let (r, t) = evaluate (prog, s) in
                               r = NONE ∧ t ∈ Q
End

(* The weakest precondition is the union of all preconditions that form a hoare triple *)
Definition wp_def:
  wp prog Q = BIGUNION {P | hoare P prog Q}
End

(* The set-based definition above implies, that is actually is the weakest precondition *)
Theorem wp_is_weakest_precondition:
  ∀prog Q. hoare (wp prog Q) prog Q ∧ ∀P. hoare P prog Q ⇒ P ⊆ (wp prog Q)
Proof
  rw[wp_def]
  >- (rw[hoare_def] >> gvs[])
  >- (rw[BIGUNION,SUBSET_DEF] >> qexists_tac ‘P’ >> rw[])
QED

(* All preconditions are subsets of the weakest precondition *)
Theorem all_preconditions_in_wp:
  ∀P prog Q. hoare P prog Q ⇒ P ⊆ wp prog Q
Proof
  rw[wp_is_weakest_precondition]
QED

(* Syntactic Lemma: Therefore are the single-element preconditions also subsets of the weakest precondition *)
Theorem all_prestates_in_wp:
  ∀x P prog Q. hoare {x} prog Q ⇒ x ∈ wp prog Q
Proof
  rw[]
  >> assume_tac all_preconditions_in_wp
  >> first_x_assum $ (drule_then assume_tac)
  >> gvs[]
QED

(* A state is in the weakest precondition, iff it causes termination and a state fulfilling the postcondition *)
Theorem wp_iff_postcondition:
  ∀s prog Q. s ∈ wp prog Q ⇔ ∃t. evaluate (prog, s) = (NONE, t) ∧ t ∈ Q
Proof
  rpt strip_tac
  >> iff_tac
  >- (rw[wp_def,hoare_def]
      >> first_x_assum $ (drule_then assume_tac)
      >> pairarg_tac
      >> qexists_tac ‘t’
      >> gvs[])
  >- (rw[]
      >> ‘hoare {s} prog Q’ by (gvs[hoare_def])
      >> gvs[all_prestates_in_wp])
QED

(* Is a state in the weakest precondition of an if, is the guard expression a predicate *)
Theorem wp_if_pred_eval:
  ∀s. s ∈ wp (If e c1 c2) Q ⇒ s ∈ is_pred e
Proof
  rw[]
  >> ‘∃w. eval s e = SOME (ValWord w)’ suffices_by (rw[is_pred_def])
  >> gvs[wp_def,hoare_def]
  >> first_x_assum $ (drule_then assume_tac)
  >> pairarg_tac
  >> gvs[evaluate_def]
  >> elim_cases [‘eval s e’, ‘x’, ‘w’]
QED





(******************************************************)
(* 3. The Weakest Preconditions of Pancake Statements *)
(******************************************************)

(* The wp of the skip statement *)
Theorem wp_skip:
  wp Skip Q = Q
Proof
  gvs[EXTENSION,wp_iff_postcondition,evaluate_def]
QED

(* The wp of the seq statement *)
Theorem wp_seq:
  wp p1 (wp p2 Q) = wp (Seq p1 p2) Q
Proof
  rw[EXTENSION]
  >> iff_tac
  >> rw[]
  >- (‘∃t. evaluate (Seq p1 p2, x) = (NONE, t) ∧ t ∈ Q’ suffices_by (metis_tac[wp_iff_postcondition])
      >> ‘∃t. evaluate (p1, x) = (NONE, t) ∧ t ∈ wp p2 Q’ by (metis_tac[wp_iff_postcondition])
      >> ‘∃t'. evaluate (p2, t) = (NONE, t') ∧ t' ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> rw[evaluate_def])
  >- (‘∃t. evaluate (p1, x) = (NONE, t) ∧ t ∈ wp p2 Q’ suffices_by (metis_tac[wp_iff_postcondition])
      >> ‘∃t. evaluate (Seq p1 p2, x) = (NONE, t) ∧ t ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> gvs[evaluate_def]
      >> pairarg_tac
      >> Cases_on ‘res’
      >> gvs[]
      >> ‘∃t. evaluate (p2, s1) = (NONE, t) ∧ t ∈ Q’ suffices_by (metis_tac[wp_iff_postcondition])
      >> qexists_tac ‘t’
      >> gvs[])
QED

(* The wp of the if statement *)
Theorem wp_if:
  wp (If e c1 c2) Q = (pred_eval e ∩ wp c1 Q) ∪ (pred_compl e ∩ wp c2 Q)
Proof
  rw[EXTENSION]
  >> iff_tac
  >> rw[]
  >- (‘x ∈ is_pred e’ by (metis_tac[wp_if_pred_eval])
      >> ‘x ∈ pred_eval e ∨ x ∈ pred_compl e’ by (metis_tac[pred_eval_lem])
      >> gvs[Once wp_def,hoare_def,evaluate_def]
      >> first_x_assum $ (drule_then assume_tac)
      >- (‘x ∈ pred_eval e ∧ x ∈ wp c1 Q’ suffices_by (rw[])
          >> ‘∃w. eval x e = SOME (ValWord w) ∧ w ≠ 0w’ by (metis_tac[pred_eval_elem])
          >> gvs[]
          >> ‘hoare {x} c1 Q’ by (gvs[hoare_def])
          >> metis_tac[all_prestates_in_wp])
      >- (‘x ∈ pred_compl e ∧ x ∈ wp c2 Q’ suffices_by (rw[])
          >> ‘∃w. eval x e = SOME (ValWord w) ∧ w = 0w’ by (metis_tac[pred_compl_elem])
          >> gvs[]
          >> ‘hoare {x} c2 Q’ by (gvs[hoare_def])
          >> metis_tac[all_prestates_in_wp]))
  >> ‘hoare {x} (If e c1 c2) Q’ suffices_by (metis_tac[all_prestates_in_wp])
  >> rw[hoare_def,evaluate_def]
  >- (‘∃w. eval x e = SOME (ValWord w) ∧ w ≠ 0w’ by (metis_tac[pred_eval_elem])
      >> ‘∃t. evaluate (c1, x) = (NONE, t) ∧ t ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> gvs[])
  >- (‘∃w. eval x e = SOME (ValWord w) ∧ w = 0w’ by (metis_tac[pred_compl_elem])
      >> ‘∃t. evaluate (c2, x) = (NONE, t) ∧ t ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> gvs[])
QED

