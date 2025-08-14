(***********************************************************************
 * Proves about Weakest Preconditions for Pancake Statements           *
 *                                                                     *
 * This file has to be placed in cakeml/pancake/semantics/             *
 ***********************************************************************)

open HolKernel Parse boolLib BasicProvers bossLib
open pred_setTheory
open panSemTheory

val _ = new_theory "weakestPrecondition";

(* Helper-tactic for multiple calls of Cases_on followed by gvs[], *)
(* i.e. when eliminating non-trivial but contradictory cases       *)
fun elim_cases []      = all_tac
  | elim_cases (x::xs) = (Cases_on x >> gvs[] >> elim_cases xs);


(***************************************************************
 * 1. Definitions and Theorems about Expressions as Predicates *
 ***************************************************************)

Definition will_evaluate_def:
  will_evaluate expr = λs. ∃w. eval s expr = SOME (ValWord w)
End

Definition pred_eval_def:
  pred_eval expr = λs. case (eval s expr) of
                       | SOME (ValWord w) => w ≠ 0w
                       | _                => F
End

Theorem pred_eval_elem:
  ∀s expr. s ∈ pred_eval expr ⇔ ∃w. eval s expr = SOME (ValWord w) ∧ w ≠ 0w
Proof
  simp[pred_eval_def]
  >> elim_cases [‘eval s expr’, ‘x’, ‘w’]
QED

Definition pred_compl_def:
  pred_compl expr = will_evaluate expr ∩ COMPL (pred_eval expr)
End

Theorem pred_eval_lem:
  ∀s expr. s ∈ will_evaluate expr ⇔ (s ∈ pred_eval expr ∨ s ∈ pred_compl expr)
Proof
  rpt strip_tac
  >> iff_tac
  >> rw[will_evaluate_def,pred_eval_def,pred_compl_def]
  >> elim_cases [‘eval s expr’, ‘x’, ‘w’]
QED

Theorem pred_compl_elem:
  ∀s expr. s ∈ pred_compl expr ⇔ ∃w. eval s expr = SOME (ValWord w) ∧ w = 0w
Proof
  rpt strip_tac
  >> iff_tac
  >> rw[pred_compl_def,pred_eval_def,will_evaluate_def]
  >> gvs[]
QED

Theorem pred_eval_compl_contradict:
  ∀s expr. s ∈ pred_eval expr ⇒ s ∉ pred_compl expr
Proof
  rw[pred_eval_def,pred_compl_def]
QED


(***********************************************************
 * 2. Definitions about Valid Values for Variables         *
 ***********************************************************)

Definition valid_value_def:
  valid_value v src = λs. case (eval s src) of
                          | NONE       => F
                          | SOME value => is_valid_value s.locals v value
End

Definition subst_def:
  subst v src P = λs. case (eval s src) of
                      | NONE       => F
                      | SOME value => (s with locals := s.locals |+ (v,value)) ∈ P
End


(***********************************************************
 * 3. Definitions and Theorems about Weakest Preconditions *
 ***********************************************************)

Definition hoare_def:
  hoare P prog Q res ⇔ ∀s. s ∈ P ⇒ let (r, t) = evaluate (prog, s) in
                                   r = res ∧ t ∈ Q
End

Definition wp_def:
  wp prog Q res = BIGUNION {P | hoare P prog Q res}
End

Theorem wp_is_weakest_precondition:
  ∀prog Q res. hoare (wp prog Q res) prog Q res ∧ ∀P. hoare P prog Q res ⇔ P ⊆ (wp prog Q res)
Proof
  SET_TAC[wp_def,hoare_def]
QED

Theorem wp_monotonic:
  ∀A B prog res. A ⊆ B ⇒ wp prog A res ⊆ wp prog B res
Proof
  rw[SUBSET_DEF,wp_def]
  >> qexists_tac ‘{x}’
  >> gvs[hoare_def]
  >> pairarg_tac
  >> first_x_assum $ (drule_then assume_tac)
  >> gvs[]
QED

Theorem all_preconditions_in_wp:
  ∀P prog Q res. hoare P prog Q res ⇔ P ⊆ wp prog Q res
Proof
  rw[wp_is_weakest_precondition]
QED

Theorem all_prestates_in_wp:
  ∀x P prog Q res. hoare {x} prog Q res ⇔ x ∈ wp prog Q res
Proof
  SET_TAC[all_preconditions_in_wp]
QED

Theorem wp_iff_postcondition:
  ∀s prog Q res. s ∈ wp prog Q res ⇔ ∃t. evaluate (prog, s) = (res, t) ∧ t ∈ Q
Proof
  rpt strip_tac
  >> iff_tac
  >- (rw[wp_def,hoare_def]
      >> first_x_assum $ (drule_then assume_tac)
      >> pairarg_tac
      >> qexists_tac ‘t’
      >> gvs[])
  >- (rw[]
      >> ‘hoare {s} prog Q res’ by (gvs[hoare_def])
      >> gvs[all_prestates_in_wp])
QED

Theorem wp_if_will_evaluate:
  ∀s res. res ≠ SOME Error ⇒ (s ∈ wp (If e c1 c2) Q res ⇒ s ∈ will_evaluate e)
Proof
  rw[]
  >> ‘∃w. eval s e = SOME (ValWord w)’ suffices_by (rw[will_evaluate_def])
  >> gvs[wp_def,hoare_def]
  >> first_x_assum $ (drule_then assume_tac)
  >> pairarg_tac
  >> gvs[evaluate_def]
  >> elim_cases [‘eval s e’, ‘x’, ‘w’]
QED

Theorem wp_assign_valid_value:
  ∀s. s ∈ wp (Assign v src) Q NONE ⇒ s ∈ valid_value v src
Proof
  rw[valid_value_def,wp_def,hoare_def,evaluate_def]
  >> first_x_assum $ (drule_then assume_tac)
  >> pairarg_tac
  >> elim_cases [‘eval s src’, ‘is_valid_value s.locals v x’]
QED

Theorem wp_assign_subst:
  ∀s. s ∈ wp (Assign v src) Q NONE ⇒ s ∈ subst v src Q
Proof
  rw[subst_def,wp_def,hoare_def,evaluate_def]
  >> first_x_assum $ (drule_then assume_tac)
  >> pairarg_tac
  >> elim_cases [‘eval s src’, ‘is_valid_value s.locals v x’]
QED

Theorem wp_error_invalid:
  ∀s. s ∈ wp (Assign v src) Q (SOME Error) ⇔ s ∈ Q DIFF (valid_value v src)
Proof
  strip_tac
  >> iff_tac
  >- (rw[valid_value_def,wp_def,hoare_def,evaluate_def]
      >> first_x_assum $ (drule_then assume_tac)
      >> pairarg_tac
      >> gvs[]
      >> elim_cases [‘eval s src’, ‘is_valid_value s.locals v x’])
  >- (rw[]
      >> ‘hoare {s} (Assign v src) Q (SOME Error)’ suffices_by (metis_tac[all_prestates_in_wp])
      >> gvs[valid_value_def,hoare_def,evaluate_def]
      >> pairarg_tac
      >> gvs[]
      >> elim_cases [‘eval s src’])
QED


(******************************************************
 * 4. The Weakest Preconditions of Pancake Statements *
 ******************************************************)

Theorem wp_skip:
  wp Skip Q res = if res = NONE then Q
                                else ∅
Proof
  Cases_on ‘res = NONE’
  >> rw[]
  >> gvs[EXTENSION,wp_iff_postcondition,evaluate_def]
QED

Theorem wp_seq:
  wp (Seq p1 p2) Q res = if res = NONE then wp p1 (wp p2 Q res) res
                                       else wp p1 (wp p2 Q res) NONE ∪ wp p1 Q res
Proof
  Cases_on ‘res = NONE’
  >> rw[EXTENSION]
  >> iff_tac
  >> rw[]
  >- (‘∃t. evaluate (p1, x) = (NONE, t) ∧ t ∈ wp p2 Q NONE’ suffices_by (metis_tac[wp_iff_postcondition])
      >> ‘∃t. evaluate (Seq p1 p2, x) = (NONE, t) ∧ t ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> gvs[evaluate_def]
      >> pairarg_tac
      >> Cases_on ‘res’
      >> gvs[]
      >> ‘∃t. evaluate (p2, s1) = (NONE, t) ∧ t ∈ Q’ suffices_by (metis_tac[wp_iff_postcondition])
      >> qexists_tac ‘t’
      >> gvs[])
  >- (‘∃t. evaluate (Seq p1 p2, x) = (NONE, t) ∧ t ∈ Q’ suffices_by (metis_tac[wp_iff_postcondition])
      >> ‘∃t. evaluate (p1, x) = (NONE, t) ∧ t ∈ wp p2 Q NONE’ by (metis_tac[wp_iff_postcondition])
      >> ‘∃t'. evaluate (p2, t) = (NONE, t') ∧ t' ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> rw[evaluate_def])
  >- (‘(∃t. evaluate (p1, x) = (NONE, t) ∧ t ∈ wp p2 Q res) ∨ (∃t'. evaluate (p1, x) = (res, t') ∧ t' ∈ Q)’ suffices_by (metis_tac[wp_iff_postcondition])
      >> ‘∃t. evaluate (Seq p1 p2, x) = (res, t) ∧ t ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> gvs[evaluate_def]
      >> pairarg_tac
      >> Cases_on ‘res'’
      >> gvs[]
      >> ‘∃t. evaluate (p2, s1) = (res, t) ∧ t ∈ Q’ suffices_by (metis_tac[wp_iff_postcondition])
      >> qexists_tac ‘t’
      >> gvs[])
  >- (‘∃t. evaluate (Seq p1 p2, x) = (res, t) ∧ t ∈ Q’ suffices_by (metis_tac[wp_iff_postcondition])
      >> ‘∃t. evaluate (p1, x) = (NONE, t) ∧ t ∈ wp p2 Q res’ by (metis_tac[wp_iff_postcondition])
      >> ‘∃t'. evaluate (p2, t) = (res, t') ∧ t' ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> rw[evaluate_def])
  >- (‘∃t. evaluate (Seq p1 p2, x) = (res, t) ∧ t ∈ Q’ suffices_by (metis_tac[wp_iff_postcondition])
      >> ‘∃t. evaluate (p1, x) = (res, t) ∧ t ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> qexists_tac ‘t’
      >> rw[evaluate_def])
QED

Theorem wp_if:
  wp (If e c1 c2) Q res = case res of
                          | SOME Error => (COMPL (will_evaluate e) ∩ Q) ∪ (pred_eval e ∩ wp c1 Q (SOME Error)) ∪ (pred_compl e ∩ wp c2 Q (SOME Error))
                          | res'       => (pred_eval e ∩ wp c1 Q res') ∪ (pred_compl e ∩ wp c2 Q res')
Proof
  Cases_on ‘res ≠ SOME Error’
  >- (‘wp (If e c1 c2) Q res = (pred_eval e ∩ wp c1 Q res) ∪ (pred_compl e ∩ wp c2 Q res)’ suffices_by (elim_cases [‘res’, ‘x’])
      >> rw[EXTENSION]
      >> iff_tac
      >> rw[]
      >- (‘x ∈ will_evaluate e’ by (metis_tac[wp_if_will_evaluate])
          >> ‘x ∈ pred_eval e ∨ x ∈ pred_compl e’ by (metis_tac[pred_eval_lem])
          >> gvs[Once wp_def,hoare_def,evaluate_def]
          >> first_x_assum $ (drule_then assume_tac)
          >- (‘x ∈ pred_eval e ∧ x ∈ wp c1 Q res’ suffices_by (rw[])
              >> ‘∃w. eval x e = SOME (ValWord w) ∧ w ≠ 0w’ by (metis_tac[pred_eval_elem])
              >> gvs[]
              >> ‘hoare {x} c1 Q res’ by (gvs[hoare_def])
              >> metis_tac[all_prestates_in_wp])
          >- (‘x ∈ pred_compl e ∧ x ∈ wp c2 Q res’ suffices_by (rw[])
              >> ‘∃w. eval x e = SOME (ValWord w) ∧ w = 0w’ by (metis_tac[pred_compl_elem])
              >> gvs[]
              >> ‘hoare {x} c2 Q res’ by (gvs[hoare_def])
              >> metis_tac[all_prestates_in_wp]))
      >> ‘hoare {x} (If e c1 c2) Q res’ suffices_by (metis_tac[all_prestates_in_wp])
      >> rw[hoare_def,evaluate_def]
      >- (‘∃w. eval x e = SOME (ValWord w) ∧ w ≠ 0w’ by (metis_tac[pred_eval_elem])
          >> ‘∃t. evaluate (c1, x) = (res, t) ∧ t ∈ Q’ by (metis_tac[wp_iff_postcondition])
          >> gvs[])
      >- (‘∃w. eval x e = SOME (ValWord w) ∧ w = 0w’ by (metis_tac[pred_compl_elem])
          >> ‘∃t. evaluate (c2, x) = (res, t) ∧ t ∈ Q’ by (metis_tac[wp_iff_postcondition])
          >> gvs[]))
  >> gvs[]
  >> rw[EXTENSION]
  >> iff_tac
  >> rw[]
  >- (‘x ∉ will_evaluate e ∨ x ∈ pred_eval e ∨ x ∈ pred_compl e’ by (metis_tac[pred_eval_lem])
      >- (‘x ∉ will_evaluate e ∧ x ∈ Q’ suffices_by (rw[])
          >> gvs[wp_def,hoare_def,evaluate_def]
          >> first_x_assum $ (drule_then assume_tac)
          >> gvs[will_evaluate_def]
          >> elim_cases [‘eval x e’, ‘x'’, ‘w’])
      >> gvs[Once wp_def,hoare_def,evaluate_def]
      >> first_x_assum $ (drule_then assume_tac)
      >- (‘x ∈ pred_eval e ∧ x ∈ wp c1 Q (SOME Error)’ suffices_by (rw[])
          >> ‘∃w. eval x e = SOME (ValWord w) ∧ w ≠ 0w’ by (metis_tac[pred_eval_elem])
          >> gvs[]
          >> ‘hoare {x} c1 Q (SOME Error)’ by (gvs[hoare_def])
          >> metis_tac[all_prestates_in_wp])
      >- (‘x ∈ pred_compl e ∧ x ∈ wp c2 Q (SOME Error)’ suffices_by (rw[])
          >> ‘∃w. eval x e = SOME (ValWord w) ∧ w = 0w’ by (metis_tac[pred_compl_elem])
          >> gvs[]
          >> ‘hoare {x} c2 Q (SOME Error)’ by (gvs[hoare_def])
          >> metis_tac[all_prestates_in_wp]))
  >> ‘hoare {x} (If e c1 c2) Q (SOME Error)’ suffices_by (metis_tac[all_prestates_in_wp])
  >> rw[hoare_def,evaluate_def]
  >- (gvs[will_evaluate_def]
      >> elim_cases [‘eval x e’, ‘x'’, ‘w’])
  >- (‘∃w. eval x e = SOME (ValWord w) ∧ w ≠ 0w’ by (metis_tac[pred_eval_elem])
      >> ‘∃t. evaluate (c1, x) = (SOME Error, t) ∧ t ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> gvs[])
  >- (‘∃w. eval x e = SOME (ValWord w) ∧ w = 0w’ by (metis_tac[pred_compl_elem])
      >> ‘∃t. evaluate (c2, x) = (SOME Error, t) ∧ t ∈ Q’ by (metis_tac[wp_iff_postcondition])
      >> gvs[])
QED

Theorem wp_assign:
  wp (Assign v src) Q res = case res of
                            | NONE       => valid_value v src ∩ subst v src Q
                            | SOME Error => Q DIFF valid_value v src
                            | _          => ∅
Proof
  Cases_on ‘res’
  >- (rw[EXTENSION]
      >> iff_tac
      >> rw[]
      >- metis_tac[wp_assign_valid_value]
      >- metis_tac[wp_assign_subst]
      >> ‘hoare {x} (Assign v src) Q NONE’ suffices_by (metis_tac[all_prestates_in_wp])
      >> gvs[valid_value_def,subst_def,hoare_def,evaluate_def]
      >> pairarg_tac
      >> elim_cases [‘eval x src’])
  >> Cases_on ‘x’
  >- gvs[EXTENSION,wp_error_invalid]
  >> gvs[EXTENSION,wp_iff_postcondition,evaluate_def]
  >> rw[]
  >> elim_cases [‘eval x src’, ‘is_valid_value x.locals v x'’]
QED

val _ = export_theory();
