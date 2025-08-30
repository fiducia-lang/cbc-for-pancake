(***********************************************************************
 * Proofs about Weakest Preconditions of Pancake Statements            *
 ***********************************************************************)

Theory panWeakestPrecondition
Ancestors panSem panPredicate

fun elim_cases xs = EVERY (map (fn x => Cases_on x >> gvs[]) xs);

Definition hoare_def:
  hoare P prog Q ⇔ ∀s. ∃k. P s ⇒ let (r,t) = evaluate (prog,s with clock := k)
                                 in r ≠ SOME Error ∧
                                    r ≠ SOME TimeOut ∧
                                    ∀k'. Q (r,t with clock := k')
End

Definition wp_def:
  wp prog Q s ⇔ ∃k. let (r,t) = evaluate (prog,s with clock := k)
                    in r ≠ SOME Error ∧
                       r ≠ SOME TimeOut ∧
                       ∀k'. Q (r,t with clock := k')
End

Theorem wp_is_weakest_precondition:
  ∀prog Q. hoare (wp prog Q) prog Q ∧
           ∀P. hoare P prog Q ⇔ (∀s. P s ⇒ wp prog Q s)
Proof
  metis_tac[wp_def,hoare_def]
QED

Theorem wp_monotonic:
  ∀A B prog. (∀s. A s ⇒ B s) ⇒ (∀s. wp prog A s ⇒ wp prog B s)
Proof
  rw[wp_def]
  >> pairarg_tac
  >> qexists ‘k’
  >> gvs[]
QED

(* TODO FROM HERE; REVISIT DEFINITIONS ABOVE *)

Theorem wp_skip:
  wp Skip Q = λs. Q (NONE, s)
Proof
  rw[FUN_EQ_THM]
  >> iff_tac
  >> rw[wp_def,evaluate_def]
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
