Theory panRefinementExample
Ancestors panSem panRefinement
Libs panRefinementLib

Definition var_eq_def[simp]:
  var_eq x (w : word64) = λs. FLOOKUP s.locals x = SOME (ValWord w)
End

Definition fixed_def[simp]:
  fixed res = λr. res = r
End

Definition postcond_def[simp]:
  postcond (qr : 'a result option -> bool)
           (qt : ('a, 'ffi) state -> bool) = λ(r,t). qr r ∧ qt t
End

Definition var_word[simp]:
  var_word x = λs. case FLOOKUP s.locals x of
                   | SOME (ValWord w) => w
                   | _                => 0w
End

Theorem assignment_1:
  Abbrev (P = var_eq x 0w) ∧
  Abbrev (Q = postcond (fixed NONE) (var_eq x 10w)) ⇒
  refine (HoareC P Q) (PanC (Assign Local x (Const 10w)))
Proof
  pan_refinement_tac assign_refinement_rule
QED

Theorem assignment_2_step_1:
  Abbrev (P = var_eq x 0w) ∧
  Abbrev (Q = postcond (fixed NONE) (var_eq x 10w)) ∧
  Abbrev (QB = (λs. F)) ∧
  Abbrev (QR = (λ(s,r). F)) ∧
  Abbrev (QE = (λ(s,eid,e). F)) ∧
  Abbrev (QF = (λ(s,f). F)) ∧
  Abbrev (e = (Cmp Less (Var Local x) (Const 10w))) ∧
  Abbrev (v = (λs. w2n (11w - var_word x s))) ∧
  Abbrev (i = (λs. ∃w. var_eq x w s ∧ 0w ≤ w ∧ w ≤ 10w)) ⇒
  refine (HoareC P Q)
         (WhileC e i v (HoareC (while_body_pre i e) (while_body_post i QB QR QE QF)))
Proof
  pan_refinement_tac while_refinement_rule
QED

Theorem assignment_2_step_2:
  Abbrev (P  = (while_body_pre i e)) ∧
  Abbrev (Q  = (while_body_post i QB QR QE QF)) ∧
  Abbrev (QB = (λs. F)) ∧
  Abbrev (QR = (λ(s,r). F)) ∧
  Abbrev (QE = (λ(s,eid,e). F)) ∧
  Abbrev (QF = (λ(s,f). F)) ∧
  Abbrev (e  = (Cmp Less (Var Local x) (Const 10w))) ∧
  Abbrev (i = (λs. ∃w. var_eq x w s ∧ 0w ≤ w ∧ w ≤ 10w)) ⇒
  refine (HoareC P Q)
         (PanC (Assign Local x (Op Add [(Var Local x); (Const 1w)])))
Proof
  pan_refinement_tac assign_refinement_rule
QED

Theorem assignment_2_step_3:
  Abbrev (P = var_eq x 0w) ∧
  Abbrev (Q = postcond (fixed NONE) (var_eq x 10w)) ∧
  Abbrev (e = (Cmp Less (Var Local x) (Const 10w))) ∧
  Abbrev (v = (λs. w2n (11w - var_word x s))) ∧
  Abbrev (i = (λs. ∃w. var_eq x w s ∧ 0w ≤ w ∧ w ≤ 10w)) ⇒
  refine (WhileC e i v (PanC (Assign Local x (Op Add [(Var Local x); (Const 1w)]))))
         (PanC (While e (Assign Local x (Op Add [(Var Local x); (Const 1w)]))))
Proof
  pan_refinement_thms_tac while_refinement_rule_pan [evaluate_def]
QED

(* inst type, there might be something in wordsLib *)
