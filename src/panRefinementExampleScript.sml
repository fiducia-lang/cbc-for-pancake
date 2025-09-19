Theory panRefinementExample
Ancestors panSem panRefinement
Libs panRefinementLib

Theorem assignment_1:
  Abbrev (P = (λs. FLOOKUP s.locals x = SOME (ValWord 0w))) ∧
  Abbrev (Q = (λ(r,s). r = NONE ∧ FLOOKUP s.locals x = SOME (ValWord 10w))) ∧
  Abbrev (k = Local) ∧
  Abbrev (src = (Const 10w)) ∧
  Abbrev (v = x) ⇒
  refine (HoareC P Q) (PanC (Assign k v src))
Proof
  pan_refinement_tac assign_refinement_rule
QED

Theorem assignment_2_step_1:
  Abbrev (P = (λs. FLOOKUP s.locals x = SOME (ValWord (0w : word64)))) ∧
  Abbrev (Q = (λ(r,s). r = NONE ∧ FLOOKUP s.locals x = SOME (ValWord (10w : word64)))) ∧
  Abbrev (QB = (λs. F)) ∧
  Abbrev (QR = (λ(s,r). F)) ∧
  Abbrev (QE = (λ(s,eid,e). F)) ∧
  Abbrev (QF = (λ(s,f). F)) ∧
  Abbrev (e = (Cmp Less (Var Local x) (Const 10w))) ∧
  Abbrev (v = (λs. case FLOOKUP s.locals x of
                   | (SOME (ValWord w)) => w2n (11w - w)
                   | _ => 0)) ∧
  Abbrev (i = (λs. ∃w. FLOOKUP s.locals x = SOME (ValWord w) ∧ 0w ≤ w ∧ w ≤ 10w)) ⇒
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
  Abbrev (i = (λs. ∃w. FLOOKUP s.locals x = SOME (ValWord w) ∧ 0w ≤ w ∧ w ≤ (10w : word64))) ⇒
  refine (HoareC P Q)
         (PanC (Assign Local x (Op Add [(Var Local x); (Const 1w)])))
Proof
  pan_refinement_tac assign_refinement_rule
QED

Theorem assignment_2_step_3:
  Abbrev (P = (λs. FLOOKUP s.locals x = SOME (ValWord (0w : word64)))) ∧
  Abbrev (Q = (λ(r,s). r = NONE ∧ FLOOKUP s.locals x = SOME (ValWord (10w : word64)))) ∧
  Abbrev (e = (Cmp Less (Var Local x) (Const 10w))) ∧
  Abbrev (v = (λs. case FLOOKUP s.locals x of
                   | (SOME (ValWord w)) => w2n ((11w : word64) - w)
                   | _ => 0)) ∧
  Abbrev (i = (λs. ∃w. FLOOKUP s.locals x = SOME (ValWord w) ∧ 0w ≤ w ∧ w ≤ 10w)) ⇒
  refine (WhileC e i v (PanC (Assign Local x (Op Add [(Var Local x); (Const 1w)]))))
         (PanC (While e (Assign Local x (Op Add [(Var Local x); (Const 1w)]))))
Proof
  pan_refinement_thms_tac while_refinement_rule_pan [evaluate_def]
QED

(* inst type, there might be something in wordsLib *)
