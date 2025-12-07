Theory panRefinementExample
Ancestors panReducedLang panReducedSem panPredicate panWeakestPrecondition panRefinement
          finite_map[qualified] wordLang[qualified]
Libs panRefinementLib BasicProvers[qualified] blastLib[qualified] HolSmtLib[qualified]

val refine_blast_tac = pan_refinement_tac_z3o;
val refine_blast_thms_tac = pan_refinement_thms_tac_z3o;
val blast_tac = HolSmtLib.Z3_ORACLE_TAC;

Definition w64_def[simp]:
  w64 (w : word64) = ValWord w
End

Definition fixed_def[simp]:
  fixed res = λr. res = r
End

Definition postcond_def[simp]:
  postcond (qr : 'a result option -> bool)
           (qt : 'a state -> bool) = λ(r,t). qr r ∧ qt t
End

Definition var_word_def[simp]:
  var_word x = λs. case FLOOKUP s.locals x of
                   | SOME (ValWord w) => w
                   | _                => 0w
End

Theorem assignment_1:
   refine
     (HoareC (var_eq_val Local x (w64 0w))
        (postcond (fixed NONE) (var_eq_val Local x (w64 10w))))
     (PanC (Assign Local x (Const 10w)))
Proof
  pan_refinement_tac assign_refinement_rule
QED

Theorem assignment_2:
   refine
     (HoareC (var_eq_val Local x (w64 0w))
        (postcond (fixed NONE) (var_eq_val Local x (w64 10w))))
     (PanC
        (While (Cmp Less (Var Local x) (Const 10w))
           (Assign Local x (Op Add [Var Local x; Const 1w]))))
Proof
  rw[]
  >> reverse (qsuff_tac ‘refine
     (HoareC (var_eq_val Local x (w64 0w))
        (postcond (fixed NONE) (var_eq_val Local x (w64 10w))))
     (WhileC (Cmp Less (Var Local x) (Const 10w))
        (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)
        (λs. w2n (-1w * var_word x s + 11w))
        (HoareC
           (while_body_pre
              (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)
              (Cmp Less (Var Local x) (Const 10w)))
           (while_body_post
              (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)
              (λs. F) (λ(s,r). F) (λ(s,eid,e). F))))’)
  >- (rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> qpat_abbrev_tac ‘P = (var_eq_val Local x (w64 0w))’
      >> qpat_abbrev_tac ‘Q = (postcond (fixed NONE) (var_eq_val Local x (w64 10w)))’
      >> qpat_abbrev_tac ‘e = (Cmp Less (Var Local x) (Const 10w))’
      >> qpat_abbrev_tac ‘i = (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)’
      >> qpat_abbrev_tac ‘v = (λs. w2n (-1w * var_word x s + 11w))’
      >> qpat_abbrev_tac ‘QB = (λs. F)’
      >> qpat_abbrev_tac ‘QR = (λ(s,r). F)’
      >> qpat_abbrev_tac ‘QE = (λ(s,eid,e). F)’
      >> refine_blast_tac while_refinement_rule)
  >> rw[]
  >> reverse (qsuff_tac ‘refine
     (WhileC (Cmp Less (Var Local x) (Const 10w))
        (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)
        (λs. w2n (-1w * var_word x s + 11w))
        (HoareC
           (while_body_pre
              (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)
              (Cmp Less (Var Local x) (Const 10w)))
           (while_body_post
              (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)
              (λs. F) (λ(s,r). F) (λ(s,eid,e). F))))
     (WhileC (Cmp Less (Var Local x) (Const 10w))
        (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)
        (λs. w2n (-1w * var_word x s + 11w))
        (PanC (Assign Local x (Op Add [Var Local x; Const 1w]))))’)
  >- (reverse (qsuff_tac ‘refine
     (HoareC
        (while_body_pre
           (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)
           (Cmp Less (Var Local x) (Const 10w)))
        (while_body_post
           (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w) (λs. F)
           (λ(s,r). F) (λ(s,eid,e). F)))
     (PanC (Assign Local x (Op Add [Var Local x; Const 1w])))’)
      >- (rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
          >> qpat_abbrev_tac ‘e = (Cmp Less (Var Local x) (Const 10w))’
          >> qpat_abbrev_tac ‘i = (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)’
          >> qpat_abbrev_tac ‘QB = (λs. F)’
          >> qpat_abbrev_tac ‘QR = (λ(s,r). F)’
          >> qpat_abbrev_tac ‘QE = (λ(s,eid,e). F)’
          >> gvs[]
          >> refine_blast_tac assign_refinement_rule)
      >> rw[]
      >> gvs[refine_monotonic_while])
  >> rw[]
  >> drule_all_then assume_tac refine_transitive
  >> reverse (qsuff_tac ‘refine
     (WhileC (Cmp Less (Var Local x) (Const 10w))
        (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)
        (λs. w2n (-1w * var_word x s + 11w))
        (PanC (Assign Local x (Op Add [Var Local x; Const 1w]))))
     (PanC
        (While (Cmp Less (Var Local x) (Const 10w))
           (Assign Local x (Op Add [Var Local x; Const 1w]))))’)
  >- (rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> qpat_abbrev_tac ‘e = (Cmp Less (Var Local x) (Const 10w))’
      >> qpat_abbrev_tac ‘i = (λs. ∃w. var_eq_val Local x (w64 w) s ∧ 0w ≤ w ∧ w ≤ 10w)’
      >> qpat_abbrev_tac ‘v = (λs. w2n (-1w * var_word x s + 11w))’
      >> refine_blast_thms_tac while_refinement_rule_pan [evaluate_def])
  >> rw[]
  >> drule_all_then assume_tac refine_transitive
  >> gvs[]
QED

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

Definition appears_def:
  appears x b e = λs. ∃addr. b ≤ addr ∧ addr ≤ e ∧ s.memory addr = x
End

Theorem linear_search1:
  Abbrev (P = (λs. appears x b e s ∧ s.memory = the_mem)) ∧
  Abbrev (Q = (λ(r,t). r = SOME (Return (ValWord ret)) ∧ b ≤ ret ∧ ret ≤ e ∧ the_mem ret = x)) ⇒
  refine (HoareC P Q) (DecC v One (Const 0w) (HoareC (set_val P v (Const 0w)) (ignore_val Q v)))
Proof
  rw[]
  >> irule dec_refinement_rule
  >> unabbrev_all_tac
  >> rw[]
  >- (gvs[ignore_val_def] >> pairarg_tac >> gvs[])
  >- (gvs[ignore_val_def] >> pairarg_tac >> gvs[])
  >- (gvs[ignore_val_def] >> pairarg_tac >> gvs[])
  >- (gvs[ignore_val_def] >> pairarg_tac >> gvs[])
  >- (qexists ‘ValWord 0w’ >> gvs[evaluates_to_def,eval_def])
  >- gvs[appears_def,clkfree_p_def]
  >- gvs[clkfree_q_def]
QED
