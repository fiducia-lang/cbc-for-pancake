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
     (HoareC (λs. FLOOKUP s.locals x = SOME (w64 0w))
        (postcond (fixed NONE) (λs. FLOOKUP s.locals x = SOME (w64 10w))))
     (PanC (Assign Local x (Const 10w)))
Proof
  pan_refinement_tac assign_refinement_rule
QED

Theorem assignment_2:
   refine
     (HoareC (λs. FLOOKUP s.locals x = SOME (w64 0w))
        (postcond (fixed NONE) (λs. FLOOKUP s.locals x = SOME (w64 10w))))
     (PanC
        (While (Cmp Less (Var Local x) (Const 10w))
           (Assign Local x (Op Add [Var Local x; Const 1w]))))
Proof
  rw[]
  >> reverse (qsuff_tac ‘refine 
     (HoareC (λs. FLOOKUP s.locals x = SOME (w64 0w))
        (postcond (fixed NONE) (λs. FLOOKUP s.locals x = SOME (w64 10w))))
     (WhileC (Cmp Less (Var Local x) (Const 10w))
        (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)
        (HoareC
           (while_body_pre
              (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)
              (Cmp Less (Var Local x) (Const 10w)))
           (while_body_post
              (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)
              (λs. F) (λ(s,r). F) (λ(s,eid,e). F))))’)
  >- (rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> qpat_abbrev_tac ‘P = (λs. FLOOKUP s.locals x = SOME (w64 0w))’
      >> qpat_abbrev_tac ‘Q = (postcond (fixed NONE) (λs. FLOOKUP s.locals x = SOME (w64 10w)))’
      >> qpat_abbrev_tac ‘e = (Cmp Less (Var Local x) (Const 10w))’
      >> qpat_abbrev_tac ‘i = (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)’
      >> qpat_abbrev_tac ‘QB = (λs. F)’
      >> qpat_abbrev_tac ‘QR = (λ(s,r). F)’
      >> qpat_abbrev_tac ‘QE = (λ(s,eid,e). F)’
      >> refine_blast_tac while_refinement_rule)
  >> rw[]
  >> reverse (qsuff_tac ‘refine
     (WhileC (Cmp Less (Var Local x) (Const 10w))
        (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)
        (HoareC
           (while_body_pre
              (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)
              (Cmp Less (Var Local x) (Const 10w)))
           (while_body_post
              (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)
              (λs. F) (λ(s,r). F) (λ(s,eid,e). F))))
     (WhileC (Cmp Less (Var Local x) (Const 10w))
        (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)
        (PanC (Assign Local x (Op Add [Var Local x; Const 1w]))))’)
  >- (reverse (qsuff_tac ‘refine
     (HoareC
       (while_body_pre
          (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)
          (Cmp Less (Var Local x) (Const 10w)))
       (while_body_post
          (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)
          (λs. F) (λ(s,r). F) (λ(s,eid,e). F)))
     (PanC (Assign Local x (Op Add [Var Local x; Const 1w])))’)
      >- (rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
          >> qpat_abbrev_tac ‘e = (Cmp Less (Var Local x) (Const 10w))’
          >> qpat_abbrev_tac ‘i = (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)’
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
        (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)
        (PanC (Assign Local x (Op Add [Var Local x; Const 1w]))))
     (PanC
        (While (Cmp Less (Var Local x) (Const 10w))
           (Assign Local x (Op Add [Var Local x; Const 1w]))))’)
  >- (rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> qpat_abbrev_tac ‘e = (Cmp Less (Var Local x) (Const 10w))’
      >> qpat_abbrev_tac ‘i = (λs. ∃w. FLOOKUP s.locals x = SOME (w64 w) ∧ 0w ≤ w ∧ w ≤ 10w)’
      >> refine_blast_thms_tac while_refinement_rule_pan [evaluate_def])
  >> rw[]
  >> drule_all_then assume_tac refine_transitive
  >> gvs[]
QED
