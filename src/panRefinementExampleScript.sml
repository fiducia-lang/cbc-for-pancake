Theory panRefinementExample
Ancestors panSem panPredicate panRefinement
          wordLang
          asm bit finite_map option words
Libs blastLib wordsLib BasicProvers

fun elim_cases xs = EVERY (map (fn x => Cases_on x >> gvs[]) xs);

val refinement_proof_simpset = srw_ss() && [clkfree_p_def,clkfree_q_def,
                                            while_body_pre_def,while_body_post_def,is_variant_def,
                                            subst_def,eval_def,
                                            evaluates_to_word_def,evaluates_to_false_def,evaluates_to_true_def,
                                            valid_value_def,is_valid_value_def,shape_of_def,
                                            word_cmp_def,word_op_def,
                                            FLOOKUP_UPDATE];

fun cleanup_tac extra = unabbrev_all_tac
                        >> rpt (CHANGED_TAC (rw_tac refinement_proof_simpset extra))
                        >> every_case_tac
                        >> gvs[]
                        >> FULL_BBLAST_TAC;

Theorem assignment_1:
  Abbrev (P = (λs. FLOOKUP s.locals x = SOME (ValWord 0w))) ∧
  Abbrev (Q = (λ(r,s). r = NONE ∧ FLOOKUP s.locals x = SOME (ValWord 10w))) ∧
  Abbrev (k = Local) ∧
  Abbrev (src = (Const 10w)) ∧
  Abbrev (v = x) ⇒
  refine (HoareC P Q) (PanC (Assign k v src))
Proof
  rw[]
  >> irule assign_refinement_rule
  >> cleanup_tac []
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
  rw[]
  >> irule while_refinement_rule
  >> cleanup_tac []
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
  rw[]
  >> irule assign_refinement_rule
  >> cleanup_tac []
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
  rw[]
  >> irule while_refinement_rule_pan
  >> cleanup_tac [evaluate_def,GSYM WORD_LO]
QED
