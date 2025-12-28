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

Definition array_in_mem_def:
  array_in_mem b l = λs. b <+ b + l ∧ ∀addr. b <=+ addr ∧ addr <+ b + l ⇒ s.memaddrs addr
End

Theorem clkfree_array_in_mem:
  ∀b l. clkfree_p (λs. array_in_mem b l s) ∧
        clkfree_p (array_in_mem b l)
Proof
  rw[clkfree_p_def,array_in_mem_def]
QED

Definition appears_def:
  appears x b l = λs. ∃addr. b <=+ addr ∧ addr <+ b + l ∧ s.memory addr = x
End

Theorem clkfree_appears:
  ∀x b l. clkfree_p (λs. appears x b l s) ∧
          clkfree_p (appears x b l)
Proof
  rw[clkfree_p_def,appears_def]
QED

Definition mem_eq_def:
  mem_eq x addr = λs. s.memory addr = x
End

Theorem clkfree_mem_eq:
  ∀x addr. clkfree_p (λs. mem_eq x addr s) ∧
           clkfree_p (mem_eq x addr)
Proof
  rw[clkfree_p_def,mem_eq_def]
QED
          
Theorem linear_search:
   v ≠ v2 ⇒
   refine
     (HoareC
        (λs. s.memory = the_mem ∧ array_in_mem b l s ∧ appears (Word x) b l s)
        (λ(r,t).
             t.memory = the_mem ∧
             ∃ret. r = SOME (Return (ValWord ret)) ∧ b ≤₊ ret ∧ ret <₊ b + l ∧
                   mem_eq (Word x) ret t))
     (PanC
        (Dec v One (Const (0w : word64))
           (While (Cmp Lower (Var Local v) (Const l))
              (Dec v2 One (Load One (Op Add [Const b; Var Local v]))
                 (Seq
                    (If (Cmp Equal (Var Local v2) (Const x))
                       (Return (Op Add [Const b; Var Local v])) Skip)
                    (Assign Local v (Op Add [Const 1w; Var Local v])))))))
Proof
  rw[]
  >> qpat_abbrev_tac ‘P = (λs.
             s.memory = the_mem ∧ array_in_mem b l s ∧ appears (Word x) b l s)’
  >> qpat_abbrev_tac ‘Q = (λ(r,t).
             t.memory = the_mem ∧ 
             ∃ret. r = SOME (Return (ValWord ret)) ∧ b ≤₊ ret ∧ ret <₊ b + l ∧
                   mem_eq (Word x) ret t)’
  >> reverse (qsuff_tac ‘refine
        (HoareC P Q)
        (DecC v One (Const 0w)
           (HoareC (λs. P s ∧ var_eq_val Local v (ValWord 0w) s) Q))’)
  >- (rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> pan_refinement_thms_tac dec_refinement_rule_varfree
                                 [array_in_mem_def,clkfree_array_in_mem,
                                  appears_def,clkfree_appears,
                                  mem_eq_def,clkfree_mem_eq])
  >> rw[]
  >> qmatch_asmsub_abbrev_tac ‘DecC v One (Const 0w) (HoareC P' Q)’
  >> reverse (qsuff_tac ‘refine
     (HoareC P' Q)
     (WhileC (Cmp Lower (Var Local v) (Const l))
        (λs.
             array_in_mem b l s ∧
             s.memory = the_mem ∧
             ∃w. var_eq_val Local v (ValWord w) s ∧ w <₊ l ∧
                 appears (Word x) (b + w) (l - w) s)
        (λs. if FLOOKUP s.locals v ≠ NONE then w2n (l - var_word v s) else 0)
        (HoareC
           (while_body_pre
              (λs.
                   array_in_mem b l s ∧
                   s.memory = the_mem ∧
                   ∃w. var_eq_val Local v (ValWord w) s ∧ w <₊ l ∧
                       appears (Word x) (b + w) (l - w) s)
              (Cmp Lower (Var Local v) (Const l)))
           (while_body_post
              (λs.
                   array_in_mem b l s ∧
                   s.memory = the_mem ∧
                   ∃w. var_eq_val Local v (ValWord w) s ∧ w <₊ l ∧
                       appears (Word x) (b + w) (l - w) s) (λs. F)
              (λ(s,r).
                   ∃ret. r = ValWord ret ∧ b ≤₊ ret ∧ ret <₊ b + l ∧ array_in_mem b l s ∧
                         s.memory = the_mem ∧ s.memory ret = Word x) (λ(s,eid,e). F))))’)
  >> qpat_abbrev_tac ‘e = (Cmp Lower (Var Local v) (Const l))’
  >> qpat_abbrev_tac ‘i = (λs.
                  array_in_mem b l s ∧
                  s.memory = the_mem ∧
                  ∃w. var_eq_val Local v (ValWord w) s ∧ w <₊ l ∧
                      appears (Word x) (b + w) (l - w) s)’
  >> qpat_abbrev_tac ‘var = (λs. if FLOOKUP s.locals v ≠ NONE then w2n (l - var_word v s) else 0)’
  >> qpat_abbrev_tac ‘QB = (λs. F)’
  >> qpat_abbrev_tac ‘QR = (λ(s,r).
                        ∃ret. r = ValWord ret ∧ b ≤₊ ret ∧ ret <₊ b + l ∧
                              array_in_mem b l s ∧ s.memory = the_mem ∧ s.memory ret = Word x)’
  >> qpat_abbrev_tac ‘QE = (λ(s,eid,e). F)’
  >- (rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> refine_blast_thms_tac while_refinement_rule
                                 [array_in_mem_def,clkfree_array_in_mem,
                                  appears_def,clkfree_appears,
                                  mem_eq_def,clkfree_mem_eq])
  >> rw[]
  >> irule refine_transitive
  >> qexists ‘(DecC v One (Const 0w) (HoareC P' Q))’
  >> rw[]
  >> irule refine_transitive
  >> qexists ‘(DecC v One (Const 0w)
                 (PanC
                    (While e
                       (Dec v2 One (Load One (Op Add [Const b; Var Local v]))
                          (Seq
                             (If (Cmp Equal (Var Local v2) (Const x))
                                (Return (Op Add [Const b; Var Local v])) Skip)
                             (Assign Local v (Op Add [Const 1w; Var Local v])))))))’
  >> reverse (rw[])
  >- gvs[dec_refinement_rule_pan]
  >> irule refine_monotonic_dec
  >> irule refine_transitive
  >> qexists ‘(WhileC e i var
                      (HoareC (while_body_pre i e) (while_body_post i QB QR QE)))’
  >> rw[]
  >> rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
  >> qpat_abbrev_tac ‘P'' = while_body_pre i e’
  >> qpat_abbrev_tac ‘Q' = while_body_post i QB QR QE’
  >> qpat_abbrev_tac ‘ad = Op Add [Const b; Var Local v]’
  >> reverse(qsuff_tac ‘refine
                   (HoareC P'' Q')
                   (DecC v2 One (Load One ad)
                      (HoareC (λs. P'' s ∧ var_eq_mem Local v2 ad One s) Q'))’)
  >- refine_blast_thms_tac dec_refinement_rule_varfree_mem
                             [array_in_mem_def,clkfree_array_in_mem,
                              appears_def,clkfree_appears,
                              mem_eq_def,clkfree_mem_eq]
  >> qpat_abbrev_tac ‘P'3' = (λs. P'' s ∧ var_eq_mem Local v2 ad One s)’
  >> rw[]
  >> reverse(qsuff_tac ‘refine
                        (HoareC P'3' Q')
                        (SeqC
                           (HoareC P'3' (λ(r,t).
                                                 if r ≠ NONE then Q'(r,t)
                                                 else (λs.
                                                         P'3' s ∧
                                                         FLOOKUP s.locals v2 ≠ SOME (ValWord x) ∧
                                                         ∃w. FLOOKUP s.locals v = SOME (ValWord w) ∧
                                                             w + 1w <₊ l) t))
                           (HoareC (λs.
                                        P'3' s ∧
                                        FLOOKUP s.locals v2 ≠ SOME (ValWord x) ∧
                                        ∃w. FLOOKUP s.locals v = SOME (ValWord w) ∧ w + 1w <₊ l) Q'))’)
  >> qpat_abbrev_tac ‘M = (λs. P'3' s ∧ FLOOKUP s.locals v2 ≠ SOME (ValWord x) ∧
                               ∃w. FLOOKUP s.locals v = SOME (ValWord w) ∧ w + 1w <₊ l)’
  >- (rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> pan_refinement_thms_tac seq_refinement_rule_both
                             [array_in_mem_def,clkfree_array_in_mem,
                              appears_def,clkfree_appears,
                              mem_eq_def,clkfree_mem_eq])
  >> qpat_abbrev_tac ‘Q'' = (λ(r,t). if r ≠ NONE then Q' (r,t) else M t)’
  >> rw[]
  >> reverse(qsuff_tac ‘refine
                        (HoareC P'3' Q'')
                        (IfC (Cmp Equal (Var Local v2) (Const x))
                           (HoareC
                              (λs. P'3' s ∧ evaluates_to_true (Cmp Equal (Var Local v2) (Const x)) s)
                              Q'')
                           (HoareC
                              (λs. P'3' s ∧ evaluates_to_false (Cmp Equal (Var Local v2) (Const x)) s)
                              Q''))’)
  >> qpat_abbrev_tac ‘e' = (Cmp Equal (Var Local v2) (Const x))’
  >- (rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> pan_refinement_thms_tac if_refinement_rule
                             [array_in_mem_def,clkfree_array_in_mem,
                              appears_def,clkfree_appears,
                              mem_eq_def,clkfree_mem_eq])
  >> qpat_abbrev_tac ‘P'4' = (λs. P'³' s ∧ evaluates_to_true e' s)’
  >> qpat_abbrev_tac ‘P'5' = (λs. P'³' s ∧ evaluates_to_false e' s)’
  >> rw[]
  >> reverse(qsuff_tac ‘refine (HoareC P'4' Q'') (PanC (Return ad))’)
  >- (rpt(qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> refine_blast_thms_tac return_refinement_rule
                             [array_in_mem_def,clkfree_array_in_mem,
                              appears_def,clkfree_appears,
                              mem_eq_def,clkfree_mem_eq])
  >> rw[]
  >> dxrule_all_then assume_tac (cj 1 refine_monotonic_if)
  >> first_x_assum $ qspecl_then [‘HoareC P'5' Q''’, ‘e'’] assume_tac
  >> dxrule_all_then assume_tac refine_transitive
  >> reverse(qsuff_tac ‘refine (HoareC P'5' Q'') (PanC (Skip))’)
  >- (rpt(qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> pan_refinement_thms_tac skip_refinement_rule
                             [array_in_mem_def,clkfree_array_in_mem,
                              appears_def,clkfree_appears,
                              mem_eq_def,clkfree_mem_eq]
      >> first_x_assum $ mp_tac
      >> gvs[]
      >> Cases_on ‘b + c' = addr’
      >> gvs[]
      >> blast_tac)
  >> rw[]
  >> dxrule_all_then assume_tac (cj 2 refine_monotonic_if)
  >> first_x_assum $ qspecl_then [‘PanC (Return ad)’, ‘e'’] assume_tac
  >> dxrule_all_then assume_tac refine_transitive
  >> reverse(qsuff_tac ‘refine (IfC e' (PanC (Return ad)) (PanC Skip)) (PanC (If e' (Return ad) Skip))’)
  >- (gvs[if_refinement_rule_pan])
  >> rw[]
  >> dxrule_all_then assume_tac refine_transitive
  >> dxrule_all_then assume_tac (cj 1 refine_monotonic_seq)
  >> first_x_assum $ qspec_then ‘HoareC M Q'’ assume_tac
  >> reverse(qsuff_tac ‘refine (HoareC M Q') (PanC (Assign Local v (Op Add [Const 1w; Var Local v])))’)
  >- (rpt(qpat_x_assum ‘refine _ _’ $ kall_tac)
      >> pan_refinement_thms_tac assign_refinement_rule
                             [array_in_mem_def,clkfree_array_in_mem,
                              appears_def,clkfree_appears,
                              mem_eq_def,clkfree_mem_eq]
      >> first_x_assum $ mp_tac
      >> gvs[]
      >> Cases_on ‘b + c = addr’
      >> gvs[]
      >> blast_tac)
  >> rw[]
  >> dxrule_all_then assume_tac (cj 2 refine_monotonic_seq)
  >> first_x_assum $ qspec_then ‘(PanC (If e' (Return ad) Skip))’ assume_tac
  >> dxrule_all_then assume_tac refine_transitive
  >> reverse(qsuff_tac ‘refine
                        (SeqC
                           (PanC (If e' (Return ad) Skip))
                           (PanC (Assign Local v (Op Add [Const 1w; Var Local v]))))
                        (PanC (Seq (If e' (Return ad) Skip)
                                   (Assign Local v (Op Add [Const 1w; Var Local v]))))’)
  >- gvs[seq_refinement_rule_pan]
  >> rw[]
  >> qspecl_then [‘HoareC P'3' Q'’, ‘SeqC (HoareC P'³' Q'') (HoareC M Q')’,
                  ‘v2’, ‘One’, ‘Load One ad’] assume_tac refine_monotonic_dec
  >> gvs[]
  >> dxrule_all_then assume_tac refine_transitive
  >> dxrule_all_then assume_tac refine_monotonic_dec
  >> first_x_assum $ qspecl_then [‘v2’, ‘One’, ‘Load One ad’] assume_tac
  >> dxrule_all_then assume_tac refine_transitive
  >> reverse(qsuff_tac ‘refine
                        (DecC v2 One (Load One ad)
                           (PanC
                              (Seq (If e' (Return ad) Skip)
                                  (Assign Local v (Op Add [Const 1w; Var Local v])))))
                        (PanC
                            (Dec v2 One (Load One ad)
                               (Seq (If e' (Return ad) Skip)
                                   (Assign Local v (Op Add [Const 1w; Var Local v])))))’)
  >- gvs[dec_refinement_rule_pan]
  >> rw[]
  >> dxrule_all_then assume_tac refine_transitive
  >> dxrule_all_then assume_tac refine_transitive
  >> dxrule_all_then assume_tac refine_monotonic_while
  >> first_x_assum $ qspecl_then [‘e’, ‘i’, ‘var’] assume_tac
  >> irule refine_transitive
  >> qexists ‘(WhileC e i var
             (PanC
                (Dec v2 One (Load One ad)
                   (Seq (If e' (Return ad) Skip)
                        (Assign Local v (Op Add [Const 1w; Var Local v]))))))’
  >> rw[]
  >> rpt (qpat_x_assum ‘refine _ _’ $ kall_tac)
  >> irule while_refinement_rule_pan
  >> unabbrev_all_tac
  >> gvs[array_in_mem_def,appears_def,mem_eq_def,var_eq_val_def]
  >> rw[is_variant_def]
  >> BasicProvers.every_case_tac
  >> gvs[]
  >- (‘0w <₊ w - l’ by blast_tac
      >> Cases_on ‘w2n (l + -1w * w)’
      >> gvs[]
      >> blast_tac)
  >> first_x_assum $ mp_tac
  >> rw_tac pan_refinement_ss [evaluate_def]
  >- (Cases_on ‘s.memory (b + w)’
      >> gvs[]
      >> Cases_on ‘c' = x’
      >> gvs[]
      >- (gvs[evaluate_def,eval_def,wordLangTheory.word_op_def,finite_mapTheory.FLOOKUP_UPDATE,
              size_of_shape_def,shape_of_def,empty_locals_def]
          >> Cases_on ‘FLOOKUP s.locals v2’
          >> gvs[res_var_def,finite_mapTheory.FLOOKUP_UPDATE])
      >> gvs[evaluate_def,finite_mapTheory.FLOOKUP_UPDATE,shape_of_def]
      >> Cases_on ‘FLOOKUP s.locals v2’
      >> gvs[res_var_def,finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.DOMSUB_FLOOKUP_THM]
      >> blast_tac)
  >- (spose_not_then assume_tac
      >> qpat_x_assum ‘¬_’ $ mp_tac
      >> gvs[]
      >> first_x_assum $ irule
      >> blast_tac)
  >> Cases_on ‘s.memory (b + w)’
  >> gvs[]
  >> Cases_on ‘c = x’
  >> gvs[]
  >- (gvs[evaluate_def,eval_def,wordLangTheory.word_op_def,finite_mapTheory.FLOOKUP_UPDATE,
          size_of_shape_def,shape_of_def,empty_locals_def]
      >> Cases_on ‘FLOOKUP s.locals v2’
      >> gvs[res_var_def,finite_mapTheory.FLOOKUP_UPDATE])
  >> gvs[evaluate_def,finite_mapTheory.FLOOKUP_UPDATE,shape_of_def]
  >> Cases_on ‘FLOOKUP s.locals v2’
  >> gvs[res_var_def,finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.DOMSUB_FLOOKUP_THM]
QED
