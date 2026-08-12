(***********************************************************************
 * Proofs of Refinement Rules for Pancake Statements                   *
 ***********************************************************************)

Theory panRefinement
Ancestors panSem panProps panPredicate panWeakestPrecondition
          finite_map[qualified]
Libs BasicProvers

fun elim_cases xs = EVERY (map (fn x => Cases_on x >> gvs[]) xs);

Theorem pq_monotonic:
  ∀(A : ('a,'ffi) state -> bool) B (res : 'a result option).
   (∀s. A s ⇒ B s) ⇒ (∀s. (λ(r,t). r = res ∧ A t) s ⇒ (λ(r,t). r = res ∧ B t) s)
Proof
  rw[]
  >> pairarg_tac
  >> gvs[]
QED

Datatype:
  Contract = HoareC    (('a, 'ffi) state -> bool) (('a result option # ('a, 'ffi) state) -> bool)
           | DecC      varname shape ('a panLang$exp) Contract
           | SeqC      Contract Contract
           | IfC       ('a panLang$exp) Contract Contract
           | WhileC    ('a panLang$exp)
                       (('a, 'ffi) state -> bool)
                       Contract
           | PanC      ('a panLang$prog)
           | DCC
End

Definition sat_def[simp]:
  sat (HoareC P Q)      prog             = hoare P prog Q ∧
  sat (DecC nl sl el c) (Dec nr sr er p) = (nl = nr ∧ sl = sr ∧ el = er ∧ sat c p) ∧
  sat (SeqC c1 c2)      (Seq p1 p2)      = (sat c1 p1 ∧ sat c2 p2) ∧
  sat (IfC l c1 c2)     (If r p1 p2)     = (l = r ∧ sat c1 p1 ∧ sat c2 p2) ∧
  sat (WhileC l i c)    (While r p)      = (l = r ∧ sat c p) ∧
  sat (PanC l)          r                = (l = r) ∧
  sat DCC               _                = T ∧
  sat _                 _                = F
End

Theorem sat_cases[simp]:
  (∀n s e l c prog. sat (DecC s e l c)   prog ⇔ ∃p.     prog = Dec s e l p ∧ sat c p) ∧
  (∀c1 c2 prog.     sat (SeqC c1 c2)     prog ⇔ ∃p1 p2. prog = Seq p1 p2   ∧ sat c1 p1 ∧ sat c2 p2) ∧
  (∀e c1 c2 prog.   sat (IfC e c1 c2)    prog ⇔ ∃p1 p2. prog = If e p1 p2  ∧ sat c1 p1 ∧ sat c2 p2) ∧
  (∀e i v c prog.   sat (WhileC e i c)   prog ⇔ ∃p.     prog = While e p   ∧ sat c p)
Proof
  rw[] >> elim_cases [‘prog’] >> iff_tac >> rw[]
QED

Definition refine_def:
  refine (c1 : ('a, 'ffi) Contract) (c2 : ('a, 'ffi) Contract) ⇔ ∀prog. sat c2 prog ⇒ sat c1 prog
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

Theorem refine_monotonic_dec:
  ∀A B v sh exp. refine A B ⇒ refine (DecC v sh exp A) (DecC v sh exp B)
Proof
  rw[refine_def]
QED

Theorem refine_monotonic_seq:
  ∀A B C. refine A B ⇒ refine (SeqC A C) (SeqC B C) ∧
                       refine (SeqC C A) (SeqC C B)
Proof
  rw[refine_def]
QED

Theorem refine_monotonic_if:
  ∀A B C e. refine A B ⇒ refine (IfC e A C) (IfC e B C) ∧
                         refine (IfC e C A) (IfC e C B)
Proof
  rw[refine_def]
QED

Theorem refine_monotonic_while:
  ∀A B e i. refine A B ⇒ refine (WhileC e i A) (WhileC e i B)
Proof
  rw[refine_def]
QED

Theorem strengthen_postcondition_refinement_rule:
  (∀s. Q' s ⇒ Q s) ⇒ refine (HoareC P Q) (HoareC P Q')
Proof
  rw[refine_def,hoare_def]
  >> first_x_assum $ drule_then assume_tac
  >> pairarg_tac
  >> gvs[]
QED

Theorem weaken_precondition_refinement_rule:
  (∀s. P s ⇒ P' s) ⇒ refine (HoareC P Q) (HoareC P' Q)
Proof
  rw[refine_def,hoare_def]
QED

Theorem skip_refinement_rule:
  (∀s. P s ⇒ Q (NONE,s)) ⇒
  refine (HoareC P Q) (PanC Skip)
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_skip]
QED

Theorem dec_refinement_rule_pan:
  refine (DecC v sh src (PanC prog)) (PanC (Dec v sh src prog))
Proof
  rw[refine_def]
QED

Theorem dec_refinement_rule_varfree:
  varfree_p v P ∧
  varfree_q v Q ∧
  ¬MEM v (var_exp src) ∧
  (∀s. P s ⇒ evaluates src s) ⇒
  refine (HoareC P Q)
         (DecC v sh src (HoareC (λs. P s ∧ var_eq Local v src s) Q))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> dxrule_then assume_tac $ ((iffLR o cj 2) wp_is_weakest_precondition)
  >> rw[]
  >> last_x_assum $ drule_then assume_tac
  >> gvs[wp_dec,evaluates_def]
  >> last_x_assum $ qspec_then ‘s with locals := s.locals |+ (v,v')’ assume_tac
  >> gvs[varfree_p_def,var_eq_def,finite_mapTheory.FLOOKUP_UPDATE,eval_fresh_var]
  >> gvs[subst_def]
  >> qsuff_tac ‘reset_subst v s Q = Q’
  >- rw[]
  >> gvs[FUN_EQ_THM]
  >> PairCases
  >> iff_tac
  >> gvs[reset_subst_def]
  >> Cases_on ‘FLOOKUP s.locals v’
  >> gvs[res_var_def,varfree_q_def]
  >> Cases_on ‘FLOOKUP x1.locals v’
  >> rw[]
  >- (‘x1 with locals := x1.locals \\ v = x1’ suffices_by metis_tac[]
      >> ‘x1.locals \\ v = x1.locals’ suffices_by gvs[state_component_equality]
      >> gvs[finite_mapTheory.flookup_thm,finite_mapTheory.DOMSUB_NOT_IN_DOM])
  >- (first_x_assum $ qspecl_then [‘x0’, ‘x1 with locals := x1.locals \\ v’, ‘x’] assume_tac
      >> gvs[]
      >> ‘x1 with locals := x1.locals |+ (v,x) = x1’ suffices_by metis_tac[]
      >> ‘x1.locals |+ (v,x) = x1.locals’ suffices_by gvs[state_component_equality]
      >> irule finite_mapTheory.FUPDATE_ELIM
      >> gvs[finite_mapTheory.flookup_thm])
  >- (first_x_assum $ qspecl_then [‘x0’, ‘x1 with locals := x1.locals |+ (v,x)’, ‘x’] assume_tac
      >> gvs[]
      >> ‘x1 with locals := x1.locals \\ v = x1’ suffices_by metis_tac[]
      >> ‘x1.locals \\ v = x1.locals’ suffices_by gvs[state_component_equality]
      >> gvs[finite_mapTheory.flookup_thm,finite_mapTheory.DOMSUB_NOT_IN_DOM])
  >> first_x_assum $ qspecl_then [‘x0’, ‘x1 with locals := x1.locals |+ (v,x)’, ‘x'’] assume_tac
  >> gvs[]
  >> ‘x1 with locals := x1.locals |+ (v,x') = x1’ suffices_by metis_tac[]
  >> ‘x1.locals |+ (v,x') = x1.locals’ suffices_by gvs[state_component_equality]
  >> irule finite_mapTheory.FUPDATE_ELIM
  >> gvs[finite_mapTheory.flookup_thm]
QED

Theorem assign_refinement_rule:
  (∀s. P s ⇒ valid_value k v src s ∧
             subst k v src (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (Assign k v src))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_assign]
QED

Theorem store_refinement_rule:
  (∀s. P s ⇒ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                        evaluates_to src val s ∧
                        addr_in_mem addr val s ∧
                        mem_subst addr val (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (Store dest src))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_store]
QED

Theorem store32_refinement_rule:
  (∀s. P s ⇒ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                        evaluates_to src (ValWord val) s ∧
                        addr_in_mem_32 addr val s ∧
                        mem_subst_32 addr val (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (Store32 dest src))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_store32]
QED

Theorem storebyte_refinement_rule:
  (∀s. P s ⇒ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                        evaluates_to src (ValWord val) s ∧
                        addr_in_mem_byte addr val s ∧
                        mem_subst_byte addr val (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (StoreByte dest src))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_storebyte]
QED

Theorem seq_refinement_rule_pan:
  refine (SeqC (PanC l) (PanC r)) (PanC (Seq l r))
Proof
  rw[refine_def]
QED

Theorem seq_refinement_rule_both:
  refine (HoareC P Q) (SeqC (HoareC P (λ(r,t). if r ≠ NONE then Q (r,t) else M t))
                            (HoareC M Q))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> rpt(dxrule_then assume_tac $ ((iffLR o cj 2) wp_is_weakest_precondition))
  >> rw[]
  >> first_x_assum $ dxrule_then assume_tac
  >> dxrule_then assume_tac (iffLR wp_nif)
  >> dxrule_then assume_tac pq_monotonic
  >> gvs[wp_seq]
  >> disj1_tac
  >> irule wp_monotonic
  >> HINT_EXISTS_TAC
  >> gvs[]
QED

Theorem if_refinement_rule_pan:
  refine (IfC e (PanC l) (PanC r)) (PanC (If e l r))
Proof
  rw[refine_def]
QED

Theorem if_refinement_rule:
  (∀s. P s ⇒ evaluates_to_word e s) ⇒
  refine (HoareC P Q) (IfC e (HoareC (λs. P s ∧ evaluates_to_true  e s) Q)
                             (HoareC (λs. P s ∧ evaluates_to_false e s) Q))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> rpt(dxrule_then assume_tac $ ((iffLR o cj 2) wp_is_weakest_precondition))
  >> gvs[wp_if]
QED

Theorem while_refinement_rule_pan:
  refine (WhileC e i (PanC p)) (PanC (While e p))
Proof
  rw[refine_def]
QED

Definition while_body_pre_def:
  while_body_pre i e = λs. i s ∧ evaluates_to_true e s
End

Definition while_body_post_def:
  while_body_post i QB (QR : ('a, 'ffi) state # 'a v -> bool) QE QF = λ(r,t). case r of
                                             | SOME Break             => QB t
                                             | SOME (Return v)        => QR (t,v)
                                             | SOME (Exception eid e) => QE (t,eid,e)
                                             | SOME (FinalFFI res)    => QF (t,res)
                                             | _                      => i t
End

Theorem while_refinement_rule:
  ∀P Q QB QR QE QF e i v.
  (∀s. P s ⇒ i s) ∧
  (∀s. i s ⇒ evaluates_to_word e s) ∧
  (∀s. i s ∧ evaluates_to_false e s ⇒ Q (NONE,s)) ∧
  (∀s k. i s ⇒ i (s with clock := k)) ∧
  (∀t.       QB t         ⇒ Q (NONE,                  t)) ∧
  (∀t v.     QR (t,v)     ⇒ Q (SOME (Return v),       t)) ∧
  (∀t eid v. QE (t,eid,v) ⇒ Q (SOME (Exception eid v),t)) ∧
  (∀t res.   QF (t,res)   ⇒ Q (SOME (FinalFFI res),   t)) ⇒
  refine (HoareC P Q)
         (WhileC e i (HoareC (while_body_pre i e) (while_body_post i QB QR QE QF)))
Proof
  rw[refine_def,hoare_def,while_body_pre_def,while_body_post_def]
  >> last_x_assum $ drule_then assume_tac
  >> qpat_x_assum ‘P s’ $ K all_tac
  >> measureInduct_on ‘s.clock’
  >> rw[Once evaluate_def]
  >> last_x_assum $ drule_then assume_tac
  >> gvs[evaluates_to_word_def,eval_upd_clock_eq]
  >> pairarg_tac
  >> Cases_on ‘w = 0w’
  >> gvs[]
  >- gvs[evaluates_to_false_def]
  >- gvs[evaluates_to_false_def]
  >> pairarg_tac
  >> Cases_on ‘res’
  >> gvs[dec_clock_def]
  >> qpat_x_assum ‘∀s k. i s ⇒ _’ $ qspecl_then [‘s’, ‘s.clock -1’] assume_tac
  >> gvs[]
  >> qpat_x_assum ‘∀s. i s ∧ evaluates_to_true e s ⇒ _’ $ dxrule_then assume_tac
  >> gvs[evaluates_to_true_def,eval_upd_clock_eq]
  >- (first_x_assum $ qspec_then ‘s1’ assume_tac
      >> gvs[]
      >> first_x_assum $ irule
      >> ‘s1.clock ≤ (s with clock := s.clock - 1).clock’ suffices_by gvs[]
      >> irule evaluate_clock
      >> qexistsl [‘p’, ‘NONE’]
      >> gvs[])
  >> Cases_on ‘x’
  >> gvs[]
  >> first_x_assum $ qspec_then ‘s1’ assume_tac
  >> gvs[]
  >> first_x_assum $ irule
  >> ‘s1.clock ≤ (s with clock := s.clock - 1).clock’ suffices_by gvs[]
  >> irule evaluate_clock
  >> qexistsl [‘p’, ‘SOME Continue’]
  >> gvs[]
QED

Theorem dcc_refinement_rule:
  refine DCC (PanC prog)
Proof
  rw[refine_def]
QED

Theorem return_refinement_rule:
  (∀s. P s ⇒ ∃val. evaluates_to e val s ∧
                   size_of_shape (shape_of val) ≤ 32 ∧
                   Q (SOME (Return val),empty_locals s)) ⇒
  refine (HoareC P Q) (PanC (Return e))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_return]
QED

Theorem annot_refinement_rule:
  (∀s. P s ⇒ Q (NONE,s)) ⇒
  refine (HoareC P Q) (PanC (Annot t1 t2))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_annot]
QED

Theorem break_refinement_rule:
  (∀s. P s ⇒ Q (SOME Break,s)) ⇒
  refine (HoareC P Q) (PanC (Break))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_break]
QED

Theorem continue_refinement_rule:
  (∀s. P s ⇒ Q (SOME Continue,s)) ⇒
  refine (HoareC P Q) (PanC (Continue))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_continue]
QED

Theorem raise_refinement_rule:
  (∀s. P s ⇒ ∃sh val. has_eshape eid sh s ∧ evaluates_to e val s ∧ shape_of val = sh ∧
                      size_of_shape (shape_of val) ≤ 32 ∧
                      Q (SOME (Exception eid val),empty_locals s)) ⇒
  refine (HoareC P Q) (PanC (Raise eid e))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_raise]
QED
