(***********************************************************************
 * Proofs of Refinement Rules for Pancake Statements                   *
 ***********************************************************************)

Theory panRefinement
Ancestors panPredicate panSem panProps panWeakestPrecondition

fun elim_cases xs = EVERY (map (fn x => Cases_on x >> gvs[]) xs);

Theorem pq_monotonic:
  ∀(A : ('a, 'ffi) state -> bool) B (res : 'a result option).
   (∀s. A s ⇒ B s) ⇒ (∀s. (λ(r,t). r = res ∧ A t) s ⇒ (λ(r,t). r = res ∧ B t) s)
Proof
  rw[]
  >> pairarg_tac
  >> gvs[]
QED

Definition is_variant_def:
  is_variant (i : ('a, 'ffi) state -> bool) (v : ('a, 'ffi) state -> num) p ⇔
             (∀s. i s ⇒ v (SND (evaluate (p,s))) < v s) ∧
             (∀s k1 k2.  v (s with clock := k1) = v (s with clock := k2))
End

Datatype:
  Contract = HoareC    (('a, 'ffi) state -> bool) (('a result option # ('a, 'ffi) state) -> bool)
           | SeqC      Contract Contract
           | IfC       ('a panLang$exp) Contract Contract
           | WhileC    ('a panLang$exp)
                       (('a, 'ffi) state -> bool)
                       (('a, 'ffi) state -> num)
                       Contract
           | PanC      ('a panLang$prog)
           | DCC
End

Definition sat_def[simp]:
  sat (HoareC P Q)     prog         = hoare P prog Q ∧
  sat (SeqC c1 c2)     (Seq p1 p2)  = (sat c1 p1 ∧ sat c2 p2) ∧
  sat (IfC l c1 c2)    (If r p1 p2) = (l = r ∧ sat c1 p1 ∧ sat c2 p2) ∧
  sat (WhileC l i v c) (While r p)  = (l = r ∧ sat c p ∧ is_variant i v p) ∧
  sat (PanC l)         r            = (l = r) ∧
  sat DCC              _            = T ∧
  sat _                _            = F
End

Theorem sat_cases[simp]:
  (∀c1 c2 prog.   sat (SeqC c1 c2)     prog ⇔ ∃p1 p2. prog = Seq p1 p2  ∧ sat c1 p1 ∧ sat c2 p2) ∧
  (∀e c1 c2 prog. sat (IfC e c1 c2)    prog ⇔ ∃p1 p2. prog = If e p1 p2 ∧ sat c1 p1 ∧ sat c2 p2) ∧
  (∀e i v c prog. sat (WhileC e i v c) prog ⇔ ∃p.     prog = While e p  ∧ sat c p ∧ is_variant i v p)
Proof
  rw[] >> elim_cases [‘prog’] >> iff_tac >> rw[]
QED

Definition refine_def:
  refine (c1 : ('a,'ffi) Contract) (c2 : ('a,'ffi) Contract) ⇔ ∀prog. sat c2 prog ⇒ sat c1 prog
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

Theorem strengthen_postcondition_refinement_rule:
  clkfree_q Q ∧ (∀s. Q' s ⇒ Q s) ⇒ refine (HoareC P Q) (HoareC P Q')
Proof
  rw[refine_def,hoare_def,clkfree_q_def]
  >> first_x_assum $ drule_then assume_tac
  >> gvs[]
  >> qexists ‘k’
  >> pairarg_tac
  >> gvs[]
QED

Theorem weaken_precondition_refinement_rule:
  clkfree_p P ∧ (∀s. P s ⇒ P' s) ⇒ refine (HoareC P Q) (HoareC P' Q)
Proof
  rw[refine_def,hoare_def,clkfree_p_def]
QED

Theorem skip_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧
  (∀s. P s ⇒ Q (NONE,s)) ⇒
  refine (HoareC P Q) (PanC Skip)
Proof
  rw[refine_def]
  >> qspecl_then [‘P’, ‘Skip’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> gvs[wp_skip]
QED

Theorem assign_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧
  (∀s. P s ⇒ valid_value k v src s ∧
             subst k v src (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (Assign k v src))
Proof
  rw[refine_def,sat_def]
  >> qspecl_then [‘P’, ‘Assign k v src’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> gvs[wp_assign]
QED

Theorem store_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧
  (∀s. P s ⇒ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                        evaluates_to src val s ∧
                        addr_in_mem addr val s ∧
                        mem_subst addr val (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (Store dest src))
Proof
  rw[refine_def]
  >> qspecl_then [‘P’, ‘Store dest src’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> gvs[wp_store]
QED

Theorem store32_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧
  (∀s. P s ⇒ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                        evaluates_to src (ValWord val) s ∧
                        addr_in_mem_32 addr val s ∧
                        mem_subst_32 addr val (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (Store32 dest src))
Proof
  rw[refine_def]
  >> qspecl_then [‘P’, ‘Store32 dest src’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> gvs[wp_store32]
QED

Theorem storebyte_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧
  (∀s. P s ⇒ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                        evaluates_to src (ValWord val) s ∧
                        addr_in_mem_byte addr val s ∧
                        mem_subst_byte addr val (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (StoreByte dest src))
Proof
  rw[refine_def]
  >> qspecl_then [‘P’, ‘StoreByte dest src’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> gvs[wp_storebyte]
QED

Theorem seq_refinement_rule_pan:
  refine (SeqC (PanC l) (PanC r)) (PanC (Seq l r))
Proof
  rw[refine_def]
QED

Theorem seq_refinement_rule_fst:
  clkfree_p P ∧ clkfree_q Q ⇒
  refine (HoareC P Q) (SeqC (HoareC P (λ(r,t). r ≠ NONE ∧ Q (r,t))) DCC)
Proof
  rw[refine_def]
  >> qspecl_then [‘P’, ‘p1’, ‘(λ(r,t). r ≠ NONE ∧ Q (r,t))’] assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘P’, ‘Seq p1 p2’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘Q’, ‘NONE’] assume_tac clkfree_qqn
  >> gvs[wp_seq]
QED

Theorem seq_refinement_rule_snd:
  clkfree_p P ∧ clkfree_q Q ∧ clkfree_p M ⇒
  refine (HoareC P Q) (SeqC (HoareC P (λ(r,t). r = NONE ∧ M t)) (HoareC M Q))
Proof
  rw[refine_def]
  >> qspecl_then [‘P’, ‘p1’, ‘(λ(r,t). r = NONE ∧ M t)’] assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘M’, ‘p2’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘P’, ‘Seq p1 p2’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> ‘clkfree_p (wp p2 Q)’ by (metis_tac[wp_clkfree])
  >> qspecl_then [‘wp p2 Q’, ‘NONE’] assume_tac clkfree_pq
  >> qspecl_then [‘M’, ‘NONE’] assume_tac clkfree_pq
  >> qspecl_then [‘M’, ‘wp p2 Q’, ‘NONE’] assume_tac pq_monotonic
  >> qspecl_then [‘λ(r,t). r = NONE ∧ M t’, ‘λ(r,t). r = NONE ∧ wp p2 Q t’, ‘p1’]
                 assume_tac wp_monotonic
  >> gvs[wp_seq]
QED

Theorem if_refinement_rule_pan:
  refine (IfC e (PanC l) (PanC r)) (PanC (If e l r))
Proof
  rw[refine_def]
QED

Theorem if_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧ (∀s. P s ⇒ evaluates_to_word e s) ⇒
  refine (HoareC P Q) (IfC e (HoareC (λs. P s ∧ evaluates_to_true  e s) Q)
                             (HoareC (λs. P s ∧ evaluates_to_false e s) Q))
Proof
  rw[refine_def]
  >> qspecl_then [‘λs. P s ∧ evaluates_to_true e s’, ‘p1’, ‘Q’]
                 assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘λs. P s ∧ evaluates_to_false e s’, ‘p2’, ‘Q’]
                 assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘P’, ‘If e p1 p2’, ‘Q’]
                 assume_tac wp_is_weakest_precondition
  >> ‘clkfree_p (λs. P s ∧ evaluates_to_true e s)’ by
     (metis_tac[clkfree_p_conj,clkfree_evaluates_to_true])
  >> ‘clkfree_p (λs. P s ∧ evaluates_to_false e s)’ by
     (metis_tac[clkfree_p_conj,clkfree_evaluates_to_false])
  >> gvs[wp_if]
QED

Theorem while_refinement_rule_pan:
  is_variant i v p ⇒
  refine (WhileC e i v (PanC p)) (PanC (While e p))
Proof
  rw[refine_def]
QED

Definition while_body_pre_def:
  while_body_pre i e = λs. i s ∧ evaluates_to_true e s
End

Definition while_body_post_def:
  while_body_post i QB QR QE QF = λ(r,t). i t ∧ case r of
                                                | SOME Break             => QB t
                                                | SOME (Return v)        => QR (t,v)
                                                | SOME (Exception eid e) => QE (t,eid,e)
                                                | SOME (FinalFFI f)      => QF (t,f)
                                                | _                      => T
End

Theorem while_refinement_rule:
  ∀P Q QB QR QE QF e i v.
  clkfree_p P ∧ clkfree_q Q ∧ clkfree_p i ∧
  (∀s. P s ⇒ i s) ∧
  (∀s. i s ⇒ evaluates_to_word e s) ∧
  (∀s. i s ∧ evaluates_to_false e s ⇒ Q (NONE,s)) ∧
  (∀t.       QB t         ⇒ Q (NONE,                  t)) ∧
  (∀t v.     QR (t,v)     ⇒ Q (SOME (Return v),       t)) ∧
  (∀t eid v. QE (t,eid,v) ⇒ Q (SOME (Exception eid v),t)) ∧
  (∀t f.     QF (t,f)     ⇒ Q (SOME (FinalFFI f),     t)) ⇒
  refine (HoareC P Q)
         (WhileC e i v (HoareC (while_body_pre i e) (while_body_post i QB QR QE QF)))
Proof
  rw[refine_def,hoare_def,while_body_pre_def,while_body_post_def]
  >> last_x_assum $ drule_then assume_tac
  >> qpat_x_assum ‘P s’ $ K all_tac
  >> measureInduct_on ‘v s’
  >> rw[Once evaluate_def]
  >> last_x_assum $ drule_then assume_tac
  >> gvs[evaluates_to_word_def,eval_upd_clock_eq]
  >> elim_cases [‘w = 0w’]
  >- (last_x_assum $ qspec_then ‘s’ assume_tac
      >> qexists ‘s.clock’
      >> gvs[evaluates_to_false_def,state_clock_idem])
  >> gvs[dec_clock_def,is_variant_def]
  >> qpat_x_assum ‘∀s. i s ∧ evaluates_to_true e s ⇒ _’ $ qspec_then ‘s’ assume_tac
  >> gvs[evaluates_to_true_def]
  >> pairarg_tac
  >> gvs[clkfree_p_def]
  >> qpat_x_assum ‘∀s k1 k2. i _ ⇔ i _’ $ qspecl_then [‘s’, ‘s.clock’, ‘k’] assume_tac
  >> gvs[state_clock_idem]
  >> qpat_x_assum ‘∀s. i s ⇒ v _ < v _’ $ qspec_then ‘s with clock := k’ assume_tac
  >> qpat_x_assum ‘∀s k1 k2. v _ = v _’ $ qspecl_then [‘s’, ‘s.clock’, ‘k’] assume_tac
  >> gvs[state_clock_idem]
  >> first_x_assum $ qspec_then ‘t’ assume_tac
  >> gvs[]
  >> pairarg_tac
  >> gvs[]
  >> qspecl_then [‘t with clock := k'’, ‘t'’, ‘r'’, ‘While e p’] assume_tac
                 (GEN_ALL evaluate_min_clock)
  >> qspecl_then [‘s with clock := k’, ‘t’, ‘r’, ‘p’] assume_tac
                 (GEN_ALL evaluate_min_clock)
  >> gvs[]
  >> qspecl_then [‘p’, ‘s with clock := k'''’, ‘r’, ‘t with clock := 0’, ‘k''’] assume_tac
                 evaluate_add_clock_eq
  >> gvs[]
  >> qexists ‘k'' + k''' + 1’
  >> rpt (pairarg_tac >> gvs[])
  >> elim_cases [‘r’]
  >- (gvs[clkfree_q_def]
      >> last_x_assum $ qspecl_then [‘r'’, ‘t'’, ‘t'.clock’, ‘0’] assume_tac
      >> gvs[state_clock_idem])
  >> elim_cases [‘x’]
  >> gvs[clkfree_q_def]
  >| [(last_x_assum $ qspecl_then [‘NONE’, ‘t’, ‘t.clock’, ‘k''’] assume_tac),
      (last_x_assum $ qspecl_then [‘r'’, ‘t'’, ‘t'.clock’, ‘0’] assume_tac),
      (last_x_assum $ qspecl_then [‘SOME (Return v')’, ‘t’, ‘t.clock’, ‘k''’] assume_tac),
      (last_x_assum $ qspecl_then [‘SOME (Exception m v')’, ‘t’, ‘t.clock’, ‘k''’] assume_tac),
      (last_x_assum $ qspecl_then [‘SOME (FinalFFI f)’, ‘t’, ‘t.clock’, ‘k''’] assume_tac)]
  >> gvs[state_clock_idem]
QED

Theorem dcc_refinement_rule:
  refine DCC (PanC prog)
Proof
  rw[refine_def]
QED
