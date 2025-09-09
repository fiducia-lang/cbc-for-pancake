(***********************************************************************
 * Proofs about Weakest Preconditions of Pancake Statements            *
 ***********************************************************************)

Theory panWeakestPrecondition
Ancestors panSem panProps panPredicate

fun elim_cases xs = EVERY (map (fn x => Cases_on x >> gvs[]) xs);

Theorem state_clock_idem:
  ∀s. s with clock := s.clock = s
Proof
  rw[state_component_equality]
QED

Definition hoare_def:
  hoare P prog Q ⇔ clkfree_p P ∧
                   clkfree_q Q ∧
                   ∀s. P s ⇒ ∃k. let (r,t) = evaluate (prog,s with clock := k)
                                 in r ≠ SOME Error ∧
                                    r ≠ SOME TimeOut ∧
                                    Q (r,t)
End

Definition wp_def:
  wp prog Q s ⇔ clkfree_q Q ∧
                ∃k. let (r,t) = evaluate (prog,s with clock := k)
                    in r ≠ SOME Error ∧
                       r ≠ SOME TimeOut ∧
                       Q (r,t)
End

Theorem wp_clkfree:
  ∀prog Q. clkfree_p (wp prog Q)
Proof
  rw[clkfree_p_def,wp_def]
QED

Theorem wp_is_weakest_precondition:
  ∀P prog Q. clkfree_p P ∧ clkfree_q Q ⇒ hoare (wp prog Q) prog Q ∧
                                         (hoare P prog Q ⇔ (∀s. P s ⇒ wp prog Q s))
Proof
  metis_tac[hoare_def,wp_def,wp_clkfree]
QED

Theorem wp_monotonic:
  ∀A B prog. (clkfree_q A ∧ clkfree_q B) ⇒ (∀s. A s ⇒ B s) ⇒ (∀s. wp prog A s ⇒ wp prog B s)
Proof
  rw[wp_def,hoare_def]
  >> pairarg_tac
  >> qexists ‘k’
  >> gvs[]
QED

Theorem wp_conj:
  ∀A B p. clkfree_q A ∧ clkfree_q B ⇒ (∀s. wp p (λ(r,t). A (r,t) ∧ B (r,t)) s ⇔ wp p A s ∧ wp p B s)
Proof
  rw[wp_def]
  >> iff_tac
  >> rw[]
  >- (qexists ‘k’ >> pairarg_tac >> gvs[])
  >- (qexists ‘k’ >> pairarg_tac >> gvs[])
  >- metis_tac[clkfree_q_conj]
  >> Cases_on ‘k > k'’
  >> rpt (pairarg_tac >> gvs[])
  >> gvs[clkfree_q_def]
  >- (qexists ‘k’
      >> qspecl_then [‘p’, ‘s with clock := k'’, ‘r’, ‘t’, ‘k - k'’]
                     assume_tac evaluate_add_clock_eq
      >> first_x_assum $ (qspecl_then [‘r’, ‘t’, ‘t.clock’, ‘k + t.clock - k'’] assume_tac)
      >> gvs[state_clock_idem])
  >> qexists ‘k'’
  >> qspecl_then [‘p’, ‘s with clock := k’, ‘r'’, ‘t'’, ‘k' - k’]
                 assume_tac evaluate_add_clock_eq
  >> last_x_assum $ (qspecl_then [‘r’, ‘t'’, ‘t'.clock’, ‘k' + t'.clock - k’] assume_tac)
  >> gvs[state_clock_idem]
QED

Theorem wp_disj:
  ∀A B p. clkfree_q A ∧ clkfree_q B ⇒ (∀s. wp p (λ(r,t). A (r,t) ∨ B (r,t)) s ⇔ wp p A s ∨ wp p B s)
Proof
  rw[wp_def]
  >> iff_tac
  >> rw[]
  >- (pairarg_tac >> gvs[]
      >- (disj1_tac >> qexists ‘k’ >> gvs[])
      >- (disj2_tac >> qexists ‘k’ >> gvs[]))
  >- metis_tac[clkfree_q_disj]
  >- (qexists ‘k’ >> pairarg_tac >> gvs[])
  >- metis_tac[clkfree_q_disj]
  >> qexists ‘k’
  >> pairarg_tac
  >> gvs[]
QED

Theorem wp_neg:
  ∀A p. clkfree_q A ⇒ (∀s. wp p (λ(r,t). ¬A (r,t)) s ⇒ ¬wp p A s)
Proof
  rw[wp_def]
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >> Cases_on ‘k > k'’
  >- (qspecl_then [‘p’, ‘s with clock := k'’, ‘r’, ‘t’, ‘k - k'’]
                   assume_tac evaluate_add_clock_eq
      >> elim_cases [‘r = SOME TimeOut’]
      >> gvs[clkfree_q_def]
      >> first_x_assum $ (qspecl_then [‘r’, ‘t’, ‘t.clock’, ‘k + t.clock - k'’] assume_tac)
      >> gvs[state_clock_idem])
  >- (qspecl_then [‘p’, ‘s with clock := k’, ‘r'’, ‘t'’, ‘k' - k’]
                   assume_tac evaluate_add_clock_eq
      >> gvs[clkfree_q_def]
      >> first_x_assum $ (qspecl_then [‘r’, ‘t'’, ‘t'.clock’, ‘k' + t'.clock - k’] assume_tac)
      >> gvs[state_clock_idem])
QED

Theorem wp_skip:
  clkfree_q Q ⇒ (wp Skip Q s ⇔ Q (NONE, s))
Proof
  rw[wp_def,evaluate_def,clkfree_q_def]
  >> assume_tac state_clock_idem
  >> iff_tac
  >> rw[]
  >- (first_x_assum $ (qspecl_then [‘NONE’, ‘s’, ‘k’, ‘s.clock’] assume_tac) >> gvs[])
  >> qexists ‘s.clock’
  >> gvs[]
QED

Theorem wp_dec:
  clkfree_q Q ⇒ (wp (Dec v sh src prog) Q s ⇔ evaluates src s ∧
                                              subst Local v src (wp prog (reset_subst v s Q)) s)
Proof
  rw[wp_def,evaluate_def,clkfree_q_def,evaluates_def,subst_def,reset_subst_def]
  >> iff_tac
  >> rw[]
  >> assume_tac state_clock_idem
  >> assume_tac eval_upd_clock_eq
  >> elim_cases [‘eval s src’]
  >> rpt (pairarg_tac >> gvs[])
  >> rw[]
  >- (first_x_assum $ (qspecl_then [‘r'’,
                                    ‘s' with locals := res_var s'.locals (v,FLOOKUP s.locals v)’,
                                    ‘k1’, ‘k2’] assume_tac)
      >> gvs[])
  >> qexists ‘k’
  >> gvs[]
QED

Theorem wp_assign:
  clkfree_q Q ⇒ (wp (Assign k v src) Q s ⇔ valid_value k v src s ∧
                                           subst k v src (λs. Q (NONE, s)) s)
Proof
  Cases_on ‘k’
  >> rw[wp_def,evaluate_def,clkfree_q_def,valid_value_def,subst_def]
  >> iff_tac
  >> rw[]
  >> assume_tac state_clock_idem
  >> assume_tac eval_upd_clock_eq
  >> elim_cases [‘eval s src’]
  >- elim_cases [‘is_valid_value s.locals v x’]
  >- (elim_cases [‘is_valid_value s.locals v x’]
      >> first_x_assum $ (qspecl_then [‘NONE’, ‘s with locals := s.locals |+ (v,x)’,
                                       ‘k’, ‘s.clock’] assume_tac)
      >> gvs[])
  >- (qexists ‘s.clock’ >> gvs[])
  >- elim_cases [‘is_valid_value s.globals v x’]
  >- (elim_cases [‘is_valid_value s.globals v x’]
      >> first_x_assum $ (qspecl_then [‘NONE’, ‘s with globals := s.globals |+ (v,x)’,
                                       ‘k’, ‘s.clock’] assume_tac)
      >> gvs[])
  >> qexists ‘s.clock’
  >> gvs[]
QED

Theorem wp_store:
  clkfree_q Q ⇒ (wp (Store dest src) Q s ⇔ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                                                      evaluates_to src val s ∧
                                                      addr_in_mem addr val s ∧
                                                      mem_subst addr val (λs. Q (NONE, s)) s)
Proof
  rw[wp_def,evaluate_def,clkfree_q_def,evaluates_to_def,addr_in_mem_def,mem_subst_def]
  >> iff_tac
  >> rw[]
  >> assume_tac state_clock_idem
  >> assume_tac eval_upd_clock_eq
  >> elim_cases [‘eval s src’, ‘eval s dest’]
  >- elim_cases [‘x’]
  >- (elim_cases [‘x'’, ‘w’, ‘mem_stores c (flatten x) s.memaddrs s.memory’]
      >> first_x_assum $ (qspecl_then [‘NONE’, ‘s with memory := x'’,
                                       ‘k’, ‘s.clock’] assume_tac)
      >> gvs[])
  >> qexists ‘s.clock’
  >> gvs[]
QED

Theorem wp_store32:
  clkfree_q Q ⇒ (wp (Store32 dest src) Q s ⇔ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                                                        evaluates_to src (ValWord val) s ∧
                                                        addr_in_mem_32 addr val s ∧
                                                        mem_subst_32 addr val (λs. Q (NONE, s)) s)
Proof
  rw[wp_def,evaluate_def,clkfree_q_def,evaluates_to_def,addr_in_mem_32_def,mem_subst_32_def]
  >> iff_tac
  >> rw[]
  >> assume_tac state_clock_idem
  >> assume_tac eval_upd_clock_eq
  >> elim_cases [‘eval s src’, ‘eval s dest’]
  >- elim_cases [‘x’]
  >- (elim_cases [‘x’, ‘x'’, ‘w’, ‘w'’, ‘mem_store_32 s.memory s.memaddrs s.be c' (w2w c)’]
      >> first_x_assum $ (qspecl_then [‘NONE’, ‘s with memory := x’,
                                       ‘k’, ‘s.clock’] assume_tac)
      >> gvs[])
  >> qexists ‘s.clock’
  >> gvs[]
QED

Theorem wp_storebyte:
  clkfree_q Q ⇒ (wp (StoreByte dest src) Q s ⇔ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                                                          evaluates_to src (ValWord val) s ∧
                                                          addr_in_mem_byte addr val s ∧
                                                          mem_subst_byte addr val (λs. Q (NONE, s)) s)
Proof
  rw[wp_def,evaluate_def,clkfree_q_def,evaluates_to_def,addr_in_mem_byte_def,mem_subst_byte_def]
  >> iff_tac
  >> rw[]
  >> assume_tac state_clock_idem
  >> assume_tac eval_upd_clock_eq
  >> elim_cases [‘eval s src’, ‘eval s dest’]
  >- elim_cases [‘x’]
  >- (elim_cases [‘x’, ‘x'’, ‘w’, ‘w'’, ‘mem_store_byte s.memory s.memaddrs s.be c' (w2w c)’]
      >> first_x_assum $ (qspecl_then [‘NONE’, ‘s with memory := x’,
                                       ‘k’, ‘s.clock’] assume_tac)
      >> gvs[])
  >> qexists ‘s.clock’
  >> gvs[]
QED

Theorem wp_seq:
  clkfree_q Q ⇒ (wp (Seq p1 p2) Q s ⇔ wp p1 (λ(r,t). r = NONE ∧ (wp p2 Q) t) s ∨
                                      wp p1 (λ(r,t). r ≠ NONE ∧ Q (r,t)) s)
Proof
  rw[wp_def,evaluate_def,clkfree_q_def]
  >> iff_tac
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >- (Cases_on ‘res’
      >> gvs[]
      >- (disj1_tac
          >> qspecl_then [‘s with clock := k’, ‘s1’, ‘NONE’, ‘p1’]
                         assume_tac (GEN_ALL evaluate_min_clock)
          >> gvs[]
          >> qexists ‘k' + s1.clock’
          >> rpt (pairarg_tac >> gvs[])
          >> qspecl_then [‘p1’, ‘s with clock := k'’, ‘NONE’, ‘s1 with clock := 0’, ‘s1.clock’]
                         assume_tac evaluate_add_clock_eq
          >> gvs[]
          >> qexists ‘s1.clock’
          >> gvs[state_clock_idem])
      >> disj2_tac
      >> rw[]
      >- (first_x_assum $ (qspecl_then [‘r’, ‘s'’, ‘k1’, ‘k2’] assume_tac) >> gvs[])
      >> qexists ‘k’
      >> gvs[])
  >- (qspecl_then [‘s with clock := k’, ‘t’, ‘NONE’, ‘p1’]
                  assume_tac (GEN_ALL evaluate_min_clock)
      >> gvs[]
      >> qexists ‘k'' + k'’
      >> qspecl_then [‘p1’, ‘s with clock := k''’, ‘NONE’, ‘t with clock := 0’, ‘k'’]
                     assume_tac evaluate_add_clock_eq
      >> gvs[])
  >> qexists ‘k’
  >> gvs[]
QED

Theorem wp_if:
  clkfree_q Q ⇒ (wp (If e c1 c2) Q s ⇔ (evaluates_to_word  e s)             ∧
                                       (evaluates_to_true  e s ⇒ wp c1 Q s) ∧
                                       (evaluates_to_false e s ⇒ wp c2 Q s))
Proof
  rw[wp_def,evaluate_def,evaluates_to_word_def,evaluates_to_true_def,evaluates_to_false_def]
  >> iff_tac
  >> rw[]
  >> assume_tac eval_upd_clock_eq
  >- elim_cases [‘eval s e’, ‘x’, ‘w’]
  >- (qexists ‘k’ >> gvs[])
  >> elim_cases [‘w = 0w’]
  >> qexists ‘k’
  >> gvs[]
QED

Theorem wp_break:
  clkfree_q Q ⇒ (wp Break Q s ⇔ Q (SOME Break,s))
Proof
  rw[wp_def,evaluate_def,clkfree_q_def]
  >> assume_tac state_clock_idem
  >> iff_tac
  >> rw[]
  >- (first_x_assum $ (qspecl_then [‘SOME Break’, ‘s’, ‘k’, ‘s.clock’] assume_tac) >> gvs[])
  >> qexists ‘s.clock’
  >> gvs[]
QED

Theorem wp_continue:
  clkfree_q Q ⇒ (wp Continue Q s ⇔ Q (SOME Continue,s))
Proof
  rw[wp_def,evaluate_def,clkfree_q_def]
  >> assume_tac state_clock_idem
  >> iff_tac
  >> rw[]
  >- (first_x_assum $ (qspecl_then [‘SOME Continue’, ‘s’, ‘k’, ‘s.clock’] assume_tac) >> gvs[])
  >> qexists ‘s.clock’
  >> gvs[]
QED

Theorem wp_raise:
  clkfree_q Q ⇒ (wp (Raise eid e) Q s ⇔ ∃sh val. has_eshape eid sh s ∧
                                                 evaluates_to e val s ∧
                                                 shape_of val = sh ∧
                                                 size_of_shape sh ≤ 32 ∧
                                                 Q (SOME (Exception eid val),empty_locals s))
Proof
  rw[wp_def,evaluate_def,clkfree_q_def,has_eshape_def,evaluates_to_def]
  >> iff_tac
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >> assume_tac state_clock_idem
  >> assume_tac eval_upd_clock_eq
  >- (elim_cases [‘FLOOKUP s.eshapes eid’, ‘eval s e’, ‘shape_of x' = x’,
                  ‘size_of_shape (shape_of x') ≤ 32’]
      >> first_x_assum $ (qspecl_then [‘SOME (Exception eid x')’, ‘s with locals := FEMPTY’,
                                       ‘s.clock’, ‘k’] assume_tac)
      >> gvs[empty_locals_def])
  >> qexists ‘s.clock’
  >> gvs[]
QED

Theorem wp_return:
  clkfree_q Q ⇒ (wp (Return e) Q s ⇔ ∃val. evaluates_to e val s ∧
                                           size_of_shape (shape_of val) ≤ 32 ∧
                                           Q (SOME (Return val),empty_locals s))
Proof
  rw[wp_def,evaluate_def,clkfree_q_def,evaluates_to_def]
  >> iff_tac
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >> assume_tac state_clock_idem
  >> assume_tac eval_upd_clock_eq
  >- (elim_cases [‘eval s e’, ‘size_of_shape (shape_of x) ≤ 32’]
      >> first_x_assum $ (qspecl_then [‘SOME (Return x)’, ‘s with locals := FEMPTY’,
                                       ‘s.clock’, ‘k’] assume_tac)
      >> gvs[empty_locals_def])
  >> qexists ‘s.clock’
  >> gvs[]
QED

Theorem wp_annot:
  clkfree_q Q ⇒ (wp (Annot a b) Q s ⇔ Q (NONE,s))
Proof
  rw[wp_def,evaluate_def,clkfree_q_def]
  >> assume_tac state_clock_idem
  >> iff_tac
  >> rw[]
  >- (first_x_assum $ (qspecl_then [‘NONE’, ‘s’, ‘k’, ‘s.clock’] assume_tac) >> gvs[])
  >> qexists ‘s.clock’
  >> gvs[]
QED
