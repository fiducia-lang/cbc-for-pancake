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



Datatype:
  Contract = HoareC    (('a, 'ffi) state -> bool) (('a result option # ('a, 'ffi) state) -> bool)
           | SeqC      Contract Contract
           | IfC       ('a panLang$exp) Contract Contract
           | PanC      ('a panLang$prog)
           | DCC
End

Definition sat_def:
  sat contr prog = case (contr, prog) of
                   | ((HoareC P Q), prog)            => hoare P prog Q
                   | ((SeqC c1 c2), (Seq p1 p2))     => sat c1 p1 ∧ sat c2 p2
                   | ((IfC l c1 c2), (If r p1 p2))   => l = r ∧ sat c1 p1 ∧ sat c2 p2
                   | ((PanC l), r)                   => l = r
                   | (DCC, _)                        => T
                   | _                               => F
End

Definition refine_def:
  refine c1 c2 ⇔ ∀prog. sat c2 prog ⇒ sat c1 prog
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
  rw[refine_def,sat_def,hoare_def,clkfree_q_def]
  >> first_x_assum $ (qspec_then ‘s’ assume_tac)
  >> gvs[]
  >> qexists ‘k’
  >> pairarg_tac
  >> gvs[]
QED

Theorem weaken_precondition_refinement_rule:
  clkfree_p P ∧ (∀s. P s ⇒ P' s) ⇒ refine (HoareC P Q) (HoareC P' Q)
Proof
  rw[refine_def,sat_def,hoare_def,clkfree_p_def]
  >> first_x_assum $ (qspec_then ‘s’ assume_tac)
  >> gvs[]
  >> qexists ‘k’
  >> gvs[]
QED

Theorem skip_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧ (∀s. P s ⇒ Q (NONE,s)) ⇒ refine (HoareC P Q) (PanC Skip)
Proof
  rw[refine_def,sat_def]
  >> qspecl_then [‘P’, ‘Skip’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> gvs[wp_skip]
QED

Theorem assign_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧ (∀s. P s ⇒ valid_value k v src s ∧
                                         subst k v src (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (Assign k v src))
Proof
  rw[refine_def,sat_def]
  >> qspecl_then [‘P’, ‘Assign k v src’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> gvs[wp_assign]
QED

Theorem store_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧ (∀s. P s ⇒ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                                                    evaluates_to src val s ∧
                                                    addr_in_mem addr val s ∧
                                                    mem_subst addr val (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (Store dest src))
Proof
  rw[refine_def,sat_def]
  >> qspecl_then [‘P’, ‘Store dest src’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> gvs[wp_store]
QED

Theorem store32_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧ (∀s. P s ⇒ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                                                    evaluates_to src (ValWord val) s ∧
                                                    addr_in_mem_32 addr val s ∧
                                                    mem_subst_32 addr val (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (Store32 dest src))
Proof
  rw[refine_def,sat_def]
  >> qspecl_then [‘P’, ‘Store32 dest src’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> gvs[wp_store32]
QED

Theorem storebyte_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧ (∀s. P s ⇒ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                                                    evaluates_to src (ValWord val) s ∧
                                                    addr_in_mem_byte addr val s ∧
                                                    mem_subst_byte addr val (λs. Q (NONE,s)) s) ⇒
  refine (HoareC P Q) (PanC (StoreByte dest src))
Proof
  rw[refine_def,sat_def]
  >> qspecl_then [‘P’, ‘StoreByte dest src’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> gvs[wp_storebyte]
QED

Theorem seq_refinement_rule_pan:
  refine (SeqC (PanC l) (PanC r)) (PanC (Seq l r))
Proof
  rw[refine_def,sat_def]
QED

Theorem seq_refinement_rule_fst:
  clkfree_p P ∧ clkfree_q Q ⇒
  refine (HoareC P Q) (SeqC (HoareC P (λ(r,t). r ≠ NONE ∧ Q (r,t))) DCC)
Proof
  rw[refine_def,sat_def]
  >> elim_cases [‘prog’]
  >> qspecl_then [‘P’, ‘p’, ‘(λ(r,t). r ≠ NONE ∧ Q (r,t))’] assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘P’, ‘Seq p p0’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘Q’, ‘NONE’] assume_tac clkfree_qqn
  >> gvs[wp_seq]
QED

Theorem seq_refinement_rule_snd:
  clkfree_p P ∧ clkfree_q Q ∧ clkfree_p M ⇒
  refine (HoareC P Q) (SeqC (HoareC P (λ(r,t). r = NONE ∧ M t)) (HoareC M Q))
Proof
  rw[refine_def,sat_def]
  >> elim_cases [‘prog’]
  >> qspecl_then [‘P’, ‘p’, ‘(λ(r,t). r = NONE ∧ M t)’] assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘M’, ‘p0’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘P’, ‘Seq p p0’, ‘Q’] assume_tac wp_is_weakest_precondition
  >> ‘clkfree_p (wp p0 Q)’ by (metis_tac[wp_clkfree])
  >> qspecl_then [‘wp p0 Q’, ‘NONE’] assume_tac clkfree_pq
  >> qspecl_then [‘M’, ‘NONE’] assume_tac clkfree_pq
  >> qspecl_then [‘M’, ‘wp p0 Q’, ‘NONE’] assume_tac pq_monotonic
  >> qspecl_then [‘λ(r,t). r = NONE ∧ M t’, ‘λ(r,t). r = NONE ∧ wp p0 Q t’, ‘p’]
                 assume_tac wp_monotonic
  >> gvs[wp_seq]
QED

Theorem if_refinement_rule_pan:
  refine (IfC e (PanC l) (PanC r)) (PanC (If e l r))
Proof
  rw[refine_def,sat_def]
QED

Theorem if_refinement_rule:
  clkfree_p P ∧ clkfree_q Q ∧ (∀s. P s ⇒ evaluates_to_word e s) ⇒
  refine (HoareC P Q) (IfC e (HoareC (λs. P s ∧ evaluates_to_true  e s) Q)
                             (HoareC (λs. P s ∧ evaluates_to_false e s) Q))
Proof
  rw[refine_def,sat_def]
  >> elim_cases [‘prog’]
  >> qspecl_then [‘λs. P s ∧ evaluates_to_true e s’, ‘p’, ‘Q’]
                 assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘λs. P s ∧ evaluates_to_false e s’, ‘p0’, ‘Q’]
                 assume_tac wp_is_weakest_precondition
  >> qspecl_then [‘P’, ‘If e p p0’, ‘Q’]
                 assume_tac wp_is_weakest_precondition
  >> ‘clkfree_p (λs. P s ∧ evaluates_to_true e s)’ by
     (metis_tac[clkfree_p_conj,clkfree_evaluates_to_true])
  >> ‘clkfree_p (λs. P s ∧ evaluates_to_false e s)’ by
     (metis_tac[clkfree_p_conj,clkfree_evaluates_to_false])
  >> gvs[wp_if]
QED



Theorem dcc_refinement_rule:
  refine DCC (PanC prog)
Proof
  rw[refine_def,sat_def]
QED
