(***********************************************************************
 * Definitions and Proofs about Predicates on Pancake States           *
 ***********************************************************************)

Theory panPredicate
Ancestors panReducedSem panReducedProps

fun elim_cases xs = EVERY (map (fn x => Cases_on x >> gvs[]) xs);

Definition clkfree_p_def:
  clkfree_p P ⇔ ∀s k1 k2. P (s with clock := k1) ⇔ P (s with clock := k2)
End

Theorem clkfree_p_cases:
  clkfree_p (λs. T) ∧ clkfree_p (λs. F)
Proof
  rw[clkfree_p_def]
QED

Definition clkfree_q_def:
  clkfree_q Q ⇔ ∀r s k1 k2. Q (r,s with clock := k1) ⇔ Q (r,s with clock := k2)
End

Theorem clkfree_q_cases:
  clkfree_q (λs. T) ∧ clkfree_q (λs. F) ∧ ∀R. clkfree_q (λ(r,t). R r)
Proof
  rw[clkfree_q_def]
QED

Theorem clkfree_pq:
  ∀(P : 'a state -> bool). clkfree_p P ⇒ clkfree_q (λ(r : 'a result option,t). P t) ∧
                                         ∀(R : 'a result option -> bool). clkfree_q (λ(r,t). R r ∧ P t)
Proof
  rw[clkfree_p_def,clkfree_q_def]
  >> first_x_assum $ (qspecl_then [‘s’, ‘k1’, ‘k2’] assume_tac)
  >> gvs[]
QED

Theorem clkfree_qp:
  ∀Q res. clkfree_q Q ⇒ clkfree_p (λs. Q (res,s))
Proof
  rw[clkfree_p_def,clkfree_q_def]
QED

Theorem clkfree_qqn:
  ∀Q res. clkfree_q Q ⇒ clkfree_q (λ(r,t). r ≠ res ∧ Q (r,t))
Proof
  rw[clkfree_p_def,clkfree_q_def]
  >> first_x_assum $ (qspecl_then [‘r’, ‘s’, ‘k1’, ‘k2’] assume_tac)
  >> gvs[]
QED

Theorem clkfree_qnif:
  ∀Q M res. clkfree_q Q ∧ clkfree_p M ⇒
            clkfree_q (λ(r,t). if r ≠ res then Q (r,t) else M t)
Proof
  rw[clkfree_q_def,clkfree_p_def]
  >> iff_tac
  >> rw[]
  >> metis_tac[]
QED

Theorem clkfree_p_conj:
  ∀P R. clkfree_p P ∧ clkfree_p R ⇒ clkfree_p (λs. P s ∧ R s)
Proof
  rw[clkfree_p_def]
  >> rpt (first_x_assum $ (qspecl_then [‘s’, ‘k1’, ‘k2’] assume_tac))
  >> gvs[]
QED

Theorem clkfree_p_disj:
  ∀P R. clkfree_p P ∧ clkfree_p R ⇒ clkfree_p (λs. P s ∨ R s)
Proof
  rw[clkfree_p_def]
  >> rpt (first_x_assum $ (qspecl_then [‘s’, ‘k1’, ‘k2’] assume_tac))
  >> gvs[]
QED

Theorem clkfree_p_neg:
  ∀P. clkfree_p P ⇒ clkfree_p (λs. ¬P s)
Proof
  rw[clkfree_p_def]
QED

Theorem clkfree_p_monotonic:
  ∀P P'. (∀s. P s ⇔ P' s) ⇒ (clkfree_p P ⇔ clkfree_p P')
Proof
  rw[clkfree_p_def]
QED

Theorem clkfree_q_conj:
  ∀(Q : 'a result option # 'a state -> bool) (R : 'a result option # 'a state -> bool).
  clkfree_q Q ∧ clkfree_q R ⇒ clkfree_q (λ(r,t). Q (r,t) ∧ R (r,t))
Proof
  rw[clkfree_q_def]
  >> rpt (first_x_assum $ (qspecl_then [‘r’, ‘s’, ‘k1’, ‘k2’] assume_tac))
  >> gvs[]
QED

Theorem clkfree_q_disj:
  ∀(Q : 'a result option # 'a state -> bool) (R : 'a result option # 'a state -> bool).
  clkfree_q Q ∧ clkfree_q R ⇒ clkfree_q (λ(r,t). Q (r,t) ∨ R (r,t))
Proof
  rw[clkfree_q_def]
  >> rpt (first_x_assum $ (qspecl_then [‘r’, ‘s’, ‘k1’, ‘k2’] assume_tac))
  >> gvs[]
QED

Theorem clkfree_q_neg:
  ∀Q. clkfree_q Q ⇒ clkfree_q (λ(r,t). ¬Q (r,t))
Proof
  rw[clkfree_q_def]
QED

Theorem clkfree_q_monotonic:
  ∀Q Q'. (∀r. Q r ⇔ Q' r) ⇒ (clkfree_q Q ⇔ clkfree_q Q')
Proof
  rw[clkfree_q_def]
QED

Definition varfree_p_def:
  varfree_p v P ⇔ (∀s val. P s ⇒ P (s with locals := s.locals |+ (v,val)) ∧
                                 P (s with locals := s.locals \\ v))
End

Definition varfree_q_def:
  varfree_q v Q ⇔ (∀r t val. Q (r,t) ⇒ Q (r,t with locals := t.locals |+ (v,val)) ∧
                                       Q (r,t with locals := t.locals \\ v))
End

Definition evaluates_def:
  evaluates e s ⇔ ∃v. eval s e = SOME v
End

Theorem clkfree_evaluates:
  ∀e. clkfree_p (λs. evaluates e s) ∧
      clkfree_p (evaluates e)
Proof
  rw[clkfree_p_def,evaluates_def,eval_upd_clock_eq]
QED

Definition evaluates_to_def:
  evaluates_to e v s ⇔ eval s e = SOME v
End

Theorem clkfree_evaluates_to:
  ∀e v. clkfree_p (λs. evaluates_to e v s) ∧
        clkfree_p (evaluates_to e v)
Proof
  rw[clkfree_p_def,evaluates_to_def,eval_upd_clock_eq]
QED

Definition evaluates_to_word_def:
  evaluates_to_word e s ⇔ ∃w. eval s e = SOME (ValWord w)
End

Theorem clkfree_evaluates_to_word:
  ∀e. clkfree_p (λs. evaluates_to_word e s) ∧
      clkfree_p (evaluates_to_word e)
Proof
  rw[clkfree_p_def,evaluates_to_word_def,eval_upd_clock_eq]
QED

Definition evaluates_to_true_def:
  evaluates_to_true e s ⇔ ∃w. eval s e = SOME (ValWord w) ∧ w ≠ 0w
End

Theorem clkfree_evaluates_to_true:
  ∀e. clkfree_p (λs. evaluates_to_true e s) ∧
      clkfree_p (evaluates_to_true e)
Proof
  rw[clkfree_p_def,evaluates_to_true_def,eval_upd_clock_eq]
QED

Definition evaluates_to_false_def:
  evaluates_to_false e s ⇔ ∃w. eval s e = SOME (ValWord w) ∧ w = 0w
End

Theorem clkfree_evaluates_to_false:
  ∀e. clkfree_p (λs. evaluates_to_false e s) ∧
      clkfree_p (evaluates_to_false e)
Proof
  rw[clkfree_p_def,evaluates_to_false_def,eval_upd_clock_eq]
QED

Theorem evaluates_to_word_lem:
  ∀e s. evaluates_to_word e s ⇒ evaluates_to_true e s ∨ evaluates_to_false e s
Proof
  rw[evaluates_to_word_def,evaluates_to_true_def,evaluates_to_false_def]
  >> elim_cases [‘w = 0w’]
QED

Theorem evaluates_to_word_contradict:
  ∀e s. evaluates_to_true  e s ⇒ ¬evaluates_to_false e s ∧
        evaluates_to_false e s ⇒ ¬evaluates_to_true  e s
Proof
  rw[evaluates_to_true_def,evaluates_to_false_def]
QED

Definition valid_value_def:
  valid_value k v e s ⇔ ∃value. eval s e = SOME value ∧
                                case k of
                                | Local  => is_valid_value s.locals  v value
                                | Global => is_valid_value s.globals v value
End

Definition subst_def:
  subst k v e P s ⇔ ∃value. eval s e = SOME value ∧
                                   case k of
                                   | Local  => P (s with locals  := s.locals  |+ (v,value))
                                   | Global => P (s with globals := s.globals |+ (v,value))
End

Definition reset_subst_def:
  reset_subst v s Q (r,t) ⇔ Q (r,t with locals := res_var t.locals (v,FLOOKUP s.locals v))
End

Definition has_eshape_def:
  has_eshape eid sh s ⇔ FLOOKUP s.eshapes eid = SOME sh
End

Definition addr_in_mem_def:
  addr_in_mem a v s ⇔ ∃m. mem_stores a (flatten v) s.memaddrs s.memory = SOME m
End

Definition mem_subst_def:
  mem_subst a v P s ⇔ ∃m. mem_stores a (flatten v) s.memaddrs s.memory = SOME m ∧
                          P (s with memory := m)
End

Definition addr_in_mem_32_def:
  addr_in_mem_32 a v s ⇔ ∃m. mem_store_32 s.memory s.memaddrs s.be a (w2w v) = SOME m
End

Definition mem_subst_32_def:
  mem_subst_32 a v P s ⇔ ∃m. mem_store_32 s.memory s.memaddrs s.be a (w2w v) = SOME m ∧
                             P (s with memory := m)
End

Definition addr_in_mem_byte_def:
  addr_in_mem_byte a v s ⇔ ∃m. mem_store_byte s.memory s.memaddrs s.be a (w2w v) = SOME m
End

Definition mem_subst_byte_def:
  mem_subst_byte a v P s ⇔ ∃m. mem_store_byte s.memory s.memaddrs s.be a (w2w v) = SOME m ∧
                               P (s with memory := m)
End
