(***********************************************************************
 * Proofs about Weakest Preconditions of Pancake Statements            *
 ***********************************************************************)

Theory panWeakestPrecondition
Ancestors panSem panProps panPredicate
Libs BasicProvers

Definition hoare_def:
  hoare P prog Q ⇔ ∀s. P s ⇒ let (r,t) = evaluate (prog,s)
                             in r ≠ SOME Error ∧ Q (r,t) ∨ r = SOME TimeOut
End

Theorem hoare_monotonic_p:
  ∀P P' prog Q. (∀s. P s ⇔ P' s) ⇒ (hoare P prog Q ⇔ hoare P' prog Q)
Proof
  rw[hoare_def]
QED

Definition wp_def:
  wp prog Q s ⇔ let (r,t) = evaluate (prog,s)
                    in r ≠ SOME Error ∧ Q (r,t) ∨ r = SOME TimeOut
End

Theorem wp_is_weakest_precondition:
  ∀P prog Q. hoare (wp prog Q) prog Q ∧ (hoare P prog Q ⇔ (∀s. P s ⇒ wp prog Q s))
Proof
  rw[hoare_def,wp_def]
QED

Theorem wp_monotonic:
  ∀A B prog. (∀s. A s ⇒ B s) ⇒ (∀s. wp prog A s ⇒ wp prog B s)
Proof
  rw[wp_def,hoare_def]
  >> pairarg_tac
  >> gvs[]
QED

Theorem wp_conj:
  ∀A B p s. wp p (λ(r,t). A (r,t) ∧ B (r,t)) s ⇔ wp p A s ∧ wp p B s
Proof
  rw[wp_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[]
QED

Theorem wp_disj:
  ∀A B p s. wp p (λ(r,t). A (r,t) ∨ B (r,t)) s ⇔ wp p A s ∨ wp p B s
Proof
  rw[wp_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[]
QED

Theorem wp_nif:
  ∀Q M p res s. wp p (λ(r,t). if r ≠ res then Q (r,t) else M t) s ⇔
                wp p (λ(r,t). r ≠ res ∧ Q (r,t)) s ∨ wp p (λ(r,t). r = res ∧ M t) s
Proof
  rw[wp_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[]
  >> Cases_on ‘r ≠ res’
  >> gvs[]
QED
        
Theorem wp_skip:
  wp Skip Q s ⇔ Q (NONE, s)
Proof
  rw[wp_def,evaluate_def]
QED

Theorem wp_dec:
  wp (Dec v sh src prog) Q s ⇔ evaluates src s ∧
                               subst Local v src (wp prog (reset_subst v s Q)) s
Proof
  rw[wp_def,evaluate_def,evaluates_def,subst_def,reset_subst_def]
  >> iff_tac
  >> rw[]
  >> rpt(pairarg_tac >> gvs[])
  >> FULL_CASE_TAC
  >> gvs[]
  >> pairarg_tac
  >> gvs[]
QED

Theorem wp_assign:
  wp (Assign k v src) Q s ⇔ valid_value k v src s ∧
                            subst k v src (λs. Q (NONE, s)) s
Proof
  Cases_on ‘k’
  >> rw[wp_def,evaluate_def,valid_value_def,subst_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[]
  >> rpt(FULL_CASE_TAC >> gvs[])
QED

Theorem wp_store:
  wp (Store dest src) Q s ⇔ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                                       evaluates_to src val s ∧
                                       addr_in_mem addr val s ∧
                                       mem_subst addr val (λs. Q (NONE, s)) s
Proof
  rw[wp_def,evaluate_def,evaluates_to_def,addr_in_mem_def,mem_subst_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[]
  >> rpt (FULL_CASE_TAC >> gvs[])
QED

Theorem wp_store32:
  wp (Store32 dest src) Q s ⇔ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                                         evaluates_to src (ValWord val) s ∧
                                         addr_in_mem_32 addr val s ∧
                                         mem_subst_32 addr val (λs. Q (NONE, s)) s
Proof
  rw[wp_def,evaluate_def,evaluates_to_def,addr_in_mem_32_def,mem_subst_32_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[]
  >> rpt (FULL_CASE_TAC >> gvs[])
QED

Theorem wp_storebyte:
  wp (StoreByte dest src) Q s ⇔ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                                           evaluates_to src (ValWord val) s ∧
                                           addr_in_mem_byte addr val s ∧
                                           mem_subst_byte addr val (λs. Q (NONE, s)) s
Proof
  rw[wp_def,evaluate_def,evaluates_to_def,addr_in_mem_byte_def,mem_subst_byte_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[]
  >> rpt (FULL_CASE_TAC >> gvs[])
QED

Theorem wp_seq:
  wp (Seq p1 p2) Q s ⇔ wp p1 (λ(r,t). r = NONE ∧ (wp p2 Q) t) s ∨
                       wp p1 (λ(r,t). r ≠ NONE ∧ Q (r,t)) s
Proof
  rw[wp_def,evaluate_def]
  >> iff_tac
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >> FULL_CASE_TAC
  >> gvs[]
QED

Theorem wp_if:
  wp (If e c1 c2) Q s ⇔ (evaluates_to_word  e s)             ∧
                        (evaluates_to_true  e s ⇒ wp c1 Q s) ∧
                        (evaluates_to_false e s ⇒ wp c2 Q s)
Proof
  rw[wp_def,evaluate_def,evaluates_to_word_def,evaluates_to_true_def,evaluates_to_false_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[]
  >> rpt (FULL_CASE_TAC >> gvs[])
QED

Theorem wp_break:
  wp Break Q s ⇔ Q (SOME Break,s)
Proof
  rw[wp_def,evaluate_def]
QED

Theorem wp_continue:
  wp Continue Q s ⇔ Q (SOME Continue,s)
Proof
  rw[wp_def,evaluate_def]
QED

Theorem wp_raise:
  wp (Raise eid e) Q s ⇔ ∃sh val. has_eshape eid sh s ∧
                                  evaluates_to e val s ∧
                                  shape_of val = sh ∧
                                  size_of_shape sh ≤ 32 ∧
                                  Q (SOME (Exception eid val),empty_locals s)
Proof
  rw[wp_def,evaluate_def,has_eshape_def,evaluates_to_def]
  >> iff_tac
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >> rpt (FULL_CASE_TAC >> gvs[])
QED

Theorem wp_tailcall:
  wp (TailCall fname argexps) Q s ⇔ ∃args p lcls. OPT_MMAP (eval s) argexps = SOME args ∧
                                                  lookup_code s.code fname args = SOME (p,lcls) ∧
                                                  (s.clock = 0 ∨
                                                   wp p (λ(r,t). r ≠ SOME Continue ∧
                                                                 r ≠ SOME Break ∧
                                                                 r ≠ NONE ∧
                                                                 Q(r,empty_locals t))
                                                        (dec_clock s with locals := lcls))
Proof
  rw[wp_def,evaluate_def]
  >> iff_tac
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >> rpt (FULL_CASE_TAC >> gvs[])
QED
 
Theorem wp_assigncall:
  wp (AssignCall (k,v) handler fname argexps) Q s ⇔
  ∃args p lcls. OPT_MMAP (eval s) argexps = SOME args ∧
                lookup_code s.code fname args = SOME (p,lcls) ∧
                (s.clock = 0 ∨
                 wp p (λ(r,t). case r of
                               | SOME (Return rv)         => is_valid_value (case k of Local => s.locals | Global => s.globals) v rv ∧
                                                             Q (NONE,set_kvar k v rv (t with locals := s.locals))
                               | SOME (Exception eid exn) => (case handler of
                                                              | NONE                => Q (SOME (Exception eid exn),empty_locals t)
                                                              | SOME (eid',evar,hp) => if eid = eid' then
                                                                                         ∃sh. FLOOKUP s.eshapes eid = SOME sh ∧
                                                                                              shape_of exn = sh ∧
                                                                                              is_valid_value s.locals evar exn ∧
                                                                                              wp hp Q (set_var evar exn (t with locals := s.locals))
                                                                                       else
                                                                                         Q (SOME (Exception eid exn),empty_locals t))
                               | SOME (FinalFFI f)        => Q (SOME (FinalFFI f),empty_locals t)
                               | _ => F) (dec_clock s with locals := lcls))
Proof
  rw[wp_def,evaluate_def]
  >> iff_tac
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >> rpt (FULL_CASE_TAC >> gvs[])
QED

Theorem wp_standalonecall:
  wp (StandAloneCall handler fname argexps) Q s ⇔
  ∃args p lcls. OPT_MMAP (eval s) argexps = SOME args ∧
                lookup_code s.code fname args = SOME (p,lcls) ∧
                (s.clock = 0 ∨
                 wp p (λ(r,t). case r of
                               | SOME (Return _)          => Q (NONE,t with locals := s.locals)
                               | SOME (Exception eid exn) => (case handler of
                                                              | NONE                => Q (SOME (Exception eid exn),empty_locals t)
                                                              | SOME (eid',evar,hp) => if eid = eid' then
                                                                                         ∃sh. FLOOKUP s.eshapes eid = SOME sh ∧
                                                                                              shape_of exn = sh ∧
                                                                                              is_valid_value s.locals evar exn ∧
                                                                                              wp hp Q (set_var evar exn (t with locals := s.locals))
                                                                                       else
                                                                                         Q (SOME (Exception eid exn),empty_locals t))
                               | SOME (FinalFFI f)        => Q (SOME (FinalFFI f),empty_locals t)
                               | _                        => F) (dec_clock s with locals := lcls))
Proof
  rw[wp_def,evaluate_def]
  >> iff_tac
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >> rpt (FULL_CASE_TAC >> gvs[])
QED

Theorem wp_deccall:
  wp (DecCall v sh fname argexps p1) Q s ⇔
  ∃args p lcls. OPT_MMAP (eval s) argexps = SOME args ∧
                lookup_code s.code fname args = SOME (p,lcls) ∧
                (s.clock = 0 ∨
                 wp p (λ(r,t). case r of
                               | SOME (Return rv)         => shape_of rv = sh ∧ wp p1 (reset_subst v s Q) (set_var v rv (t with locals := s.locals))
                               | SOME (Exception eid exn) => Q (SOME (Exception eid exn),empty_locals t)
                               | SOME (FinalFFI f)        => Q (SOME (FinalFFI f),empty_locals t)
                               | _                        => F) (dec_clock s with locals := lcls))
Proof
  rw[wp_def,evaluate_def]
  >> iff_tac
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >> rpt (FULL_CASE_TAC >> gvs[reset_subst_def])
  >> rpt (pairarg_tac >> gvs[])
QED     
        
Theorem wp_return:
  wp (Return e) Q s ⇔ ∃val. evaluates_to e val s ∧
                            size_of_shape (shape_of val) ≤ 32 ∧
                            Q (SOME (Return val),empty_locals s)
Proof
  rw[wp_def,evaluate_def,evaluates_to_def]
  >> iff_tac
  >> rw[]
  >> rpt (pairarg_tac >> gvs[])
  >> rpt (FULL_CASE_TAC >> gvs[])
QED

Theorem wp_annot:
  wp (Annot a b) Q s ⇔ Q (NONE,s)
Proof
  rw[wp_def,evaluate_def]
QED
