(***********************************************************************
 * Definitions and Proofs about Predicates on Pancake States           *
 ***********************************************************************)

Theory panPredicate
Ancestors panSem

fun elim_cases xs = EVERY (map (fn x => Cases_on x >> gvs[]) xs);

Definition evaluates_def:
  evaluates e s ⇔ ∃v. eval s e = SOME v
End

Definition evaluates_to_def:
  evaluates_to e v s ⇔ eval s e = SOME v
End

Definition evaluates_to_word_def:
  evaluates_to_word e s ⇔ ∃w. eval s e = SOME (ValWord w)
End

Definition evaluates_to_true_def:
  evaluates_to_true e s ⇔ ∃w. eval s e = SOME (ValWord w) ∧ w ≠ 0w
End

Definition evaluates_to_false_def:
  evaluates_to_false e s ⇔ ∃w. eval s e = SOME (ValWord w) ∧ w = 0w
End

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

Definition reset_local_subst_def:
  reset_local_subst v s Q (r,t) ⇔ Q (r,t with locals := res_var t.locals (v,FLOOKUP s.locals v))
End

Definition knows_eid_def:
  knows_eshape eid s ⇔ ∃sh. FLOOKUP s.eshapes eid = SOME sh
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
