(***********************************************************************
 * Definitions and Proofs about Predicates on Pancake States           *
 ***********************************************************************)

Theory panPredicate
Ancestors panLang panSem
          list[qualified]
Libs BasicProvers

Theorem shape_of_val:
  ∀w : 'a word_lab. shape_of (Val w) = One
Proof
  rw[]
  >> qsuff_tac ‘∃w'. w = Word w'’
  >- (rw[] >> rw[shape_of_def])
  >> Cases_on ‘w’
  >> gvs[]
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
Definition evaluates_shape_def:
  evaluates_shape e sh s ⇔ ∃v. eval s e = SOME v ∧ shape_of v = sh
End

Definition evaluates_to_def:
  evaluates_to e v s ⇔ eval s e = SOME v
End

Theorem evaluates_to_const:
  ∀s. evaluates_to (Const val) (ValWord val) s
Proof
  rw[evaluates_to_def,eval_def]
QED

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
  >> Cases_on ‘w = 0w’
  >> gvs[]
QED

Theorem evaluates_to_word_contradict:
  ∀e s. (evaluates_to_true  e s ⇒ ¬evaluates_to_false e s) ∧
        (evaluates_to_false e s ⇒ ¬evaluates_to_true  e s)
Proof
  rw[evaluates_to_true_def,evaluates_to_false_def]
  >> gvs[]
QED

Definition var_eq_def:
  var_eq k v e s ⇔ case k of
                   | Local  => FLOOKUP s.locals  v = eval s e
                   | Global => FLOOKUP s.globals v = eval s e
End
        
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
