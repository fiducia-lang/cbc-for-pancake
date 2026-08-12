(***********************************************************************
 * Definitions and Proofs about Predicates on Pancake States           *
 ***********************************************************************)

Theory panPredicate
Ancestors panLang panSem
          list[qualified]
Libs BasicProvers Parse[qualified]

local open OpenTheoryMap
  val ns = ["PanPredicate"]
in
  fun ot0 x y = OpenTheory_const_name{const={Thy="panPredicate",Name=x},name=(ns,y)}
  fun ot x = ot0 x x
end 
     
Definition implies_everywhere_def[simp]:
  $IMPLIES_EVERYWHERE P Q ⇔ ∀s. P s ⇒ Q s
End

val _ = set_fixity "IMPLIES_EVERYWHERE" (Infix(NONASSOC, 450));
val _ = Parse.Unicode.unicode_version {u = "\226\135\155", tmnm = "IMPLIES_EVERYWHERE"};
val _ = TeX_notation {hol = "IMPLIES_EVERYWHERE", TeX = ("\\ensuremath{\\Rrightarrow}", 1)}
val _ = TeX_notation {hol = "\226\135\155", TeX = ("\\ensuremath{\\Rrightarrow}", 1)}
val _ = ot0 "IMPLIES_EVERYWHERE" "implies_everywhere"

Theorem shape_of_val[simp]:
  ∀w. shape_of (Val w) = One
Proof
  rw[]
  >> ‘∃w'. w = Word w'’ suffices_by (rw[] >> rw[shape_of_def])
  >> Cases_on ‘w’
  >> gvs[]
QED

Definition unboxvw_def[simp]:
  unboxvw (ValWord w) = w
End

Definition the_eval_def:
  the_eval e s = THE (eval s e)
End

Definition the_eval_vw_def:
  the_eval_vw e s = unboxvw (the_eval e s)
End

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

Theorem evaluates_const[simp]:
  ∀s. evaluates (Const val) s
Proof
  gvs[evaluates_def,eval_def]
QED

Definition evaluates_shape_def:
  evaluates_shape e sh s ⇔ ∃v. eval s e = SOME v ∧ shape_of v = sh
End

Definition evaluates_to_def:
  evaluates_to e v s ⇔ eval s e = SOME v
End

Theorem evaluates_to_const[simp]:
  ∀s. evaluates_to (Const val) (ValWord val) s
Proof
  rw[evaluates_to_def,eval_def]
QED

Definition evaluates_to_word_def:
  evaluates_to_word e s ⇔ ∃w. eval s e = SOME (ValWord w)
End

Theorem evaluates_to_word_const[simp]:
  ∀s. evaluates_to_word (Const val) s
Proof
  rw[evaluates_to_word_def,eval_def]
QED

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

Definition has_kvar_vw_def:
  has_kvar_vw vk v s ⇔ ∃w. lookup_kvar s vk v = SOME (ValWord w)
End

Theorem has_kvar_vw_ffi_eq:
  ∀vk v s ffi. has_kvar_vw vk v (s with ffi := ffi) ⇔ has_kvar_vw vk v s
Proof
  rw[has_kvar_vw_def,lookup_kvar_def]
QED
        
Definition in_sh_memaddrs_def:
  in_sh_memaddrs addr s ⇔ s.sh_memaddrs (addr s)
End
        
Definition var_eq_def:
  var_eq k v e s ⇔ case k of
                   | Local  => FLOOKUP s.locals  v = eval s e
                   | Global => FLOOKUP s.globals v = eval s e
End
        
Definition valid_value_def:
  valid_value k v e s ⇔ let value = THE (eval s e) in
                        case k of
                        | Local  => is_valid_value s.locals  v value
                        | Global => is_valid_value s.globals v value
End

Definition subst_def:
  subst k v e P s ⇔ let value = THE (eval s e) in
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
  addr_in_mem a v s ⇔ IS_SOME (mem_stores (a s) (flatten (v s)) s.memaddrs s.memory)
End

Definition mem_subst_def:
  mem_subst a v P s ⇔ let m = THE (mem_stores (a s) (flatten (v s)) s.memaddrs s.memory) in
                      P (s with memory := m)
End

Definition addr_in_mem32_def:
  addr_in_mem32 a s ⇔ aligned 2 (a s) ∧ byte_align (a s) ∈ s.memaddrs
End

Definition mem_subst32_def:
  mem_subst32 a v P s ⇔ let m = THE (mem_store_32 s.memory s.memaddrs s.be (a s) (w2w (v s))) in
                         P (s with memory := m)
End

Definition addr_in_mem8_def:
  addr_in_mem8 a s ⇔ byte_align (a s) ∈ s.memaddrs
End

Definition mem_subst8_def:
  mem_subst8 a v P s ⇔ let m = THE (mem_store_byte s.memory s.memaddrs s.be (a s) (w2w (v s))) in
                           P (s with memory := m)
End
