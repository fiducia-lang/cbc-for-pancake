(***********************************************************************
 * Proofs of Refinement Rules for Pancake Statements                   *
 ***********************************************************************)

Theory panRefinement
Ancestors panSem panProps panPredicate panWeakestPrecondition
          finite_map[qualified]
Libs BasicProvers

fun elim_cases xs = EVERY (map (fn x => Cases_on x >> gvs[]) xs);

local open OpenTheoryMap
  val ns = ["PanRefinement"]
in
  fun ot0 x y = OpenTheory_const_name{const={Thy="panRefinement",Name=x},name=(ns,y)}
  fun ot x = ot0 x x
end 
    
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
           | DecCallC  varname shape funname ('a panLang$exp list) Contract
           | PanC      ('a panLang$prog)
End

Definition sat_def[simp]:
  sat (HoareC P Q)             prog                    = hoare P prog Q ∧
  sat (DecC nl sl el c)        (Dec nr sr er p)        = (nl = nr ∧ sl = sr ∧ el = er ∧ sat c p) ∧
  sat (SeqC c1 c2)             (Seq p1 p2)             = (sat c1 p1 ∧ sat c2 p2) ∧
  sat (IfC l c1 c2)            (If r p1 p2)            = (l = r ∧ sat c1 p1 ∧ sat c2 p2) ∧
  sat (WhileC l i c)           (While r p)             = (l = r ∧ sat c p) ∧
  sat (DecCallC vl sl fl el c) (DecCall vr sr fr er p) = (vl = vr ∧ sl = sr ∧ fl = fr ∧ el = er ∧ sat c p) ∧
  sat (PanC l)                 r                       = (l = r) ∧
  sat _                        _                       = F
End

Theorem sat_cases[simp]:
  (∀n s e l c prog. sat (DecC s e l c)       prog ⇔ ∃p.     prog = Dec s e l p       ∧ sat c p) ∧
  (∀c1 c2 prog.     sat (SeqC c1 c2)         prog ⇔ ∃p1 p2. prog = Seq p1 p2         ∧ sat c1 p1 ∧ sat c2 p2) ∧
  (∀e c1 c2 prog.   sat (IfC e c1 c2)        prog ⇔ ∃p1 p2. prog = If e p1 p2        ∧ sat c1 p1 ∧ sat c2 p2) ∧
  (∀e i v c prog.   sat (WhileC e i c)       prog ⇔ ∃p.     prog = While e p         ∧ sat c p) ∧
  (∀v s f e c prog. sat (DecCallC v s f e c) prog ⇔ ∃p.     prog = DecCall v s f e p ∧ sat c p)
Proof
  rw[] >> elim_cases [‘prog’] >> iff_tac >> rw[]
QED

Definition refine_def:
  $refine (c1 : ('a, 'ffi) Contract) (c2 : ('a, 'ffi) Contract) ⇔ ∀prog. sat c2 prog ⇒ sat c1 prog
End

val _ = set_fixity "refine" (Infix(NONASSOC, 450));
val _ = Parse.Unicode.unicode_version { u = "\226\138\145", tmnm = "refine" };
val _ = TeX_notation {hol = "refine", TeX = ("\\HOLTokenSubmap{}", 1)}
val _ = ot0 "refine" "refine"

Theorem refine_reflexive:
  ∀A. A refine A
Proof
  rw[refine_def]
QED

Theorem refine_transitive:
  ∀A B C. A refine B ∧ B refine C ⇒ A refine C
Proof
  rw[refine_def]
QED

Theorem refine_monotonic_dec:
  ∀A B v sh exp. A refine B ⇒ (DecC v sh exp A) refine (DecC v sh exp B)
Proof
  rw[refine_def]
QED

Theorem refine_monotonic_seq:
  ∀A B C. A refine B ⇒ (SeqC A C) refine (SeqC B C) ∧
                       (SeqC C A) refine (SeqC C B)
Proof
  rw[refine_def]
QED

Theorem refine_monotonic_if:
  ∀A B C e. A refine B ⇒ (IfC e A C) refine (IfC e B C) ∧
                         (IfC e C A) refine (IfC e C B)
Proof
  rw[refine_def]
QED

Theorem refine_monotonic_while:
  ∀A B e i. A refine B ⇒ (WhileC e i A) refine (WhileC e i B)
Proof
  rw[refine_def]
QED

Theorem refine_monotonic_deccall:
  ∀A B v s f e. A refine B ⇒ (DecCallC v s f e A) refine (DecCallC v s f e B)
Proof
  rw[refine_def]
QED

Theorem refine_to_prog_hoare:
  ∀P prog Q. (HoareC P Q) refine (PanC prog) ⇒ hoare P prog Q
Proof
  rw[refine_def]
QED
        
Theorem strengthen_postcondition_refinement_rule:
  Q' ⇛ Q ⇒ (HoareC P Q) refine (HoareC P Q')
Proof
  rw[refine_def,hoare_def]
  >> first_x_assum $ drule_then assume_tac
  >> pairarg_tac
  >> gvs[]
QED

Theorem weaken_precondition_refinement_rule:
  P ⇛ P' ⇒ (HoareC P Q) refine (HoareC P' Q)
Proof
  rw[refine_def,hoare_def]
QED

Theorem both_pre_post_refinement_rule:
  (∀s. P s ⇒ P' s) ∧ (∀s. Q' s ⇒ Q s) ⇒ (HoareC P Q) refine (HoareC P' Q')
Proof
  rw[]
  >> irule refine_transitive
  >> qexists ‘HoareC P' Q’
  >> gvs[strengthen_postcondition_refinement_rule,weaken_precondition_refinement_rule]
QED

Theorem skip_refinement_rule:
  P ⇛ CURRY Q NONE ⇒
  (HoareC P Q) refine (PanC Skip)
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_skip]
QED

Theorem dec_refinement_rule_pan:
  (DecC v sh src (PanC prog)) refine (PanC (Dec v sh src prog))
Proof
  rw[refine_def]
QED

Theorem MEM_IN_LIST_TO_SET:
  MEM e l ⇒ set l e
Proof
  Induct_on ‘l’
  >> gvs[IN_DEF]
QED

Theorem varnotset_eval_thm:
  ∀P src v.
  P ⇛ (λs. v ∉ FDOM s.locals) ∧
  P ⇛ evaluates src ∧
  (∃s. P s) ⇒
  ¬MEM v (var_exp src)
Proof
  rw[IN_DEF]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> last_x_assum $ kall_tac
  >> spose_not_then assume_tac
  >> last_x_assum $ mp_tac
  >> gvs[evaluates_def]
  >> ‘eval s src = NONE’ suffices_by gvs[]
  >> rpt (pop_assum $ mp_tac)
  >> qid_spec_tac ‘src’
  >> qid_spec_tac ‘s’
  >> recInduct eval_ind    
  >> rw[]
  >> gvs[panLangTheory.var_exp_def,eval_def,finite_mapTheory.FLOOKUP_DEF,IN_DEF,AllCaseEqs()]
  >>~- ([‘eval _ _ = NONE ∨ _’],(Cases_on ‘eval s e1’ >> gvs[] >> Cases_on ‘x’ >> gvs[]))
  >> Induct_on ‘es’
  >> rw[]
  >- (‘eval s h = NONE’ suffices_by gvs[]
      >> first_x_assum $ irule
      >> gvs[MEM_IN_LIST_TO_SET])
  >- (Cases_on ‘eval s h’
      >> gvs[]
      >> first_x_assum $ irule
      >> gvs[MEM_IN_LIST_TO_SET])
  >- (‘eval s h = NONE’ suffices_by gvs[]
      >> first_x_assum $ irule
      >> gvs[MEM_IN_LIST_TO_SET])
  >- (‘set (FLAT (MAP (λa. var_exp a) es)) v’ by gvs[MEM_IN_LIST_TO_SET]
      >> gvs[]
      >> Cases_on ‘eval s h’
      >> gvs[]
      >> Cases_on ‘x’
      >> gvs[]
      >> Cases_on ‘w’
      >> gvs[]
      >> Cases_on ‘op’
      >> gvs[wordLangTheory.word_op_def,AllCaseEqs()]
      >> Cases_on ‘es’
      >> gvs[listTheory.OPT_MMAP_def]
      >- (qpat_x_assum ‘eval s h' = _’ $ mp_tac >> ‘eval s h' = NONE’ suffices_by gvs[] >> first_x_assum $ irule >> gvs[MEM_IN_LIST_TO_SET])
      >> Cases_on ‘t’
      >> gvs[listTheory.OPT_MMAP_def])
  >- (‘eval s h = NONE’ suffices_by gvs[]
      >> first_x_assum $ irule
      >> gvs[MEM_IN_LIST_TO_SET])
  >- (Cases_on ‘eval s h’
      >> gvs[]
      >> ‘set (FLAT (MAP (λa. var_exp a) es)) v’ by gvs[MEM_IN_LIST_TO_SET]
      >> gvs[]
      >> Cases_on ‘x’
      >> gvs[]
      >> Cases_on ‘w’
      >> gvs[]
      >> Cases_on ‘op’
      >> gvs[]
      >> Cases_on ‘MAP (λw. case w of ValWord n => n | Struct v1 => ARB) ws’
      >> gvs[pan_op_def]
      >> Cases_on ‘t’
      >> gvs[pan_op_def]
      >> Cases_on ‘es’
      >> gvs[listTheory.OPT_MMAP_def]
      >- (qpat_x_assum ‘eval s h' = _’ $ mp_tac >> ‘eval s h' = NONE’ suffices_by gvs[] >> first_x_assum $ irule >> gvs[MEM_IN_LIST_TO_SET])
      >> Cases_on ‘t’
      >> gvs[listTheory.OPT_MMAP_def])
QED

Theorem varfree_eval_thm:
  varfree_p v P ∧
  P ⇛ evaluates src ∧
  (∃s. P s) ⇒
  ¬MEM v (var_exp src)
Proof
  rw[]
  >> irule varnotset_eval_thm
  >> qexists ‘(λs. P s ∧ v ∉ FDOM s.locals)’
  >> rw[]
  >> qexists ‘s with locals := s.locals \\ v’
  >> gvs[varfree_p_def]
QED

Definition dec_refinement_rule_rhs[simp]:
  DecBC P v src Q = HoareC (λs. P (s with locals := s.locals \\ v) ∧ var_eq Local v src s)
                           (λ(r,t). Q (r,t with locals := t.locals \\ v))
End

Theorem dec_refinement_rule:
  P ⇛ (λs. v ∉ FDOM s.locals) ∧
  P ⇛ evaluates src ⇒
  (HoareC P Q) refine
         (DecC v sh src (DecBC P v src Q))
Proof
  rw[refine_def,IN_DEF]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> dxrule_then assume_tac $ ((iffLR o cj 2) wp_is_weakest_precondition)
  >> rw[]
  >> ‘¬MEM v (var_exp src)’ by (irule varnotset_eval_thm >> qexists ‘P’ >> gvs[IN_DEF] >> qexists ‘s’ >> gvs[])
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[wp_dec,subst_def,evaluates_def]
  >> first_x_assum $ qspec_then ‘s with locals := s.locals |+ (v,v')’ assume_tac
  >> ‘s with locals := s.locals \\ v = s’ by gvs[finite_mapTheory.DOMSUB_NOT_IN_DOM,IN_DEF,
                                                 state_component_equality]
  >> gvs[var_eq_def,finite_mapTheory.FLOOKUP_UPDATE,eval_fresh_var]
  >> ‘reset_subst v s Q = (λ(r,t). Q (r,t with locals := t.locals \\ v))’ suffices_by gvs[]
  >> gvs[FUN_EQ_THM]
  >> rw[]
  >> PairCases_on ‘x’
  >> rw[reset_subst_def,IN_DEF,finite_mapTheory.FLOOKUP_DEF,res_var_def]
QED
        
Theorem assign_refinement_rule:
  P ⇛ evaluates src ∧
  P ⇛ valid_value k v src ∧
  P ⇛ subst k v src (CURRY Q NONE) ⇒
  (HoareC P Q) refine (PanC (Assign k v src))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_assign]
QED

Theorem store_refinement_rule:
  P ⇛ evaluates_to_word dest ∧
  P ⇛ evaluates src ∧
  P ⇛ addr_in_mem (the_eval_vw dest) (the_eval src) ∧
  P ⇛ mem_subst (the_eval_vw dest) (the_eval src) (CURRY Q NONE) ⇒
  (HoareC P Q) refine (PanC (Store dest src))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_store]
QED

Theorem store32_refinement_rule:
  P ⇛ evaluates_to_word dest ∧
  P ⇛ evaluates_to_word src ∧
  P ⇛ addr_in_mem32 (the_eval_vw dest) ∧
  P ⇛ mem_subst32 (the_eval_vw dest) (the_eval_vw src) (CURRY Q NONE) ⇒
  (HoareC P Q) refine (PanC (Store32 dest src))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_store32]
QED

Theorem storebyte_refinement_rule:
  P ⇛ evaluates_to_word dest ∧
  P ⇛ evaluates_to_word src ∧
  P ⇛ addr_in_mem8 (the_eval_vw dest) ∧
  P ⇛ mem_subst8 (the_eval_vw dest) (the_eval_vw src) (CURRY Q NONE) ⇒
  (HoareC P Q) refine (PanC (StoreByte dest src))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_storebyte]
QED

Definition op_align_def[simp]:
  op_align op w s = if op = OpW then (w s) else (byte_align (w s))
End

Definition ffi_shmemload_def[simp]:
  ffi_shmemload op vk v src Q s = hoareFFI s
                    (SharedMem MappedRead)
                    [n2w (nb_op op)]
                    (word_to_bytes (the_eval_vw src s) F)
                    (λt output. Q (NONE,set_kvar vk v (ValWord (word_of_bytes F 0w output)) s with ffi := t))
                    (λoutcome. Q (SOME (FinalFFI outcome),empty_locals s))
End

Theorem shmemload_refinement_rule:
  P ⇛ has_kvar_vw vk v ∧
  P ⇛ evaluates_to_word src ∧
  P ⇛ in_sh_memaddrs (op_align op (the_eval_vw src)) ∧
  P ⇛ ffi_shmemload op vk v src Q ⇒
  (HoareC P Q) refine (PanC (ShMemLoad op vk v src))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_shmemload,has_kvar_vw_def,in_sh_memaddrs_def,evaluates_to_word_def,evaluates_to_def,IN_DEF]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[the_eval_vw_def,the_eval_def]
QED

Definition ffi_shmemstore_def[simp]:
  ffi_shmemstore op vk v src dest Q s = hoareFFI s
                    (SharedMem MappedWrite)
                    [n2w (nb_op op)]
                    (if op = OpW then
                        word_to_bytes (the_eval_vw src s) F ++ word_to_bytes (the_eval_vw dest s) F
                     else
                        (TAKE (nb_op op) (word_to_bytes (the_eval_vw src s) F) ++ word_to_bytes (the_eval_vw dest s) F))
                    (λt output. Q (NONE,s with ffi := t))
                    (λoutcome. Q (SOME (FinalFFI outcome),s))
End

Theorem shmemstore_refinement_rule:
  P ⇛ evaluates_to_word dest ∧
  P ⇛ evaluates_to_word src ∧
  P ⇛ in_sh_memaddrs (op_align op (the_eval_vw dest)) ∧
  P ⇛ ffi_shmemstore op vk v src dest Q ⇒
  (HoareC P Q) refine (PanC (ShMemStore op dest src))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_shmemstore,has_kvar_vw_def,in_sh_memaddrs_def,evaluates_to_word_def,evaluates_to_def,IN_DEF]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[the_eval_vw_def,the_eval_def]
QED

Theorem seq_refinement_rule_pan:
  (SeqC (PanC l) (PanC r)) refine (PanC (Seq l r))
Proof
  rw[refine_def]
QED

Definition seq_refinement_rule_rhs[simp]:
  SeqBC P M Q = HoareC P (λ(r,t). if r ≠ NONE then Q (r,t) else M t)
End                       
        
Theorem seq_refinement_rule:
  (HoareC P Q) refine (SeqC (SeqBC P M Q)
                            (HoareC M Q))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> rpt(dxrule_then assume_tac $ ((iffLR o cj 2) wp_is_weakest_precondition))
  >> rw[]
  >> gvs[]
  >> first_x_assum $ dxrule_then assume_tac
  >> dxrule_then assume_tac (iffLR wp_nif)
  >> dxrule_then assume_tac pq_monotonic
  >> gvs[wp_seq]
  >> disj1_tac
  >> irule (SRULE [] wp_monotonic)
  >> HINT_EXISTS_TAC
  >> gvs[]
QED

Theorem if_refinement_rule_pan:
  (IfC e (PanC l) (PanC r)) refine (PanC (If e l r))
Proof
  rw[refine_def]
QED

Definition if_refinement_rule_rhs_T[simp]:
  IfBCT P e Q = HoareC (λs. P s ∧ evaluates_to_true e s) Q
End
        
Definition if_refinement_rule_rhs_F[simp]:
  IfBCF P e Q = HoareC (λs. P s ∧ evaluates_to_false e s) Q
End
        
Theorem if_refinement_rule:
  P ⇛ evaluates_to_word e ⇒
  (HoareC P Q) refine (IfC e (IfBCT P e Q)
                             (IfBCF P e Q))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> rpt(dxrule_then assume_tac $ ((iffLR o cj 2) wp_is_weakest_precondition))
  >> gvs[wp_if]
QED

Theorem while_refinement_rule_pan:
  (WhileC e i (PanC p)) refine (PanC (While e p))
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
        
Definition while_refinement_rule_rhs[simp]:
  WhileBC e i QB QR QE QF = HoareC (while_body_pre i e) (while_body_post i QB QR QE QF)
End        

Theorem while_refinement_rule:
  ∀P Q QB QR QE QF e i v.
  P ⇛ i ∧
  i ⇛ evaluates_to_word e ∧
  (λs. i s ∧ evaluates_to_false e s) ⇛ CURRY Q NONE ∧
  (∀s k. i s ⇒ i (s with clock := k)) ∧
  QB ⇛ CURRY Q NONE ∧
  (∀t v.     QR (t,v)     ⇒ Q (SOME (Return v),       t)) ∧
  (∀t eid v. QE (t,eid,v) ⇒ Q (SOME (Exception eid v),t)) ∧
  (∀t res.   QF (t,res)   ⇒ Q (SOME (FinalFFI res),   t)) ⇒
  (HoareC P Q) refine
         (WhileC e i (WhileBC e i QB QR QE QF))
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
      >> strip_tac
      >> first_x_assum $ irule
      >> ‘s1.clock ≤ (s with clock := s.clock - 1).clock’ suffices_by gvs[]
      >> irule evaluate_clock
      >> qexistsl [‘p’, ‘NONE’]
      >> gvs[])
  >> Cases_on ‘x’
  >> gvs[]
  >> first_x_assum $ qspec_then ‘s1’ assume_tac
  >> gvs[]
  >> strip_tac
  >> first_x_assum $ irule
  >> ‘s1.clock ≤ (s with clock := s.clock - 1).clock’ suffices_by gvs[]
  >> irule evaluate_clock
  >> qexistsl [‘p’, ‘SOME Continue’]
  >> gvs[]
QED

Theorem return_refinement_rule:
  P ⇛ evaluates e ∧
  P ⇛ (λs. size_of_shape (shape_of (the_eval e s)) ≤ 32) ∧
  P ⇛ (λs. Q (SOME (Return (the_eval e s)),empty_locals s)) ⇒
  (HoareC P Q) refine (PanC (Return e))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_return,evaluates_def,evaluates_to_def]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[the_eval_def]
QED

Theorem annot_refinement_rule:
  P ⇛ CURRY Q NONE ⇒
  (HoareC P Q) refine (PanC (Annot t1 t2))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_annot]
QED

Theorem break_refinement_rule:
  P ⇛ CURRY Q (SOME Break) ⇒
  (HoareC P Q) refine (PanC (Break))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_break]
QED

Theorem continue_refinement_rule:
  P ⇛ CURRY Q (SOME Continue) ⇒
  (HoareC P Q) refine (PanC (Continue))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_continue]
QED

Theorem raise_refinement_rule:
  P ⇛ evaluates e ∧
  P ⇛ (λs. has_eshape eid (shape_of (the_eval e s)) s) ∧
  P ⇛ (λs. size_of_shape (shape_of (the_eval e s)) ≤ 32) ∧
  P ⇛ (λs. Q (SOME (Exception eid (the_eval e s)),empty_locals s)) ⇒
  (HoareC P Q) refine (PanC (Raise eid e))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_raise,evaluates_def,evaluates_to_def]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[the_eval_def]
QED

Theorem pred_upd_simp[simp]:
  ∀P s. P s ⇒ P (dec_clock s with <|locals := s.locals; clock := s.clock|>) ∧
              P (s with <|locals := s.locals; clock := s.clock|>)
Proof
  rw[dec_clock_def]
  >> ‘s with <|locals := s.locals; clock := s.clock|> = s’ suffices_by gvs[]
  >> gvs[state_component_equality]
QED

Definition tailcall_contract_def[simp]:
  tailcall_contract P fname argexps Q s = let (p,lcls) = THE (lookup_code s.code fname (THE (OPT_MMAP (eval s) argexps)))
           in hoare (λs'. s'.locals = lcls ∧ P (s' with <|locals := s.locals; clock := s.clock|>))
                    p
                    (λ(r,t). r ≠ SOME Continue ∧ r ≠ SOME Break ∧ r ≠ NONE ∧ Q (r,empty_locals t))
End

Definition evaluates_all_def[simp]:
  evaluates_all exps s ⇔ IS_SOME (OPT_MMAP (eval s) exps)
End

Definition the_evals_def[simp]:
  the_evals exps s = THE (OPT_MMAP (eval s) exps)
End

Definition has_function[simp]:
  has_function fname args s ⇔ IS_SOME (lookup_code s.code fname (the_evals args s))
End
        
Theorem tailcall_refinement_rule:
  P ⇛ evaluates_all argexps ∧
  P ⇛ has_function fname argexps ∧
  P ⇛ tailcall_contract P fname argexps Q ⇒
  (HoareC P Q) refine (PanC (TailCall fname argexps))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_tailcall]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[optionTheory.IS_SOME_EXISTS]
  >> PairCases_on ‘x’
  >> gvs[]
  >> dxrule_then assume_tac ((iffLR o cj 2) wp_is_weakest_precondition)
  >> disj2_tac
  >> gvs[]
  >> first_x_assum $ irule
  >> gvs[dec_clock_def]
  >> ‘s with <|locals := s.locals; clock := s.clock|> = s’ suffices_by gvs[]
  >> gvs[state_component_equality]
QED

Definition assigncall_contract_def[simp]:
  assigncall_contract P fname argexps k v Q s = let (p,lcls) = THE (lookup_code s.code fname (THE (OPT_MMAP (eval s) argexps)))
           in hoare (λs'. s'.locals = lcls ∧ P (s' with <|locals := s.locals; clock := s.clock|>))
                    p
                    (λ(r,t). case r of
                             | SOME (Return rv)         => is_valid_value (case k of Local => s.locals | Global => s.globals) v rv ∧
                                                           Q (NONE,set_kvar k v rv (t with locals := s.locals))
                             | SOME (Exception eid exn) => Q (SOME (Exception eid exn),empty_locals t)
                             | SOME (FinalFFI f)        => Q (SOME (FinalFFI f),empty_locals t)
                             | _                        => F)
End
        
Theorem assigncall_refinement_rule:
  P ⇛ evaluates_all argexps ∧
  P ⇛ has_function fname argexps ∧
  P ⇛ assigncall_contract P fname argexps k v Q ⇒
  (HoareC P Q) refine (PanC (AssignCall (k,v) NONE fname argexps))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_assigncall]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[optionTheory.IS_SOME_EXISTS]
  >> PairCases_on ‘x’
  >> gvs[]
  >> dxrule_then assume_tac ((iffLR o cj 2) wp_is_weakest_precondition)
  >> disj2_tac
  >> gvs[]
  >> first_x_assum $ irule
  >> gvs[dec_clock_def]
  >> ‘s with <|locals := s.locals; clock := s.clock|> = s’ suffices_by gvs[]
  >> gvs[state_component_equality]
QED

Definition assigncall_handler_contract_def[simp]:
  assigncall_handler_contract P fname argexps k v (eid,evar,hp) Q s =
           let (p,lcls) = THE (lookup_code s.code fname (THE (OPT_MMAP (eval s) argexps)))
           in hoare (λs'. s'.locals = lcls ∧ P (s' with <|locals := s.locals; clock := s.clock|>))
                    p
                    (λ(r,t). case r of
                             | SOME (Return rv)          => is_valid_value (case k of Local => s.locals | Global => s.globals) v rv ∧
                                                            Q (NONE,set_kvar k v rv (t with locals := s.locals))
                             | SOME (Exception eid' exn) => if eid' = eid then
                                                              FLOOKUP s.eshapes eid = SOME (shape_of exn) ∧
                                                              is_valid_value s.locals evar exn ∧
                                                              hoare (λs'. s' = set_var evar exn (s' with locals := s.locals)) hp Q
                                                            else
                                                              Q (SOME (Exception eid' exn),empty_locals t)
                             | SOME (FinalFFI f)         => Q (SOME (FinalFFI f),empty_locals t)
                             | _                         => F)
End

Theorem assigncall_handler_refinement_rule:
  P ⇛ evaluates_all argexps ∧
  P ⇛ has_function fname argexps ∧
  P ⇛ assigncall_handler_contract P fname argexps k v handler Q ⇒
  (HoareC P Q) refine (PanC (AssignCall (k,v) (SOME handler) fname argexps))
Proof
  rw[refine_def]
  >> PairCases_on ‘handler’
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_assigncall]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[optionTheory.IS_SOME_EXISTS]
  >> PairCases_on ‘x’
  >> gvs[]
  >> dxrule_then assume_tac ((iffLR o cj 2) wp_is_weakest_precondition)
  >> disj2_tac
  >> gvs[]
  >> first_x_assum $ assume_tac o SRULE [cj 2 wp_is_weakest_precondition]
  >> first_x_assum $ qspec_then ‘dec_clock s with locals := x1’ assume_tac
  >> gvs[]
  >> ‘P (dec_clock s with <|locals := s.locals; clock := s.clock|>)’ by (‘dec_clock s with <|locals := s.locals; clock := s.clock|> = s’ suffices_by gvs[]
                                                                         >> gvs[state_component_equality,dec_clock_def])
  >> gvs[wp_def]
  >> pairarg_tac
  >> gvs[]
  >> rpt (FULL_CASE_TAC >> gvs[])
  >> first_x_assum $ irule
  >> gvs[set_var_def]
QED

Definition standalonecall_contract_def[simp]:
  standalonecall_contract P fname argexps Q s =
           let (p,lcls) = THE (lookup_code s.code fname (THE (OPT_MMAP (eval s) argexps)))
           in hoare (λs'. s'.locals = lcls ∧ P (s' with <|locals := s.locals; clock := s.clock|>))
                    p
                    (λ(r,t). case r of
                             | SOME (Return rv)         => Q (NONE,t with locals := s.locals)
                             | SOME (Exception eid exn) => Q (SOME (Exception eid exn),empty_locals t)
                             | SOME (FinalFFI f)        => Q (SOME (FinalFFI f),empty_locals t)
                             | _                        => F)
End
        
Theorem standalonecall_refinement_rule:
  P ⇛ evaluates_all argexps ∧
  P ⇛ has_function fname argexps ∧
  P ⇛ standalonecall_contract P fname argexps Q ⇒
  (HoareC P Q) refine (PanC (StandAloneCall NONE fname argexps))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_standalonecall]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[optionTheory.IS_SOME_EXISTS]
  >> PairCases_on ‘x’
  >> gvs[]
  >> dxrule_then assume_tac ((iffLR o cj 2) wp_is_weakest_precondition)
  >> disj2_tac
  >> gvs[]
  >> first_x_assum $ irule
  >> gvs[dec_clock_def]
  >> ‘s with <|locals := s.locals; clock := s.clock|> = s’ suffices_by gvs[]
  >> gvs[state_component_equality]
QED

Definition standalonecall_handler_contract_def[simp]:
  standalonecall_handler_contract P fname argexps (eid,evar,hp) Q s =
           let (p,lcls) = THE (lookup_code s.code fname (THE (OPT_MMAP (eval s) argexps)))
           in hoare (λs'. s'.locals = lcls ∧ P (s' with <|locals := s.locals; clock := s.clock|>))
                    p
                    (λ(r,t). case r of
                             | SOME (Return rv)          => Q (NONE,t with locals := s.locals)
                             | SOME (Exception eid' exn) => if eid' = eid then
                                                              FLOOKUP s.eshapes eid = SOME (shape_of exn) ∧
                                                              is_valid_value s.locals evar exn ∧
                                                              hoare (λs'. s' = set_var evar exn (s' with locals := s.locals)) hp Q
                                                            else
                                                              Q (SOME (Exception eid' exn),empty_locals t)
                             | SOME (FinalFFI f)         => Q (SOME (FinalFFI f),empty_locals t)
                             | _                         => F)
End

Theorem standalonecall_handler_refinement_rule:
  P ⇛ evaluates_all argexps ∧
  P ⇛ has_function fname argexps ∧
  P ⇛ standalonecall_handler_contract P fname argexps handler Q ⇒
  (HoareC P Q) refine (PanC (StandAloneCall (SOME handler) fname argexps))
Proof
  rw[refine_def]
  >> PairCases_on ‘handler’
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_standalonecall]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[optionTheory.IS_SOME_EXISTS]
  >> PairCases_on ‘x’
  >> gvs[]
  >> dxrule_then assume_tac ((iffLR o cj 2) wp_is_weakest_precondition)
  >> disj2_tac
  >> gvs[]
  >> first_x_assum $ assume_tac o SRULE [cj 2 wp_is_weakest_precondition]
  >> first_x_assum $ qspec_then ‘dec_clock s with locals := x1’ assume_tac
  >> gvs[]
  >> ‘P (dec_clock s with <|locals := s.locals; clock := s.clock|>)’ by (‘dec_clock s with <|locals := s.locals; clock := s.clock|> = s’ suffices_by gvs[]
                                                                         >> gvs[state_component_equality,dec_clock_def])
  >> gvs[wp_def]
  >> pairarg_tac
  >> gvs[]
  >> rpt (FULL_CASE_TAC >> gvs[])
  >> first_x_assum $ irule
  >> gvs[set_var_def]
QED

Theorem deccall_refinement_rule_pan:
  (DecCallC v s f e (PanC p)) refine (PanC (DecCall v s f e p))
Proof
  rw[refine_def]
QED

Definition deccall_contract_def[simp]:
  deccall_contract P f e v sh P' Q s = 
           let (p,lcls) = THE (lookup_code s.code f (THE (OPT_MMAP (eval s) e)))
           in hoare (λs'. s'.locals = lcls ∧ P (s' with <|locals := s.locals; clock := s.clock|>))
                    p
                    (λ(r,t). case r of
                             | SOME (Return rv)         => shape_of rv = sh ∧ P' (set_var v rv (t with locals := s.locals))
                             | SOME (Exception eid exn) => Q (SOME (Exception eid exn),empty_locals t)
                             | SOME (FinalFFI f)        => Q (SOME (FinalFFI f),empty_locals t)
                             | _                        => F)
End

Theorem deccall_refinement_rule_varfree:
  varfree_q v Q ∧
  P ⇛ evaluates_all argexps ∧
  P ⇛ has_function fname argexps ∧
  P ⇛ deccall_contract P fname argexps v sh P' Q ⇒
  (HoareC P Q) refine (DecCallC v sh fname argexps (HoareC P' Q))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_deccall]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[optionTheory.IS_SOME_EXISTS]
  >> PairCases_on ‘x’
  >> gvs[]
  >> dxrule_then assume_tac ((iffLR o cj 2) wp_is_weakest_precondition)
  >> disj2_tac
  >> gvs[]
  >> first_x_assum $ qspec_then ‘dec_clock s with locals := x1’ assume_tac
  >> gvs[]
  >> ‘P (dec_clock s with <|locals := s.locals; clock := s.clock|>)’ by (‘dec_clock s with <|locals := s.locals; clock := s.clock|> = s’ suffices_by gvs[]
                                                                         >> gvs[state_component_equality,dec_clock_def])
  >> gvs[wp_def]
  >> pairarg_tac
  >> gvs[]
  >> rpt (FULL_CASE_TAC >> gvs[])
  >> gvs[reset_subst_def,hoare_def]
  >> first_x_assum $ dxrule_then assume_tac
  >> pairarg_tac
  >> gvs[]
  >> Cases_on ‘FLOOKUP s.locals v’
  >> gvs[res_var_def,varfree_q_def]
QED

Definition array_in_memaddrs[simp]:
  array_in_memaddrs ptr len s ⇔ ∀k. all_words (the_eval_vw ptr s) (w2n (the_eval_vw len s)) k ⇒
                                    byte_align k ∈ s.memaddrs 
End

Definition extcall_ffi_contract[simp]:
  extcall_ffi_contract ffi_index cnfptr cnflen inptr inlen Q s =
                    hoareFFI s
                    (ExtCall (explode ffi_index))
                    (THE (read_bytearray (the_eval_vw cnfptr s) (w2n (the_eval_vw cnflen s)) (mem_load_byte s.memory s.memaddrs s.be)))
                    (THE (read_bytearray (the_eval_vw inptr s)  (w2n (the_eval_vw inlen s))  (mem_load_byte s.memory s.memaddrs s.be)))
                    (λt output. Q (NONE, s with <|memory := write_bytearray (the_eval_vw inptr s) output s.memory s.memaddrs s.be; ffi := t|>))
                    (λoutcome. Q (SOME (FinalFFI outcome),empty_locals s))
End

Theorem extcall_refinement_rule:
  P ⇛ evaluates_to_word cnfptr ∧
  P ⇛ evaluates_to_word cnflen ∧
  P ⇛ evaluates_to_word inptr ∧
  P ⇛ evaluates_to_word inlen ∧
  P ⇛ array_in_memaddrs cnfptr cnflen ∧
  P ⇛ array_in_memaddrs inptr inlen ∧
  P ⇛ extcall_ffi_contract ffi_index cnfptr cnflen inptr inlen Q ⇒
  (HoareC P Q) refine (PanC (ExtCall ffi_index cnfptr cnflen inptr inlen))
Proof
  rw[refine_def]
  >> irule ((iffRL o cj 2) wp_is_weakest_precondition)
  >> gvs[wp_extcall,evaluates_to_word_def,evaluates_to_def]
  >> rw[]
  >> rpt (first_x_assum $ drule_then assume_tac)
  >> gvs[the_eval_vw_def,the_eval_def]
QED

