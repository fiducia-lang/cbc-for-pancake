(***********************************************************************
 * Proofs about Weakest Preconditions of Pancake Statements            *
 ***********************************************************************)

Theory panWeakestPrecondition
Ancestors panSem panProps panPredicate
          misc[qualified]
Libs BasicProvers

Definition hoare_def:
  hoare P prog Q ⇔ ∀s. P s ⇒ let (r,t) = evaluate (prog,s)
                             in r ≠ SOME TimeOut ⇒ r ≠ SOME Error ∧ Q (r,t)
End

Theorem hoare_monotonic_p:
  ∀P P' prog Q. P' ⇛ P ⇒ (hoare P prog Q ⇒ hoare P' prog Q)
Proof
  rw[hoare_def]
QED

Definition hoareFFI_def:
  hoareFFI s caltyp conf input Q R ⇔ case (call_FFI s.ffi caltyp conf input) of
                                           | FFI_return t output => Q t output
                                           | FFI_final outcome   => R outcome
End

Definition wp_def:
  wp prog Q s ⇔ let (r,t) = evaluate (prog,s)
                in r ≠ SOME TimeOut ⇒ r ≠ SOME Error ∧ Q (r,t)
End

Theorem wp_is_weakest_precondition:
  ∀P prog Q. hoare (wp prog Q) prog Q ∧ (hoare P prog Q ⇔ (P ⇛ wp prog Q))
Proof
  rw[hoare_def,wp_def]
QED

Theorem wp_monotonic:
  ∀A B prog. (A ⇛ B) ⇒ (wp prog A ⇛ wp prog B)
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
  wp Skip Q s ⇔ CURRY Q NONE s
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
  wp (Assign k v src) Q s ⇔ evaluates src s ∧
                            valid_value k v src s ∧
                            subst k v src (CURRY Q NONE) s
Proof
  Cases_on ‘k’
  >> rw[wp_def,evaluate_def,valid_value_def,subst_def,evaluates_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[AllCaseEqs()]
QED

Theorem wp_store:
  wp (Store dest src) Q s ⇔ evaluates_to_word dest s ∧
                            evaluates src s ∧
                            addr_in_mem (the_eval_vw dest) (the_eval src) s ∧
                            mem_subst (the_eval_vw dest) (the_eval src) (CURRY Q NONE) s
Proof
  rw[wp_def,evaluate_def,evaluates_def,evaluates_to_word_def,addr_in_mem_def,mem_subst_def,
     the_eval_def,the_eval_vw_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[AllCaseEqs()]
QED

Theorem wp_store32:
  wp (Store32 dest src) Q s ⇔ evaluates_to_word dest s ∧
                              evaluates_to_word src s ∧
                              addr_in_mem32 (the_eval_vw dest) s ∧
                              mem_subst32 (the_eval_vw dest) (the_eval_vw src) (CURRY Q NONE) s
Proof
  rw[wp_def,evaluate_def,evaluates_to_word_def,addr_in_mem32_def,mem_subst32_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[AllCaseEqs(),the_eval_vw_def,the_eval_def,mem_store_32_def,IN_DEF]
QED

Theorem wp_storebyte:
  wp (StoreByte dest src) Q s ⇔ evaluates_to_word dest s ∧
                                evaluates_to_word src s ∧
                                addr_in_mem8 (the_eval_vw dest) s ∧
                                mem_subst8 (the_eval_vw dest) (the_eval_vw src) (CURRY Q NONE) s
Proof
  rw[wp_def,evaluate_def,evaluates_to_word_def,addr_in_mem8_def,mem_subst8_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[AllCaseEqs(),the_eval_vw_def,the_eval_def,mem_store_byte_def,IN_DEF]
QED

Definition shmemload_post_def[simp]:
  shmemload_post Q vk v s = ((λt output. Q (NONE,set_kvar vk v (ValWord (word_of_bytes F 0w output)) s with ffi := t)),
                             (λoutcome.  Q (SOME (FinalFFI outcome),empty_locals s)))
End

Theorem wp_shmemload:
  wp (ShMemLoad op vk v src) Q s ⇔ (∃w. lookup_kvar s vk v = SOME (ValWord w)) ∧
                                   ∃addr. evaluates_to src (ValWord addr) s ∧
                                          (if op = OpW then addr else byte_align addr) ∈ s.sh_memaddrs ∧
                                          let (QF,RF) = shmemload_post Q vk v s in
                                            hoareFFI
                                              s
                                              (SharedMem MappedRead)
                                              [n2w (nb_op op)]
                                              (word_to_bytes addr F)
                                              QF
                                              RF
Proof
  rw[wp_def,evaluate_def,evaluates_to_def,sh_mem_load_def,hoareFFI_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[AllCaseEqs(),IN_DEF]
  >- (Cases_on ‘v5’ >> gvs[])
  >- (Cases_on ‘v5’ >> gvs[])
  >- (Cases_on ‘v5’ >> gvs[])
  >- (Cases_on ‘v5’ >> gvs[])
  >> Cases_on ‘op’
  >> gvs[nb_op_def]
QED

Definition shmemstore_post_def[simp]:
  shmemstore_post Q s = ((λt output. Q (NONE, s with ffi := t)),
                         (λoutcome.  Q (SOME (FinalFFI outcome),s)))
End

Theorem wp_shmemstore:
  wp (ShMemStore op dest src) Q s ⇔ ∃addr val. evaluates_to dest (ValWord addr) s ∧
                                               evaluates_to src (ValWord val) s ∧
                                               (if op = OpW then addr else byte_align addr) ∈ s.sh_memaddrs ∧
                                               let (QF,RF) = shmemstore_post Q s in
                                                 hoareFFI
                                                  s
                                                  (SharedMem MappedWrite)
                                                  [n2w (nb_op op)]
                                                  (if op = OpW then
                                                     (word_to_bytes val F ++ word_to_bytes addr F)
                                                   else
                                                     (TAKE (nb_op op) (word_to_bytes val F) ++ word_to_bytes addr F))
                                                  QF
                                                  RF
Proof
  rw[wp_def,evaluate_def,evaluates_to_def,sh_mem_store_def,hoareFFI_def]
  >> iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[AllCaseEqs()]
  >> Cases_on ‘op’
  >> gvs[nb_op_def,IN_DEF]
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
  >> every_case_tac
  >> gvs[]
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
  >> gvs[AllCaseEqs()]
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
  >> gvs[AllCaseEqs()]
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
  >> gvs[AllCaseEqs()]
  >> FULL_CASE_TAC
  >> gvs[]
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
  >> gvs[AllCaseEqs()]
  >> FULL_CASE_TAC
  >> gvs[]
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
  >> gvs[AllCaseEqs(),reset_subst_def]
  >> pairarg_tac
  >> gvs[]
QED

Theorem mem_SOME_EQ_read_bytearray:
  ∀p n m. (∀k. all_words p n k ⇒ ∃w. m k = SOME w) ⇔ ∃ba. read_bytearray p n m = SOME ba
Proof
  rw[]
  >> reverse iff_tac
  >- (rw[]
      >> dxrule_then assume_tac miscTheory.read_bytearray_IMP_mem_SOME
      >> gvs[IN_DEF]
      >> first_x_assum $ dxrule_then assume_tac
      >> Cases_on ‘m k’
      >> gvs[])
  >> qid_spec_tac ‘p’
  >> Induct_on ‘n’
  >> rw[]
  >> gvs[miscTheory.read_bytearray_def]
  >> reverse (qsuff_tac ‘∃w. m p = SOME w’)
  >- (first_x_assum $ irule >> gvs[miscTheory.all_words_def])
  >> rw[]
  >> gvs[]
  >> qsuff_tac ‘(∀k. all_words (p + 1w) n k ⇒ ∃w. m k = SOME w)’
  >> rw[]
  >- (first_x_assum $ drule_then assume_tac >> gvs[])
  >> qsuff_tac ‘all_words p (SUC n) k’
  >- gvs[]
  >> rw[miscTheory.all_words_def,IN_DEF]
QED

Theorem memaddrs_EQ_mem_load_byte_SOME:
  ∀m be dm k. dm (byte_align k) ⇔ ∃w. mem_load_byte m dm be k = SOME w
Proof
  rw[mem_load_byte_def]
  >> Cases_on ‘m (byte_align k)’
  >> gvs[IN_DEF]
QED

Definition extcall_post_def[simp]:
  extcall_post Q addr s = ((λt output. Q (NONE, s with <|memory := write_bytearray addr output s.memory s.memaddrs s.be; ffi := t|>)),
                           (λoutcome.  Q (SOME (FinalFFI outcome),empty_locals s)))
End

Theorem wp_extcall:
  wp (ExtCall ffi_index cnfptr cnflen inptr inlen) Q s ⇔ ∃cpw clw ipw ilw. evaluates_to cnfptr (ValWord cpw) s ∧
                                                                           evaluates_to cnflen (ValWord clw) s ∧
                                                                           evaluates_to inptr  (ValWord ipw) s ∧
                                                                           evaluates_to inlen  (ValWord ilw) s ∧
                                                                           (∀k. all_words cpw (w2n clw) k ⇒ byte_align k ∈ s.memaddrs) ∧
                                                                           (∀k. all_words ipw (w2n ilw) k ⇒ byte_align k ∈ s.memaddrs) ∧
                                                                           let (QF,RF) = extcall_post Q ipw s in
                                                                             hoareFFI s (ExtCall (explode ffi_index))
                                                                                   (THE (read_bytearray cpw (w2n clw) (mem_load_byte s.memory s.memaddrs s.be)))
                                                                                   (THE (read_bytearray ipw (w2n ilw) (mem_load_byte s.memory s.memaddrs s.be)))
                                                                                   QF
                                                                                   RF
Proof
  rw[wp_def,evaluate_def,evaluates_to_def,hoareFFI_def]
  >> reverse iff_tac
  >> rw[]
  >> pairarg_tac
  >> gvs[]
  >- (‘r ≠ SOME Error ∧ Q (r,t) ∨ r = SOME TimeOut’ suffices_by metis_tac[]
      >> gvs[IN_DEF]
      >> rpt (qpat_x_assum ‘∀k. _ ⇒ s.memaddrs _’ $ assume_tac o GEN_ALL o REWRITE_RULE [memaddrs_EQ_mem_load_byte_SOME])
      >> rpt (qpat_x_assum ‘∀m be k. _’ $ qspecl_then [‘s.memory’, ‘s.be’] assume_tac)
      >> rpt (qpat_x_assum ‘∀k. _ ⇒ ∃w. _’ $ assume_tac o REWRITE_RULE [mem_SOME_EQ_read_bytearray])
      >> gvs[AllCaseEqs()])
  >> gvs[AllCaseEqs()]
  >> rw[IN_DEF]
  >> irule (iffRL memaddrs_EQ_mem_load_byte_SOME)
  >> qexistsl [‘s.be’, ‘s.memory’]
  >> irule (iffRL mem_SOME_EQ_read_bytearray)
  >| [qexistsl [‘w2n ad1’, ‘sz1’], qexistsl [‘w2n ad2’, ‘sz2’], qexistsl [‘w2n ad1’, ‘sz1’], qexistsl [‘w2n ad2’, ‘sz2’]]
  >> gvs[]
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
  >> gvs[AllCaseEqs()]
QED

Theorem wp_tick:
  wp Tick Q s ⇔ s.clock = 0 ∨ Q (NONE,dec_clock s)
Proof
  rw[wp_def,evaluate_def]
QED

Theorem wp_annot:
  wp (Annot a b) Q s ⇔ Q (NONE,s)
Proof
  rw[wp_def,evaluate_def]
QED
