(* misc theorems *)
Theory panMisc
Ancestors panRefinement
          byte mlstring words
Libs blastLib wordsLib

Definition word_def:
  word s ⇔ ∃w. s = (ValWord w)
End

Definition word_with_def:
  word_with P s ⇔ ∃w. s = (ValWord w) ∧ P w
End

Definition the_word_def:
  the_word w s ⇔ s = (ValWord w)
End

Definition unbox_def[simp]:
  unbox (Word w) = w
End

Definition unboxv_def[simp]:
  unboxv (ValWord w) = w
End

Definition signature_def:
  signature = FST
End
        
Definition code_def:
  code = SND
End
        
Definition fun_contract_def:
  FunContract vars P Qt Qr =
  HoareC (λs. set (MAP (strlit o FST) vars) = FDOM s.locals ∧
              EVERY (λ(var,P_var). FDOM s.locals (strlit var) ∧
                                   P_var (s.locals ' (strlit var))) vars ∧
              P s)
         (λ(r,t). t.locals = FEMPTY ∧
                  Qt t ∧
                  ∃ret. r = SOME (Return ret) ∧ Qr ret)
End

Definition drop_annot_def:
  drop_annot (Seq (Annot a b) p) = drop_annot p ∧
  drop_annot (Seq l r) = Seq (drop_annot l) (drop_annot r)  ∧
  drop_annot (If e l r) = If e (drop_annot l) (drop_annot r) ∧
  drop_annot (Dec k v s p) = Dec k v s (drop_annot p) ∧
  drop_annot (DecCall v s f e p) = DecCall v s f e (drop_annot p) ∧
  drop_annot (While e p) = While e (drop_annot p) ∧
  drop_annot p = p
End

Theorem drop_annot_evaluate_eq:
  ∀p s. evaluate (p,s) = evaluate (drop_annot p,s)
Proof
  recInduct panSemTheory.evaluate_ind
  >> rw[drop_annot_def]
  >~ [‘While’]
  >- (once_rewrite_tac[panSemTheory.evaluate_def]
      >> rpt (BasicProvers.FULL_CASE_TAC)
      >> gvs[]
      >> pairarg_tac
      >> gvs[]
      >> rpt (BasicProvers.FULL_CASE_TAC >> gvs[drop_annot_def])
      >> BasicProvers.FULL_CASE_TAC
      >> gvs[drop_annot_def])
  >~ [‘Seq’]
  >- (Cases_on ‘c1’
      >> once_rewrite_tac[drop_annot_def,panSemTheory.evaluate_def]
      >> gvs[]
      >> pairarg_tac
      >> gvs[]
      >> BasicProvers.FULL_CASE_TAC
      >> gvs[drop_annot_def]
      >> once_rewrite_tac[panSemTheory.evaluate_def]
      >> gvs[]
      >> gvs[panSemTheory.evaluate_def])    
  >> rw[drop_annot_def,panSemTheory.evaluate_def]
  >> rpt BasicProvers.TOP_CASE_TAC
  >> gvs[]
QED
        
Theorem take_4_word64_to_bytes[simp]:
  TAKE 4 (word_to_bytes (w : word64) F) =
  word_to_bytes ((31 >< 0) w : word32) F
Proof
  rw[word_to_bytes_def,word_to_bytes_aux_compute,
     get_byte_def,byte_index_def,
     word_extract_def]
  >> FULL_BBLAST_TAC
QED

Theorem drop_take_4_bytes_32_cons[simp]:
  DROP 4 ((word_to_bytes (w : word32) F) ++ word_to_bytes w' F) = word_to_bytes w' F ∧
  TAKE 4 ((word_to_bytes (w : word32) F) ++ word_to_bytes w' F) = word_to_bytes w  F
Proof
  rw[word_to_bytes_def,word_to_bytes_aux_compute,
     get_byte_def,byte_index_def]
QED

Theorem take_4_bytes_32_w2w[simp]:
  TAKE 4 (word_to_bytes (w2w (w : word32) : word64) F) = word_to_bytes w F
Proof
  rw[word_to_bytes_def,word_to_bytes_aux_compute,
     get_byte_def,byte_index_def]
  >> FULL_BBLAST_TAC
QED
        
Theorem byte_align_idem[simp]:
  byte_align (byte_align w) = byte_align w
Proof
  irule (iffLR alignmentTheory.byte_align_aligned)
  >> gvs[alignmentTheory.byte_align_def,alignmentTheory.byte_aligned_def,alignmentTheory.aligned_align]
QED

Theorem word_of_bytes_word_to_bytes_64[simp]:
  ∀w : word64. word_of_bytes F 0w (word_to_bytes w F) = w
Proof
  irule byteTheory.word_of_bytes_word_to_bytes
  >> gvs[dividesTheory.compute_divides]
QED

Theorem word_of_bytes_word_to_bytes_32[simp]:
  ∀w : word32. word_of_bytes F 0w (word_to_bytes w F) = w
Proof
  irule byteTheory.word_of_bytes_word_to_bytes
  >> gvs[dividesTheory.compute_divides]
QED
        
Theorem take_4_word_to_bytes_w2w[simp]:
  TAKE 4 (word_to_bytes (w : word64) F) = word_to_bytes (w2w w : word32) F
Proof
  rw[byteTheory.word_to_bytes_def,byteTheory.word_to_bytes_aux_compute,byteTheory.get_byte_def,byteTheory.byte_index_def]
  >> FULL_BBLAST_TAC
QED

Theorem aligned_2_thm:
  ∀w : 'a word. dimword (:'a) ≥ 2 ∧ ¬w ' 0 ∧ ¬w ' 1 ⇒ aligned 2 w
Proof
  rw[alignmentTheory.aligned_def,alignmentTheory.align_shift]
  >> rw_tac (srw_ss() ++ fcpLib.FCP_ss) [wordsTheory.word_lsr_def,wordsTheory.word_lsl_def]
  >> iff_tac
  >> rw[]
  >- gvs[fcpTheory.FCP_BETA]
  >- (gvs[arithmeticTheory.GREATER_EQ,
          arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
          arithmeticTheory.LT_SUC]
      >> spose_not_then assume_tac
      >> gvs[arithmeticTheory.NOT_LT,
             arithmeticTheory.LE_LT])
  >> rw[fcpTheory.FCP_BETA]
  >> gvs[arithmeticTheory.GREATER_EQ,
         arithmeticTheory.LE_LT]
  >- (qabbrev_tac ‘P = λi. i + 2 < dimindex (:'a)’
      >> gvs[arithmeticTheory.SUB_ELIM_THM']
      >> unabbrev_all_tac
      >> rw[]
      >> gvs[]
      >> spose_not_then assume_tac
      >> gvs[arithmeticTheory.NOT_LT,
             arithmeticTheory.LE_LT]
      >| [rev_dxrule_all_then assume_tac arithmeticTheory.LESS_TRANS, ALL_TAC]
      >> ‘i < SUC 1’ by gvs[]
      >> gvs[GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
             arithmeticTheory.LE_LT])
  >- (last_x_assum $ assume_tac o GSYM
      >> gvs[]
      >> qabbrev_tac ‘P = λi. i + 2 < dimindex (:'a)’
      >> gvs[arithmeticTheory.SUB_ELIM_THM']
      >> unabbrev_all_tac
      >> rw[]
      >> gvs[]
      >> spose_not_then assume_tac
      >> gvs[arithmeticTheory.NOT_LT,
             arithmeticTheory.LE_LT]
      >| [rev_dxrule_all_then assume_tac arithmeticTheory.LESS_TRANS, ALL_TAC]
      >> ‘i < SUC 1’ by gvs[]
      >> gvs[GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
             arithmeticTheory.LE_LT])
  >- (qabbrev_tac ‘P = λi. w ' (i + 2)’
      >> gvs[arithmeticTheory.SUB_ELIM_THM']
      >> unabbrev_all_tac
      >> rw[]
      >> gvs[]
      >> ‘i < SUC 1’ by gvs[]
      >> gvs[GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
             arithmeticTheory.LE_LT])
  >> last_x_assum $ assume_tac o GSYM
  >> gvs[]
  >> qabbrev_tac ‘P = λi. w ' (i + 2)’
  >> gvs[arithmeticTheory.SUB_ELIM_THM']
  >> unabbrev_all_tac
  >> rw[]
  >> gvs[]
  >> ‘i < SUC 1’ by gvs[]
  >> gvs[GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
         arithmeticTheory.LE_LT]
QED

Theorem w2w_w2w_8_64_32[simp]:
  ∀w : word8. w2w (w2w w : word64) : word32 = w2w w
Proof
  BBLAST_TAC
QED

Theorem memory_only_words[simp]:
  ∀s addr. ∃w. s.memory addr = Word w
Proof
  Cases_on ‘s.memory addr’ >> gvs[]
QED

Theorem SNOC_NOT_PREFIX:
  ∀x l. ¬(SNOC x l ≼ l)
Proof
  strip_tac
  >> Induct
  >> gvs[listTheory.isPREFIX]
QED

Theorem TAKE_1_word_to_bytes_64_0w:
  TAKE 1 (word_to_bytes (0w : word64) F) = word_to_bytes (0w : word8) F
Proof
  gvs[byteTheory.word_to_bytes_def,byteTheory.word_to_bytes_aux_compute,byteTheory.get_byte_def]
QED

