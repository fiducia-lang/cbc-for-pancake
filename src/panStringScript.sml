(* Zero-Terminated Strings in Pancake Memory *)
Theory panString
Ancestors panSem alignment arithmetic words
Libs blastLib
          
Definition array_def:
  array start length addr ⇔ start ≤₊ addr ∧ addr <₊ start + length
End

Theorem array_not_nil:
  ∀start addr. ¬array start 0w addr
Proof
  rw[array_def]
  >> qspecl_then [‘addr’,‘start’] assume_tac wordsTheory.WORD_LOWER_EQ_CASES
  >> gvs[wordsTheory.WORD_NOT_LOWER]
QED

Definition aligned_array_def:
  aligned_array (start : 'a word) (length : 'a word) ⇔ byte_aligned start ∧ byte_aligned length
End

Theorem aligned_array_corr:
  ∀start length. aligned_array start length ⇒ (∀addr. array start length (byte_align addr) ⇒ array start length addr) ∧
                                              (∀addr. array start length addr ⇒ array start length (byte_align addr))
Proof
  rw[aligned_array_def,array_def]
  >- (dxrule_then assume_tac WORD_LOWER_EQ_TRANS
      >> first_x_assum $ irule
      >> gvs[byte_align_def,align_ls])
  >- (dxrule_then (drule_then assume_tac) byte_aligned_add
      >> gvs[byte_align_def,byte_aligned_def]
      >> qmatch_asmsub_abbrev_tac ‘aligned b _’
      >> Cases_on ‘aligned b addr’
      >- gvs[align_aligned]
      >> irule aligned_between
      >> qexists ‘b’
      >> gvs[WORD_ADD_COMM])
  >- (gvs[byte_align_def,byte_aligned_def]
      >> qmatch_asmsub_abbrev_tac ‘aligned b _’
      >> Cases_on ‘aligned b addr’
      >- gvs[align_aligned]
      >> spose_not_then assume_tac
      >> gvs[WORD_NOT_LOWER_EQUAL]
      >> dxrule_all_then assume_tac aligned_between
      >> gvs[GSYM WORD_NOT_LOWER_EQUAL])
  >- (gvs[byte_align_def]
      >> irule WORD_LOWER_EQ_LOWER_TRANS
      >> qexists ‘addr’
      >> gvs[align_ls])
QED

Definition wf_array_def:
  wf_array (start : 'a word) (length : 'a word) ⇔ w2n start + w2n length < dimword (:'a)
End

Theorem wf_array_corr:
  ∀start length. wf_array start length ⇒ start ≤₊ start + length
Proof
  rw[wf_array_def]
  >> dxrule_then assume_tac w2n_add_2
  >> gvs[WORD_LS,WORD_ADD_COMM]
QED

Theorem start_in_wf_array:
  ∀start length. wf_array start length ∧ length >₊ 0w ⇒ array start length start
Proof
  rw[wf_array_def,array_def]
  >> dxrule_then assume_tac w2n_add_2
  >> gvs[WORD_LO,WORD_ADD_COMM,WORD_HIGHER]
QED

(* TODO REWRITE WITHOUT BITBLASTING FROM HERE *)
        
Theorem wf_array_not_last:
  ∀start length addr : word64. wf_array start length ∧ array start length addr ∧ addr ≠ start + length - 1w ⇒ array start length (addr + 1w)
Proof
  rw[array_def]
  >> dxrule_then assume_tac wf_array_corr
  >> FULL_BBLAST_TAC
QED
        
Definition wf_aligned_array_def:
  wf_aligned_array start length ⇔ wf_array start length ∧ aligned_array start length
End
        
Theorem wf_array_len_pre:
  ∀start length : word64. wf_array start length ∧ length >₊ 0w ⇒ wf_array start (length - 1w) ∧
                                                                 ∀addr. array start length addr ∧ addr ≠ start + length - 1w ⇒ array start (length - 1w) addr
Proof
  rw[]
  >- (gvs[wf_array_def]
      >> ‘w2n (length' - 1w) < w2n length'’ suffices_by gvs[]
      >> irule WORD_PRED_THM
      >> gvs[WORD_HIGHER,WORD_LO_word_0])
  >> drule_all_then assume_tac wf_array_corr
  >> gvs[array_def]
  >> FULL_BBLAST_TAC
QED

Theorem wf_array_len_suc:
  ∀start length : word64. wf_array start length ∧ start + length ≠ -1w ⇒ wf_array start (length + 1w) ∧
                                                                         ∀addr. array start length addr ⇒ array start (length + 1w) addr
Proof
  rw[]
  >- (drule_then assume_tac wf_array_corr
      >> dxrule_then assume_tac ((iffRL o cj 2) WORD_LO_word_T)
      >> gvs[WORD_LO]
      >> last_x_assum $ mp_tac
      >> pure_rewrite_tac [wf_array_def]
      >> strip_tac
      >> drule_then assume_tac w2n_add_2
      >> gvs[]
      >> pop_assum $ kall_tac
      >> ‘w2n (length' + 1w) = w2n length' + w2n (1w : word64)’ suffices_by gvs[]
      >> irule w2n_add_2
      >> gvs[])
  >> gvs[array_def]                       
  >> FULL_BBLAST_TAC
QED

Theorem wf_array_start_suc:
  ∀start length : word64. wf_array start length ∧ length >+ 0w ⇒ wf_array (start + 1w) (length - 1w)
Proof
  rw[]
  >> drule_then assume_tac (cj 1 wf_array_len_pre)
  >> gvs[]
  >> rpt (qpat_x_assum ‘wf_array _ _’ $ mp_tac)
  >> pure_rewrite_tac [wf_array_def]
  >> rpt strip_tac
  >> qsuff_tac ‘w2n ((start + 1w) + (length' + -1w)) = w2n (start + 1w) + w2n (length' + -1w)’
  >- (strip_tac
      >> ‘w2n (start + length') = w2n start + w2n length'’ by gvs[w2n_add_2]
      >> gvs[])
  >> irule w2n_add_2
  >> qsuff_tac ‘start + length' + -1w ≠ -1w’
  >- (strip_tac
      >> dxrule_then assume_tac ((iffRL o cj 2) WORD_LO_word_T)
      >> drule_then assume_tac w2n_add_2
      >> gvs[WORD_LO,WORD_ADD_ASSOC]
      >> ‘w2n (start + 1w) = w2n start + w2n (1w : word64)’ suffices_by gvs[]
      >> irule w2n_add_2
      >> gvs[])
  >> spose_not_then assume_tac
  >> rev_drule_then assume_tac w2n_add_2
  >> gvs[]
QED
        
Definition zts_def:
  zts start len mem addrset be ⇔ len ≠ -1w ∧
                                 wf_array start (len + 1w) ∧
                                 get_byte (start + len) (mem (byte_align (start + len))) be = 0w ∧
                                 (∀addr. array start (len + 1w) addr ⇒ addrset (byte_align addr)) ∧
                                 (∀addr. array start len        addr ⇒ get_byte addr (mem (byte_align addr)) be ≠ 0w)
End

Theorem zts_corr:
  zts (start : word64) len memory addrset be ⇒ wf_array start len
Proof
  rw[zts_def]
  >> drule_then assume_tac (cj 1 wf_array_len_pre)
  >> gvs[]
  >> pop_assum $ irule
  >> gvs[WORD_HIGHER,WORD_LO_word_0]
  >> spose_not_then assume_tac
  >> gvs[WORD_SUM_ZERO]
QED
        
Theorem zts_start_suc:
  ∀mem addrset be start len : word64. zts start len mem addrset be ∧ len >+ 0w ⇒ zts (start + 1w) (len - 1w) mem addrset be
Proof
  rw[zts_def]
  >- gvs[WORD_HIGHER,WORD_LO_word_0]
  >- (drule_then assume_tac wf_array_start_suc
      >> gvs[]
      >> pop_assum $ irule
      >> gvs[WORD_HIGHER,WORD_LO_word_0]
      >> spose_not_then assume_tac
      >> gvs[WORD_SUM_ZERO])
  >> first_x_assum $ irule
  >> drule_then assume_tac wf_array_corr
  >> gvs[array_def]
  >> FULL_BBLAST_TAC
QED

Definition zts_at_def:
  zts_at start mem addrset be ⇔ ∃len. zts start len mem addrset be
End

Theorem zts_therefore_zts_at:
  ∀start len mem addrset be. zts start len mem addrset be ⇒ zts_at start mem addrset be
Proof
  rw[zts_at_def]
  >> gvs[SF SFY_ss]
QED
        
Theorem zts_at_start_addrset:
  zts_at (start : word64) memory addrset be ⇒ addrset (byte_align start)
Proof
  rw[zts_at_def,zts_def]
  >> first_x_assum $ irule
  >> drule_then assume_tac wf_array_corr
  >> gvs[array_def]
  >> FULL_BBLAST_TAC
QED

Theorem len_is_unique:
  ∀len1 len2 : word64. zts start len1 memory addrset be ∧ zts start len2 memory addrset be ⇒ len1 = len2
Proof
  rw[]
  >> drule_then assume_tac zts_corr
  >> rev_drule_then assume_tac zts_corr
  >> gvs[zts_def,array_def]
  >> rpt (dxrule_then assume_tac wf_array_corr)
  >> gvs[]
  >> Cases_on ‘len1 + start <+ len2 + start’
  >- (first_x_assum $ drule_all_then assume_tac >> gvs[])
  >> gvs[wordsTheory.WORD_NOT_LOWER,wordsTheory.WORD_LOWER_OR_EQ]
QED

        
Theorem zts_ne_then:
  zts_at start memory addrset be ∧ get_byte start (memory (byte_align start) : word64) be ≠ 0w ⇒ zts_at (start + 1w) memory addrset be ∧
                                                                                                 ∃len. len >₊ 0w ∧ zts start len memory addrset be
Proof
  rw[zts_at_def]
  >> drule_then assume_tac zts_corr
  >> gvs[zts_def]
  >> ‘0w <₊ len’ by (‘len ≠ 0w’ suffices_by gvs[wordsTheory.WORD_LO_word_0]
                     >> spose_not_then assume_tac
                     >> gvs[zts_def])
  >> rw[]
  >- (qexists ‘len - 1w’
      >> rw[]
      >- gvs[WORD_LO_word_0]
      >- (rev_drule_then assume_tac wf_array_start_suc
          >> gvs[]
          >> pop_assum $ irule
          >> gvs[WORD_HIGHER,WORD_LO_word_0]
          >> spose_not_then assume_tac
          >> gvs[WORD_SUM_ZERO])
      >> first_x_assum $ irule
      >> gvs[array_def]
      >> rw[]
      >> rpt (dxrule_all_then assume_tac wf_array_corr)
      >- (irule wordsTheory.WORD_LOWER_EQ_TRANS
          >> qexists ‘start + 1w’
          >> gvs[]
          >> ‘start <=+ 1w + start’ suffices_by gvs[]
          >> FULL_BBLAST_TAC)
      >> FULL_BBLAST_TAC)
  >> qexists ‘len’
  >> gvs[WORD_HIGHER,WORD_LO_word_0]
  >> spose_not_then assume_tac
  >> gvs[WORD_SUM_ZERO]
QED

Definition get_zts_def:
  get_zts (start : word64) mem addrset be = if (zts_at start mem addrset be) then
                                   if (get_byte start (mem (byte_align start)  : word64) be ≠ 0w) then
                                     (get_byte start (mem (byte_align start)) be) :: (get_zts (start + 1w) mem addrset be)
                                   else
                                     [0w]
                                 else
                                   []
Termination
  WF_REL_TAC ‘measure (λ(start,mem,addrset,be). w2n (@len. zts start len mem addrset be))’
  >> rw[]
  >> ‘zts_at (start + 1w) mem' addrset be’ by gvs[zts_ne_then]
  >> gvs[zts_at_def]
  >> ‘0w <₊ len’ by (‘len ≠ 0w’ suffices_by gvs[wordsTheory.WORD_LO_word_0]
                     >> spose_not_then assume_tac
                     >> gvs[zts_def])
  >> ‘len = (@len. zts start len mem' addrset be)’ by (irule ((INST_TYPE [“:'b” |-> “:'a”] o INST_TYPE [“:'a” |-> “:64”]) len_is_unique)
                                         >> qexistsl [‘addrset’, ‘be’, ‘mem'’, ‘start’]
                                         >> gvs[]
                                         >> qabbrev_tac ‘P = λlen. zts start len mem' addrset be’
                                         >> gvs[]
                                         >> ‘P (@x. P x)’ suffices_by metis_tac[]
                                         >> irule (iffRL SELECT_THM)
                                         >> qexists ‘len’
                                         >> gvs[])
  >> ‘len' = (@len. zts (start + 1w) len mem' addrset be)’ by (irule ((INST_TYPE [“:'b” |-> “:'a”] o INST_TYPE [“:'a” |-> “:64”]) len_is_unique)
                                                 >> qexistsl [‘addrset’, ‘be’, ‘mem'’, ‘start + 1w’]
                                                 >> gvs[]
                                                 >> qabbrev_tac ‘P = λlen. zts (start + 1w) len mem' addrset be’
                                                 >> gvs[]
                                                 >> ‘P (@x. P x)’ suffices_by metis_tac[]
                                                 >> irule (iffRL SELECT_THM)
                                                 >> qexists ‘len'’
                                                 >> gvs[])
  >> ‘len' <+ len’ suffices_by gvs[wordsTheory.WORD_LO]
  >> rpt (qpat_x_assum ‘_ = @x. P x’ $ kall_tac)
  >> spose_not_then assume_tac
  >> drule_then assume_tac zts_corr
  >> rev_drule_then assume_tac zts_corr
  >> gvs[wordsTheory.WORD_NOT_LOWER,zts_def]
  >> qpat_x_assum ‘get_byte (len + start) _ _ = _’ $ mp_tac
  >> gvs[]
  >> first_x_assum $ irule
  >> rw[array_def]
  >> rpt (dxrule_then assume_tac wf_array_corr)
  >> FULL_BBLAST_TAC
End

Theorem get_zts_not_null:
  ∀start mem addrset be. zts_at start mem addrset be ⇒ get_zts start mem addrset be ≠ []
Proof
  rw[Once get_zts_def]     
QED                    
