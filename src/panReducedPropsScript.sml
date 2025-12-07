(*
  panReducedLang Properties
*)
Theory panReducedProps
Ancestors
  panReducedLang panReducedSem pan_commonProps
Libs
  preamble

Theorem mem_load_some_shape_eq:
  ∀sh adr dm (m: 'a word -> 'a word_lab) v.
  mem_load sh adr dm m = SOME v ==>
  shape_of v = sh
Proof
  qsuff_tac ‘(∀sh adr dm (m: 'a word -> 'a word_lab) v.
  mem_load sh adr dm m = SOME v ==> shape_of v = sh) /\
  (∀sh adr dm (m: 'a word -> 'a word_lab) v.
   mem_loads sh adr dm m = SOME v ==> MAP shape_of v = sh)’
  >- metis_tac [] >>
  ho_match_mp_tac mem_load_ind >> rw [mem_load_def] >>
  cases_on ‘sh’ >> fs [option_case_eq] >>
  rveq >> TRY (cases_on ‘m adr’) >> fs [shape_of_def] >>
  metis_tac []
QED

Definition v2word_def:
  v2word (ValWord v) = Word v
End

Theorem eval_upd_clock_eq:
  !t e ck. eval (t with clock := ck) e =  eval t e
Proof
  ho_match_mp_tac eval_ind >> rw [] >>
  fs [eval_def] >>
  qsuff_tac ‘OPT_MMAP (λa. eval (t with clock := ck) a) es =
             OPT_MMAP (λa. eval t a) es’ >>
  fs [] >>
  pop_assum mp_tac >>
   qid_spec_tac ‘es’ >>
   Induct >> rw [] >>
   fs [OPT_MMAP_def]
QED

Theorem evaluate_add_clock_eq:
  !p t res st ck.
   evaluate (p,t) = (res,st) /\ res <> SOME TimeOut ==>
    evaluate (p,t with clock := t.clock + ck) = (res,st with clock := st.clock + ck)
Proof
  recInduct evaluate_ind >> rw []
  >~ [‘While’]
  >- (once_rewrite_tac [evaluate_def] >>
      qpat_x_assum ‘evaluate _ = _’ mp_tac >>
      rw[Once evaluate_def] >>
      gvs[eval_upd_clock_eq,AllCaseEqs()] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs(),dec_clock_def]) >>
  gvs[evaluate_def,AllCaseEqs(),eval_upd_clock_eq] >>
  rpt(pairarg_tac >> gvs[]) >>
  gvs[oneline nb_op_def,AllCaseEqs(),
      set_var_def,
      set_global_def,
      empty_locals_def,
      dec_clock_def,
      lookup_kvar_def,
      set_kvar_def
     ] >>
  PURE_TOP_CASE_TAC >> gvs[]
QED

Theorem evaluate_clock_sub:
  !p t res st ck.
    evaluate (p,t) = (res,st with clock := st.clock + ck) ∧
    res <> SOME TimeOut ⇒
    evaluate (p,t with clock := t.clock - ck) = (res,st)
Proof
  (* TODO: generated names *)
  recInduct evaluate_ind >> rw []
  >~ [‘While’]
  >- (once_rewrite_tac [evaluate_def] >>
      qpat_x_assum ‘evaluate _ = _’ mp_tac >>
      rw[Once evaluate_def] >>
      gvs[eval_upd_clock_eq,AllCaseEqs()] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs(),dec_clock_def] >>
      imp_res_tac evaluate_clock >>
      gvs[] >>
      rw[state_component_equality] >>
      first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      rw[] >>
      last_x_assum $ qspecl_then [‘s1' with clock := s1'.clock - ck’,‘ck’] mp_tac >>
      (impl_tac >- rw[state_component_equality]) >>
      strip_tac >>
      gvs[])
  >~ [‘Seq’]
  >- (once_rewrite_tac [evaluate_def] >>
      qpat_x_assum ‘evaluate _ = _’ mp_tac >>
      rw[Once evaluate_def] >>
      gvs[eval_upd_clock_eq,AllCaseEqs()] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs(),dec_clock_def] >>
      imp_res_tac evaluate_clock >>
      gvs[] >>
      rw[state_component_equality] >>
      first_x_assum $ resolve_then (Pos hd) mp_tac EQ_REFL >>
      rw[] >>
      last_x_assum $ qspecl_then [‘s1' with clock := s1'.clock - ck’,‘ck’] mp_tac >>
      (impl_tac >- rw[state_component_equality]) >>
      strip_tac >>
      gvs[])
  >~ [‘Dec’]
  >- (once_rewrite_tac [evaluate_def] >>
      qpat_x_assum ‘evaluate _ = _’ mp_tac >>
      rw[Once evaluate_def] >>
      gvs[eval_upd_clock_eq,AllCaseEqs()] >>
      rpt(pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs(),dec_clock_def] >>
      imp_res_tac evaluate_clock >>
      gvs[]
      >- rw[state_component_equality] >>
      last_x_assum $ qspecl_then [‘st'' with clock := st''.clock - ck’,‘ck’] mp_tac >>
      (impl_tac >- gvs[state_component_equality]) >>
      strip_tac >>
      gvs[state_component_equality]) >>
  gvs[evaluate_def,state_component_equality,AllCaseEqs(),eval_upd_clock_eq,
      oneline nb_op_def, set_var_def, empty_locals_def,
      dec_clock_def,
      set_global_def, lookup_kvar_def, set_kvar_def
     ] >>
  rpt(pairarg_tac >> gvs[]) >>
  gvs[state_component_equality]
QED

Theorem evaluate_min_clock:
  evaluate (prog,s) = (q,r) ∧ q ≠ SOME TimeOut ⇒
  ∃k. evaluate (prog,s with clock := k) = (q,r with clock := 0)
Proof
  qabbrev_tac ‘x = r with clock := 0’>>
  ‘r = x with clock := x.clock + r.clock’
    by simp[state_component_equality,Abbr‘x’]>>
  pop_assum (fn h => rewrite_tac[Once h])>>strip_tac>>
  drule_all evaluate_clock_sub>>
  strip_tac>>fs[]>>metis_tac[]
QED

Theorem update_locals_not_vars_eval_eq:
  ∀s e v n w.
  ~MEM n (var_exp e) /\
  eval s e = SOME v ==>
  eval (s with locals := s.locals |+ (n,w)) e = SOME v
Proof
  ho_match_mp_tac eval_ind >>
  rpt conj_tac >> rpt gen_tac
  >~ [‘Struct’]
  >- (fs [var_exp_def] >>
      rpt strip_tac >>
      gvs[eval_def,AllCaseEqs()] >>
      imp_res_tac opt_mmap_el >>
      imp_res_tac opt_mmap_length_eq >>
      gvs[opt_mmap_eq_some] >>
      irule LIST_EQ >>
      rw[EL_MAP] >>
      first_x_assum irule >>
      simp[MEM_EL,PULL_EXISTS] >>
      irule_at (Pos last) EQ_REFL >>
      simp[] >>
      rw[] >>
      gvs[MEM_FLAT,MEM_MAP,MEM_EL,PULL_FORALL, SF DNF_ss] >>
      metis_tac[]) >>
  rw[] >>
  gvs[eval_def,var_exp_def, lookup_kvar_def, FLOOKUP_UPDATE,AllCaseEqs(),
      PULL_EXISTS] >>
  ntac 2 $ first_assum $ irule_at $ Pos last >>
  imp_res_tac opt_mmap_el >>
  imp_res_tac opt_mmap_length_eq >>
  gvs[opt_mmap_eq_some] >>
  irule LIST_EQ >>
  rw[EL_MAP] >>
  first_x_assum irule >>
  simp[MEM_EL,PULL_EXISTS] >>
  irule_at (Pos last) EQ_REFL >>
  simp[] >>
  rw[] >>
  gvs[MEM_FLAT,MEM_MAP,MEM_EL,PULL_FORALL, SF DNF_ss] >>
  metis_tac[]
QED
