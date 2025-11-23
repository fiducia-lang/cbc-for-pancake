(*
  panReducedLang Properties
*)
Theory panReducedProps
Ancestors
  panReducedLang panReducedSem
Libs
  preamble

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
