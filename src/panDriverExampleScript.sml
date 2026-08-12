(* The driver example *)
Theory panDriverExample
Ancestors panLang panSem panPredicate panWeakestPrecondition panString panRefinement panMisc
Libs panRefinementLib blastLib finite_mapLib listLib numLib


(* Register Definitions *)
Definition AUX_IRQ_def:
  AUX_IRQ base = base + 0w : word64
End
    
Definition AUX_MU_IO_REG_def:
  AUX_MU_IO_REG base = base + 64w : word64
End

Definition AUX_MU_IER_REG_def:
  AUX_MU_IER_REG base = base + 68w : word64
End

Definition AUX_MU_IIR_REG_def:
  AUX_MU_IIR_REG base = base + 72w : word64
End

Definition AUX_MU_LSR_REG_def:
  AUX_MU_LSR_REG base = base + 84w : word64
End

Definition conf_registers_def:
  conf_registers base = {AUX_MU_IER_REG base}
End

Definition status_registers_def:
  status_registers base = {AUX_IRQ base; AUX_MU_IIR_REG base; AUX_MU_LSR_REG base}
End

Definition registers_def:
  registers base = conf_registers base ∪ status_registers base ∪ {AUX_MU_IO_REG base}
End


(* FFI Definitions *)
Datatype:
  ffi_state = <| registers:    word64 |-> word32
               ; write_buffer: word64  -> word64 |>
End

val ffi_state_component_equality = theorem "ffi_state_component_equality";

Definition uart_ffi_def:
  uart_ffi = λmem b aux_base name state conf data. case name of
                                                   | (SharedMem MappedRead) => (case conf of
                                                     | [4w] => let addr = (word_of_bytes F 0w data) in
                                                       if (FDOM state.registers addr ∧ ((conf_registers aux_base) ∪ (status_registers aux_base)) addr) then
                                                         Oracle_return state (word_to_bytes (w2w (state.registers ' addr) : word64) F)
                                                       else Oracle_final FFI_failed
                                                     | [1w] => let addr = (word_of_bytes F 0w data) in
                                                       if (array (unbox (mem (b + 16w))) (unbox (mem (b + 24w))) (byte_align addr)) then
                                                         Oracle_return state (word_to_bytes (w2w (get_byte addr (state.write_buffer (byte_align addr)) F) : word64) F)
                                                       else Oracle_final FFI_failed
                                                     | _    => Oracle_final FFI_failed)
                                                   | (SharedMem MappedWrite) => (case conf of
                                                     | [4w] => let addr = (word_of_bytes F 0w (DROP 4 data)) in
                                                       if (FDOM state.registers addr ∧ (conf_registers aux_base) addr) then
                                                         Oracle_return (state with registers := state.registers |+ (addr,word_of_bytes F 0w (TAKE 4 data))) data
                                                       else (if (addr = (AUX_MU_IO_REG aux_base) ∧ state.registers ' (AUX_MU_LSR_REG aux_base) ' 5) then
                                                         Oracle_return state data
                                                       else
                                                         Oracle_final FFI_failed)
                                                       | _    => Oracle_final FFI_failed)
                                                   | (ExtCall "microkit_irq_ack") => (case (conf,data) of
                                                       | ([w],[]) => Oracle_return state data
                                                       | _        => Oracle_final FFI_failed)
                                                   | _ => Oracle_final FFI_failed
End


(* Resulting Functions *)
val fun_get_bits = parse ‘
fun get_bits(1 register, 1 bitmask) {
    var value = 0;
    !ld32 value, register;
    return value & bitmask;
}
’;

val fun_set_bits = parse ‘
fun set_bits(1 register, 1 bitmask, 1 bit) {
    var value = 0;
    !ld32 value, register;

    if (bit) {
        value = value | bitmask;
    } else {
        value = value & (bitmask ^ -1);
    }

    !st32 register, value;
    return 0;
}
’;
        
val fun_set_transmit_interrupt = parse ‘
fun set_transmit_interrupt(1 transmit_interrupt) {
    return set_bits(aux_base_vaddr + 68, 1, transmit_interrupt);
}
’;

val fun_set_receive_interrupt = parse ‘
fun set_receive_interrupt(1 receive_interrupt) {
    return set_bits(aux_base_vaddr + 68, (1 << 1), receive_interrupt);
}
’;

val fun_putc = parse ‘
fun putc(1 char) {
    var aux_mu_lsr_reg = 0;
    while (!(aux_mu_lsr_reg & (1 << 5))) {
        !ld32 aux_mu_lsr_reg, aux_base_vaddr + 84;
    }
    !st32 aux_base_vaddr + 64, char;
    return 0;
}
’;

val fun_puts = parse ‘
fun puts(1 buffer) {
    var char = 0;
    !ld8 char, buffer;

    while (char != 0) {
        putc(char);
        buffer = buffer + 1;
        !ld8 char, buffer;
    }

    return 0;
}
’;
        
val fun_main = parse ‘
fun main() {
    aux_base_vaddr = lds 1 @base;
    aux_len = lds 1 (@base + @biw);
    write_buffer_vaddr = lds 1 (@base + @biw * 2);
    write_buffer_len = lds 1 (@base + @biw * 3);
 
    set_transmit_interrupt(0);
    set_receive_interrupt(0);

    return 0;
}
’;

val fun_notified = parse ‘
export fun notified(1 channel) {
    if (channel == 1) {
        puts(write_buffer_vaddr);
    } else {
        return 1;
    }

    return 0;
}
’;

(* Program and Device Invariants *)
Definition uart_globals_def:
  uart_globals b aux_base = λs. s.memaddrs = {0w; b; b + 8w; b + 16w; b + 24w} ∧
                                ¬s.be ∧
                                s.eshapes = FEMPTY ∧
                                s.base_addr = b ∧
                                s.code = (FEMPTY |+ (strlit "get_bits",^fun_get_bits)
                                                 |+ (strlit "set_bits",^fun_set_bits)
                                                 |+ (strlit "set_transmit_interrupt",^fun_set_transmit_interrupt)
                                                 |+ (strlit "set_receive_interrupt",^fun_set_receive_interrupt)
                                                 |+ (strlit "putc",^fun_putc)
                                                 |+ (strlit "puts",^fun_puts)
                                                 |+ (strlit "main",^fun_main)
                                                 |+ (strlit "notified",^fun_notified)) ∧
                                s.memory b = Word aux_base ∧
                                FDOM s.ffi.ffi_state.registers = registers aux_base ∧
                                s.ffi.oracle = uart_ffi s.memory b aux_base ∧
                                has_kvar_vw Global (strlit "aux_base_vaddr") s ∧
                                has_kvar_vw Global (strlit "aux_len") s ∧
                                has_kvar_vw Global (strlit "write_buffer_vaddr") s ∧
                                has_kvar_vw Global (strlit "write_buffer_len") s ∧
                                let aux_len           = unbox (s.memory (b + 8w));
                                    write_buffer_base = unbox (s.memory (b + 16w));
                                    write_buffer_len  = unbox (s.memory (b + 24w)) in
                                  wf_aligned_array aux_base aux_len ∧
                                  wf_aligned_array write_buffer_base write_buffer_len ∧
                                  s.sh_memaddrs = (IMAGE byte_align (registers aux_base)
                                                   ∪ (array aux_base aux_len)
                                                   ∪ (array write_buffer_base write_buffer_len)) ∧
                                  DISJOINT (conf_registers aux_base) (status_registers aux_base) ∧
                                  DISJOINT (conf_registers aux_base) (array aux_base aux_len) ∧
                                  DISJOINT (conf_registers aux_base) (array write_buffer_base write_buffer_len) ∧
                                  DISJOINT (status_registers aux_base) (array aux_base aux_len) ∧
                                  DISJOINT (status_registers aux_base) (array write_buffer_base write_buffer_len) ∧
                                  DISJOINT (array aux_base aux_len) (array write_buffer_base write_buffer_len)
End

Theorem uart_globals_locals_eq:
  ∀s l base aux_base. uart_globals base aux_base (s with locals := l) ⇔ uart_globals base aux_base s
Proof
  rw[uart_globals_def,has_kvar_vw_def,lookup_kvar_def]
QED

Theorem uart_globals_clock_eq:
  ∀s k base aux_base. uart_globals base aux_base (s with clock := k) ⇔ uart_globals base aux_base s
Proof
  rw[uart_globals_def,has_kvar_vw_def,lookup_kvar_def]
QED
        
Theorem uart_globals_io_events_eq:
  ∀s e base aux_base. uart_globals base aux_base (s with ffi := s.ffi with io_events := e) ⇔ uart_globals base aux_base s
Proof
  rw[uart_globals_def,has_kvar_vw_def,lookup_kvar_def]
QED

(* Refinement of Functions *)
Definition fun_get_bits_contract:
  fun_get_bits_contract reg mask ffi_pre registers mem base aux_base globals =
  FunContract [("register",word_with (λw. w = reg ∧ (conf_registers aux_base w ∨ status_registers aux_base w)));("bitmask",the_word mask)]
              (λs. ffi_pre s.ffi.ffi_state s.ffi.io_events ∧
                   s.ffi.ffi_state.registers = registers ∧
                   FDOM s.ffi.ffi_state.registers reg ∧
                   s.globals = globals ∧
                   s.memory = mem ∧
                   uart_globals base aux_base s)
              (λt. ffi_pre t.ffi.ffi_state (FRONT t.ffi.io_events) ∧
                   t.ffi.ffi_state.registers = registers ∧
                   FDOM t.ffi.ffi_state.registers reg ∧
                   t.globals = globals ∧
                   t.memory = mem ∧
                   t.ffi.io_events ≠ [] ∧
                   (∃b. LENGTH b = 8 ∧ LAST t.ffi.io_events = IO_event (SharedMem MappedRead) [4w] (ZIP (word_to_bytes reg F,b))) ∧
                   uart_globals base aux_base t)
              (word_with (λr. r = (w2w (registers ' reg)) && mask))
End

Theorem fun_get_bits_thm:
  ∀reg mask ffi_pre registers mem base aux_base globals.
  (fun_get_bits_contract reg mask ffi_pre registers mem base aux_base globals)
  refine
  (PanC (code ^fun_get_bits))
Proof
  begin_refinement_tac fun_get_bits_contract
  >> apply_dec
  >> apply_seq ‘M = (λs. P (s with <| locals := s.locals |+ (strlit "value",ValWord 0w); ffi := s.ffi with io_events := FRONT s.ffi.io_events |>) ∧
                         FLOOKUP s.locals (strlit "value") = SOME (ValWord (w2w (registers' ' reg))) ∧
                         s.ffi.io_events ≠ [] ∧
                         ffi_pre s.ffi.ffi_state (FRONT s.ffi.io_events) ∧
                         (∃b. LENGTH b = 8 ∧ LAST s.ffi.io_events = IO_event (SharedMem MappedRead) [4w] (ZIP (word_to_bytes reg F,b))))’
  >- (apply_shmemload uart_ffi_def
      >>~- ([‘s.sh_memaddrs _’],(gvs[uart_globals_def] >> rpt disj1_tac >> qexists ‘reg’ >> simp[registers_def,IN_DEF]))
      >> gvs[uart_globals_def]
      >> simp[uart_ffi_def,registers_def,IN_DEF]
      >> gvs[has_kvar_vw_def,lookup_kvar_def,rich_listTheory.FRONT_APPEND]
      >| [disj1_tac, disj2_tac]
      >> qexists ‘word_to_bytes (w2w (s.ffi.ffi_state.registers ' reg) : word64) F’ >> gvs[])
  >> apply_return
  >> qexists ‘b’
  >> gvs[uart_globals_locals_eq,uart_globals_io_events_eq]
QED

Definition fun_set_bits_contract:
  fun_set_bits_contract reg mask bit ffi_pre_state globals memory base aux_base =
         FunContract [("register",word_with (λw. w = reg ∧ conf_registers aux_base reg));
                      ("bitmask",the_word mask);
                      ("bit",the_word bit)]
                     (λs. s.ffi.ffi_state = ffi_pre_state ∧
                          s.globals = globals ∧
                          s.memory = memory ∧
                          FDOM s.ffi.ffi_state.registers reg ∧
                          uart_globals base aux_base s)
                     (λt. t.ffi.ffi_state = ffi_pre_state with registers :=
                                            (if bit = 0w then
                                               ffi_pre_state.registers |+ (reg,((ffi_pre_state.registers ' reg) && (¬(w2w mask))))
                                             else
                                               ffi_pre_state.registers |+ (reg,(ffi_pre_state.registers ' reg) || (w2w mask))) ∧
                          t.globals = globals ∧
                          t.memory = memory ∧
                          FDOM t.ffi.ffi_state.registers reg ∧
                          uart_globals base aux_base t)
                     (word_with (λr. r = 0w))
End

Theorem fun_set_bits_thm:
  ∀reg mask bit ffi_pre_state globals memory base aux_base.
  (fun_set_bits_contract reg mask bit ffi_pre_state globals memory base aux_base)
  refine
  (PanC (code ^fun_set_bits))
Proof
  begin_refinement_tac fun_set_bits_contract
  >> apply_dec
  >> apply_seq ‘M = (λs. P (s with locals := s.locals |+ (strlit "value",ValWord 0w)) ∧
                         FLOOKUP s.locals (strlit "value") = SOME (ValWord (w2w (ffi_pre_state.registers ' reg))))’
  >>~- ([‘ShMemLoad’],apply_shmemload uart_ffi_def
                      >> gvs[uart_globals_def,has_kvar_vw_def,lookup_kvar_def]
                      >- ASM_SET_TAC[]
                      >- (rpt disj1_tac >> qexists ‘reg’ >> simp[registers_def,IN_DEF])
                      >- (simp[uart_ffi_def,registers_def,IN_DEF]))
  >> Cases_on ‘bit = 0w’
  >| [apply_seq ‘M = (λs. P (s with locals := s.locals |+ ((strlit "value"),
                          ValWord (w2w (ffi_pre_state.registers ' reg)))) ∧
                          (FLOOKUP s.locals (strlit "value")) = SOME (ValWord (¬mask && w2w (ffi_pre_state.registers ' reg))))’,
      apply_seq ‘M = (λs. P (s with locals := s.locals |+ ((strlit "value"),
                          ValWord (w2w (ffi_pre_state.registers ' reg)))) ∧
                          (FLOOKUP s.locals (strlit "value")) = SOME (ValWord (mask || w2w (ffi_pre_state.registers ' reg))))’]
  >>~- ([‘If’],(apply_if >> apply_assign))
  >> apply_seq ‘M = λs. Q (SOME (Return (ValWord 0w)),empty_locals s)’
  >> gvs[empty_locals_def]
  >>~- ([‘ShMemStore’],(apply_shmemstore uart_ffi_def
                        >- ASM_SET_TAC[]
                        >- (gvs[uart_globals_def] >> ASM_SET_TAC[])
                        >> gvs[uart_globals_def,has_kvar_vw_def,lookup_kvar_def]
                        >> simp[uart_ffi_def,registers_def,IN_DEF]
                        >> conj_tac
                        >- (qmatch_goalsub_abbrev_tac ‘_ with registers := _ |+ (_,a) = _ with registers := _ |+ (_,b)’
                            >> ‘a = b’ suffices_by gvs[]
                            >> unabbrev_all_tac
                            >> BBLAST_TAC)
                        >> ASM_SET_TAC[]))
  >> apply_return
QED

Definition with_transmit_interrupts_enabled_def:
  with_transmit_interrupts_enabled ffi aux_base st =
  ffi with registers :=
      (ffi.registers |+ (AUX_MU_IER_REG aux_base,
                           (if st then
                              (ffi.registers ' (AUX_MU_IER_REG aux_base)) || 1w
                            else
                              (ffi.registers ' (AUX_MU_IER_REG aux_base)) && -2w)))
End

Definition transmit_interrupts_enabled_def:
  transmit_interrupts_enabled ffi aux_base ⇔ ffi.registers ' (AUX_MU_IER_REG aux_base) ' 0
End

Theorem transmit_interrupts_enabled_eq[simp]:
  ∀ffi b b' aux_base. (transmit_interrupts_enabled (ffi with write_buffer := b') aux_base ⇔ transmit_interrupts_enabled ffi aux_base)
Proof
  rw[transmit_interrupts_enabled_def]
QED

Theorem transmit_interrupts_enabled_thm:
  ∀ffi aux_base.
       transmit_interrupts_enabled (with_transmit_interrupts_enabled ffi aux_base T) aux_base ∧
        ¬transmit_interrupts_enabled (with_transmit_interrupts_enabled ffi aux_base F) aux_base ∧
        ∀reg bit st. (reg ≠ AUX_MU_IER_REG aux_base ∨ (bit > 0 ∧ bit < 32)) ⇒
                     ffi.registers ' reg ' bit =
                     (with_transmit_interrupts_enabled ffi aux_base st).registers ' reg ' bit
Proof
  rw[with_transmit_interrupts_enabled_def,transmit_interrupts_enabled_def]
  >- FULL_BBLAST_TAC
  >- FULL_BBLAST_TAC
  >> iff_tac
  >> Cases_on ‘reg = AUX_MU_IER_REG aux_base’
  >> rw[]
  >> gvs[finite_mapTheory.FAPPLY_FUPDATE_THM]
  >> qabbrev_tac ‘w = ffi.registers ' (AUX_MU_IER_REG aux_base)’
  >> qpat_x_assum ‘Abbrev _’ $ kall_tac
  >> rpt (last_x_assum $ mp_tac)
  >> qid_spec_tac ‘bit’
  >> rpt (CONV_TAC (BOUNDED_FORALL_CONV ALL_CONV) >> conj_tac >- FULL_BBLAST_TAC)
  >> rw[]
QED

Definition fun_set_transmit_interrupt_contract:
  fun_set_transmit_interrupt_contract transmit_interrupt ffi_pre_state globals memory base aux_base =
          FunContract [("transmit_interrupt",the_word transmit_interrupt)]
                      (λs. s.ffi.ffi_state = ffi_pre_state ∧
                           s.globals = globals ∧
                           s.globals ' (strlit "aux_base_vaddr") = ValWord (aux_base) ∧
                           s.memory = memory ∧
                           uart_globals base aux_base s)
                      (λt. uart_globals base aux_base t ∧
                           t.globals = globals ∧
                           t.memory = memory ∧
                           t.ffi.ffi_state = with_transmit_interrupts_enabled ffi_pre_state aux_base (transmit_interrupt ≠ 0w))
                      (word_with (λr. r = (0w : word64)))
End

Theorem fun_set_transmit_interrupt:
  ∀transmit_interrupt ffi_pre_state globals memory base aux_base.
  (fun_set_transmit_interrupt_contract transmit_interrupt ffi_pre_state globals memory base aux_base)
  refine
  (PanC (code ^fun_set_transmit_interrupt))
Proof
  begin_refinement_tac fun_set_transmit_interrupt_contract
  >> irule tailcall_refinement_rule
  >> rw[lookup_code_def,eval_def,finite_mapTheory.FLOOKUP_DEF,finite_mapTheory.FUPDATE_LIST,shape_of_def]
  >- gvs[uart_globals_def,has_kvar_vw_def,lookup_kvar_def,wordLangTheory.word_op_def,finite_mapTheory.FLOOKUP_DEF]
  >- gvs[uart_globals_def,has_kvar_vw_def,lookup_kvar_def,wordLangTheory.word_op_def,finite_mapTheory.FLOOKUP_DEF]
  >> gvs[uart_globals_def,has_kvar_vw_def,lookup_kvar_def,wordLangTheory.word_op_def,finite_mapTheory.FLOOKUP_DEF,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FAPPLY_FUPDATE_THM]
  >> irule refine_to_prog_hoare
  >> irule refine_transitive
  >> qexists ‘fun_set_bits_contract (AUX_MU_IER_REG aux_base) 1w transmit_interrupt s.ffi.ffi_state s.globals s.memory s.base_addr aux_base’
  >> reverse (conj_tac)
  >- gvs[REWRITE_RULE [code_def] fun_set_bits_thm]
  >> gvs[fun_set_bits_contract,fun_contract_def]
  >> irule both_pre_post_refinement_rule
  >> rw[empty_locals_def,with_transmit_interrupts_enabled_def]
  >> gvs[finite_mapTheory.FAPPLY_FUPDATE_THM,
         uart_globals_def,finite_mapTheory.FUPDATE_LIST,
         conf_registers_def,word_with_def,AUX_MU_IER_REG_def,the_word_def,has_kvar_vw_def,lookup_kvar_def]
  >> rpt (pairarg_tac >> fs[])
  >> gvs[]
  >- SET_TAC []
  >> rw[]
  >> gvs[SF SFY_ss,finite_mapTheory.FLOOKUP_DEF,registers_def,conf_registers_def,AUX_MU_IER_REG_def]
QED

Definition with_receive_interrupts_enabled_def:
  with_receive_interrupts_enabled ffi aux_base st =
  ffi with registers :=
      (ffi.registers |+ (AUX_MU_IER_REG aux_base,
                           (if st then
                              (ffi.registers ' (AUX_MU_IER_REG aux_base)) || 2w
                            else
                              (ffi.registers ' (AUX_MU_IER_REG aux_base)) && -3w)))
End

Definition receive_interrupts_enabled_def:
  receive_interrupts_enabled ffi aux_base ⇔ ffi.registers ' (AUX_MU_IER_REG aux_base) ' 1
End

Theorem receive_interrupts_enabled_eq[simp]:
  ∀ffi b b' aux_base. (receive_interrupts_enabled (ffi with write_buffer := b') aux_base ⇔ receive_interrupts_enabled ffi aux_base)
Proof
  rw[receive_interrupts_enabled_def]
QED

Theorem receive_interrupts_enabled_thm:
  ∀ffi aux_base.
       receive_interrupts_enabled (with_receive_interrupts_enabled ffi aux_base T) aux_base ∧
        ¬receive_interrupts_enabled (with_receive_interrupts_enabled ffi aux_base F) aux_base ∧
        ∀reg bit st. (reg ≠ AUX_MU_IER_REG aux_base ∨ (bit ≠ 1 ∧ bit < 32)) ⇒
                     ffi.registers ' reg ' bit =
                     (with_receive_interrupts_enabled ffi aux_base st).registers ' reg ' bit
Proof
  rw[with_receive_interrupts_enabled_def,receive_interrupts_enabled_def]
  >- FULL_BBLAST_TAC
  >- FULL_BBLAST_TAC
  >> iff_tac
  >> Cases_on ‘reg = AUX_MU_IER_REG aux_base’
  >> rw[]
  >> gvs[finite_mapTheory.FAPPLY_FUPDATE_THM]
  >> qabbrev_tac ‘w = ffi.registers ' (AUX_MU_IER_REG aux_base)’
  >> qpat_x_assum ‘Abbrev _’ $ kall_tac
  >> rpt (last_x_assum $ mp_tac)
  >> qid_spec_tac ‘bit’
  >> rpt (CONV_TAC (BOUNDED_FORALL_CONV ALL_CONV) >> conj_tac >- FULL_BBLAST_TAC)
  >> CONV_TAC (BOUNDED_FORALL_CONV ALL_CONV)
  >> rw[]
  >> FULL_BBLAST_TAC
QED

Theorem interrupts_comm:
  ∀ffi aux_base rec tra. with_receive_interrupts_enabled (with_transmit_interrupts_enabled ffi aux_base tra) aux_base rec =
                         with_transmit_interrupts_enabled (with_receive_interrupts_enabled ffi aux_base rec) aux_base tra
Proof
  rw[with_receive_interrupts_enabled_def,with_transmit_interrupts_enabled_def]
  >> qmatch_goalsub_abbrev_tac ‘ffi with registers := _ |+ (k,v1) = ffi with registers := _ |+ (k,v2)’
  >> ‘v1 = v2’ suffices_by gvs[]
  >> qunabbrev_tac ‘v1’
  >> qunabbrev_tac ‘v2’
  >> FULL_BBLAST_TAC
QED
        
Definition fun_set_receive_interrupt_contract:
  fun_set_receive_interrupt_contract receive_interrupt ffi_pre_state globals memory base aux_base =
          FunContract [("receive_interrupt",the_word receive_interrupt)]
                      (λs. s.ffi.ffi_state = ffi_pre_state ∧
                           s.globals = globals ∧
                           s.globals ' (strlit "aux_base_vaddr") = ValWord aux_base ∧
                           s.memory = memory ∧
                           uart_globals base aux_base s)
                      (λt. uart_globals base aux_base t ∧
                           t.globals = globals ∧
                           t.memory = memory ∧
                           t.ffi.ffi_state = with_receive_interrupts_enabled ffi_pre_state aux_base (receive_interrupt ≠ 0w))
                      (word_with (λr. r = (0w : word64)))
End

Theorem fun_set_receive_interrupt:
  ∀receive_interrupt ffi_pre_state globals memory base aux_base.
  (fun_set_receive_interrupt_contract receive_interrupt ffi_pre_state globals memory base aux_base)
  refine
  (PanC (code ^fun_set_receive_interrupt))
Proof
  begin_refinement_tac fun_set_receive_interrupt_contract
  >> irule tailcall_refinement_rule
  >> rw[lookup_code_def,eval_def,finite_mapTheory.FLOOKUP_DEF,finite_mapTheory.FUPDATE_LIST,
        shape_of_def,wordLangTheory.word_sh_def,wordLangTheory.word_op_def]
  >- gvs[uart_globals_def,has_kvar_vw_def,lookup_kvar_def,finite_mapTheory.FLOOKUP_DEF]
  >> gvs[uart_globals_def,has_kvar_vw_def,lookup_kvar_def,wordLangTheory.word_op_def,finite_mapTheory.FLOOKUP_DEF,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FAPPLY_FUPDATE_THM]
  >> irule refine_to_prog_hoare
  >> irule refine_transitive
  >> qexists ‘fun_set_bits_contract (AUX_MU_IER_REG aux_base) 2w receive_interrupt s.ffi.ffi_state s.globals s.memory s.base_addr aux_base’
  >> reverse (conj_tac)
  >- gvs[REWRITE_RULE [code_def] fun_set_bits_thm]
  >> gvs[fun_set_bits_contract,fun_contract_def]
  >> irule both_pre_post_refinement_rule
  >> rw[empty_locals_def,with_receive_interrupts_enabled_def]
  >> gvs[finite_mapTheory.FAPPLY_FUPDATE_THM,
         uart_globals_def,finite_mapTheory.FUPDATE_LIST,
         conf_registers_def,word_with_def,AUX_MU_IER_REG_def,the_word_def,has_kvar_vw_def,lookup_kvar_def]
  >> rpt (pairarg_tac >> gvs[])
  >- SET_TAC []
  >> rw[]
  >> gvs[SF SFY_ss,finite_mapTheory.FLOOKUP_DEF,registers_def,conf_registers_def,AUX_MU_IER_REG_def]
QED

Definition device_ready_def:
  device_ready aux_base s ⇔
                   ¬transmit_interrupts_enabled s.ffi.ffi_state aux_base ∧
                   ¬receive_interrupts_enabled s.ffi.ffi_state aux_base ∧
                   FLOOKUP s.globals (strlit "aux_base_vaddr") = SOME (ValWord aux_base) ∧
                   let aux_len            = unbox (s.memory (s.base_addr +  8w));
                       write_buffer_start = unbox (s.memory (s.base_addr + 16w));
                       write_buffer_len   = unbox (s.memory (s.base_addr + 24w)) in
                     FLOOKUP s.globals (strlit "aux_len") = SOME (ValWord aux_len) ∧
                     (∀addr. array aux_base aux_len addr ⇒ addr ∈ s.sh_memaddrs) ∧
                     FLOOKUP s.globals (strlit "write_buffer_vaddr") = SOME (ValWord write_buffer_start) ∧
                     FLOOKUP s.globals (strlit "write_buffer_len") = SOME (ValWord write_buffer_len) ∧
                     (∀addr. array write_buffer_start write_buffer_len addr ⇒ addr ∈ s.sh_memaddrs)
End

Theorem fun_main:
  ∀ffi_pre_state memory base aux_base.
 (FunContract []
                      (λs. uart_globals base aux_base s ∧
                           s.memory = memory ∧
                           s.ffi.ffi_state = ffi_pre_state ∧
                           s.globals = FEMPTY |++ [(strlit "aux_base_vaddr",ValWord 0w);
                                                   (strlit "aux_len",ValWord 0w);
                                                   (strlit "write_buffer_vaddr",ValWord 0w);
                                                   (strlit "write_buffer_len",ValWord 0w)])
                      (λt. uart_globals base aux_base t ∧ device_ready aux_base t)
                      (word_with (λr. r = (0w : word64))))
  refine
  (PanC (code ^fun_main))
Proof
  begin_refinement_tac code_def
  >> apply_seq ‘M = λs. uart_globals base aux_base s ∧
                        s.memory = memory ∧
                        s.ffi.ffi_state = ffi_pre_state ∧
                        s.globals = FEMPTY |++ [(strlit "aux_base_vaddr",ValWord (unbox (s.memory base)));
                                                (strlit "aux_len",ValWord 0w);
                                                (strlit "write_buffer_vaddr",ValWord 0w);
                                                (strlit "write_buffer_len",ValWord 0w)] ∧
                        s.ffi.oracle = uart_ffi memory base aux_base’
  >- (apply_assign >> gvs[mem_load_def,uart_globals_def,shape_of_def,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FAPPLY_FUPDATE_THM,
                          finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FUPDATE_COMMUTES,has_kvar_vw_def,lookup_kvar_def]
                   >> Cases_on ‘s.memory s.base_addr’
                   >> gvs[unbox_def])
  >> apply_seq ‘M = λs. uart_globals base aux_base s ∧
                        s.memory = memory ∧
                        s.ffi.ffi_state = ffi_pre_state ∧
                        s.globals = FEMPTY |++ [(strlit "aux_base_vaddr",ValWord (unbox (s.memory base)));
                                                (strlit "aux_len",ValWord (unbox (s.memory (base + 8w))));
                                                (strlit "write_buffer_vaddr",ValWord 0w);
                                                (strlit "write_buffer_len",ValWord 0w)] ∧
                        s.ffi.oracle = uart_ffi memory base aux_base’
  >- (apply_assign >> gvs[mem_load_def,uart_globals_def,shape_of_def,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FAPPLY_FUPDATE_THM,
                          finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FUPDATE_COMMUTES,has_kvar_vw_def,lookup_kvar_def]
                   >> Cases_on ‘s.memory s.base_addr’
                   >> Cases_on ‘s.memory (s.base_addr + 8w)’
                   >> gvs[unbox_def,byteTheory.bytes_in_word_def,finite_mapTheory.FUPDATE_COMMUTES])
  >> apply_seq ‘M = λs. uart_globals base aux_base s ∧
                        s.memory = memory ∧
                        s.ffi.ffi_state = ffi_pre_state ∧
                        s.globals = FEMPTY |++ [(strlit "aux_base_vaddr",ValWord (unbox (s.memory base)));
                                                (strlit "aux_len",ValWord (unbox (s.memory (base + 8w))));
                                                (strlit "write_buffer_vaddr",ValWord (unbox (s.memory (base + 16w))));
                                                (strlit "write_buffer_len",ValWord 0w)] ∧
                        s.ffi.oracle = uart_ffi memory base aux_base’
  >- (apply_assign >> gvs[mem_load_def,uart_globals_def,shape_of_def,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FAPPLY_FUPDATE_THM,
                          finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FUPDATE_COMMUTES,has_kvar_vw_def,lookup_kvar_def]
                   >> Cases_on ‘s.memory s.base_addr’
                   >> Cases_on ‘s.memory (s.base_addr + 8w)’
                   >> Cases_on ‘s.memory (s.base_addr + 16w)’
                   >> gvs[unbox_def,byteTheory.bytes_in_word_def,finite_mapTheory.FUPDATE_COMMUTES])
  >> apply_seq ‘M = λs. uart_globals base aux_base s ∧
                        s.memory = memory ∧
                        s.ffi.ffi_state = ffi_pre_state ∧
                        s.globals = FEMPTY |++ [(strlit "aux_base_vaddr",ValWord (unbox (s.memory base)));
                                                (strlit "aux_len",ValWord (unbox (s.memory (base + 8w))));
                                                (strlit "write_buffer_vaddr",ValWord (unbox (s.memory (base + 16w))));
                                                (strlit "write_buffer_len",ValWord (unbox (s.memory (base + 24w))))] ∧
                        s.ffi.oracle = uart_ffi memory base aux_base’
  >- (apply_assign >> gvs[mem_load_def,uart_globals_def,shape_of_def,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FAPPLY_FUPDATE_THM,
                          finite_mapTheory.FLOOKUP_UPDATE,finite_mapTheory.FUPDATE_COMMUTES,has_kvar_vw_def,lookup_kvar_def]
                   >> Cases_on ‘s.memory s.base_addr’
                   >> Cases_on ‘s.memory (s.base_addr + 8w)’
                   >> Cases_on ‘s.memory (s.base_addr + 16w)’
                   >> Cases_on ‘s.memory (s.base_addr + 24w)’
                   >> gvs[unbox_def,byteTheory.bytes_in_word_def,finite_mapTheory.FUPDATE_COMMUTES])
  >> apply_seq ‘M = λs. P (s with ffi := s.ffi with ffi_state := ffi_pre_state) ∧ s.ffi.ffi_state = with_transmit_interrupts_enabled ffi_pre_state aux_base F’
  >- (irule standalonecall_refinement_rule
      >> unabbrev_all_tac
      >> rw[finite_mapTheory.FLOOKUP_UPDATE]
      >> gvs[eval_def,lookup_code_def,uart_globals_def,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FLOOKUP_UPDATE]
      >> irule refine_to_prog_hoare
      >> irule refine_transitive
      >> qexists ‘fun_set_transmit_interrupt_contract 0w s.ffi.ffi_state s.globals s.memory s.base_addr (unbox (s.memory s.base_addr))’
      >> gvs[REWRITE_RULE [code_def] fun_set_transmit_interrupt]
      >> gvs[fun_set_transmit_interrupt_contract,fun_contract_def]
      >> irule both_pre_post_refinement_rule
      >> rw[]
      >- (pairarg_tac >> gvs[uart_globals_def,finite_mapTheory.FUPDATE_LIST,transmit_interrupts_enabled_thm,has_kvar_vw_def,lookup_kvar_def])
      >> gvs[uart_globals_def,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FAPPLY_FUPDATE_THM,the_word_def,has_kvar_vw_def,lookup_kvar_def])
  >> apply_seq ‘M = λs. P (s with ffi := s.ffi with ffi_state := with_transmit_interrupts_enabled ffi_pre_state aux_base F) ∧
                        s.ffi.ffi_state = with_receive_interrupts_enabled (with_transmit_interrupts_enabled ffi_pre_state aux_base F) aux_base F’
  >- (irule standalonecall_refinement_rule
      >> unabbrev_all_tac
      >> rw[finite_mapTheory.FLOOKUP_UPDATE]
      >> gvs[eval_def,lookup_code_def,uart_globals_def,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FLOOKUP_UPDATE]
      >> irule refine_to_prog_hoare
      >> irule refine_transitive
      >> qexists ‘fun_set_receive_interrupt_contract 0w s.ffi.ffi_state s.globals s.memory s.base_addr (unbox (s.memory s.base_addr))’
      >> gvs[REWRITE_RULE [code_def] fun_set_receive_interrupt]
      >> gvs[fun_set_receive_interrupt_contract,fun_contract_def]
      >> irule both_pre_post_refinement_rule
      >> rw[]
      >- (pairarg_tac >> gvs[uart_globals_def,finite_mapTheory.FUPDATE_LIST,receive_interrupts_enabled_thm,has_kvar_vw_def,lookup_kvar_def])
      >> gvs[IN_DEF,uart_globals_def,finite_mapTheory.FUPDATE_LIST,with_transmit_interrupts_enabled_def,finite_mapTheory.FAPPLY_FUPDATE_THM,
             the_word_def,has_kvar_vw_def,lookup_kvar_def,registers_def,conf_registers_def]
      >> SET_TAC[])
  >> apply_return
  >- (gvs[uart_globals_def,with_receive_interrupts_enabled_def,with_transmit_interrupts_enabled_def,has_kvar_vw_def,lookup_kvar_def,IN_DEF,registers_def,conf_registers_def] >> SET_TAC[])
  >> gvs[uart_globals_def,device_ready_def,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FLOOKUP_UPDATE,IN_DEF]
  >> conj_tac
  >- gvs[interrupts_comm,transmit_interrupts_enabled_thm]
  >> gvs[receive_interrupts_enabled_thm]
QED

Definition w2w32_def[simp]:
  w2w32 = w2w : ('a word -> word32)
End

Definition fun_putc_contract:
  fun_putc_contract pre pre_state base char memory aux_base = 
  (FunContract [("char",the_word char)]
                (λs. uart_globals base aux_base s ∧ device_ready aux_base s ∧ pre (s.ffi.io_events) ∧ s.memory = memory ∧ s.ffi.ffi_state = pre_state)
                (λt. uart_globals base aux_base t ∧ device_ready aux_base t ∧ t.memory = memory ∧ t.ffi.ffi_state = pre_state ∧
                     ∃head mid. t.ffi.io_events = (head ++ mid ++ [IO_event (SharedMem MappedWrite) [4w] (ZIP ((word_to_bytes (w2w32 char) F) ++ (word_to_bytes (AUX_MU_IO_REG aux_base) F),
                                                                                                               (word_to_bytes (w2w32 char) F) ++ (word_to_bytes (AUX_MU_IO_REG aux_base) F)))]) ∧
                                EVERY (λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b) mid ∧
                                mid ≠ [] ∧
                                pre head)
                (the_word (0w : word64)))
End

Theorem fun_putc:
  ∀pre pre_state base char memory aux_base.
  (fun_putc_contract pre pre_state base char memory aux_base) refine (PanC (code ^fun_putc))
Proof
  begin_refinement_tac fun_putc_contract
  >> apply_dec
  >> apply_seq ‘M = λs. FDOM s.locals (strlit "char") ∧
                        s.locals ' (strlit "char") = ValWord char ∧
                        uart_globals base aux_base s ∧
                        device_ready aux_base s ∧
                        s.memory = memory ∧
                        s.ffi.ffi_state = pre_state ∧
                        s.ffi.ffi_state.registers ' (AUX_MU_LSR_REG aux_base) ' 5 ∧
                        (∃w. FLOOKUP s.locals (strlit "aux_mu_lsr_reg") = SOME (ValWord w)) ∧
                        ∃head mid. s.ffi.io_events = head ++ mid ∧
                                   EVERY (λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b) mid ∧
                                   mid ≠ [] ∧
                                   pre head’
  >- (unabbrev_all_tac
      >> qmatch_goalsub_abbrev_tac ‘(HoareC P Q) refine (PanC (While e subprog))’
      >> qabbrev_tac ‘i = λs. FDOM s.locals (strlit "char") ∧
                              s.locals ' (strlit "char") = ValWord (w2w char) ∧
                              uart_globals base aux_base s ∧ device_ready aux_base s ∧
                              s.memory = memory ∧
                              s.ffi.ffi_state = pre_state ∧
                              (∃w. FLOOKUP s.locals (strlit "aux_mu_lsr_reg") = SOME (ValWord w) ∧
                                   (¬(w ' 5) ∨ (s.ffi.ffi_state.registers ' (AUX_MU_LSR_REG aux_base) ' 5))) ∧
                              ∃head mid. s.ffi.io_events = head ++ mid ∧
                                         EVERY (λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b) mid ∧
                                         pre head ∧
                                         (evaluates_to_false e s ⇒ mid ≠ [])’
      >> irule refine_transitive
      >> qexists ‘WhileC e i (PanC subprog)’
      >> reverse (rw[])
      >- gvs[while_refinement_rule_pan]
      >> irule refine_transitive
      >> qexists ‘WhileC e i (HoareC (while_body_pre i e) (while_body_post i (λs. F) (λs. F) (λs. F) (λs. F)))’
      >> rw[]
      >- (irule (SIMP_RULE (srw_ss()) [] while_refinement_rule)
          >> unabbrev_all_tac
          >> rw[uart_globals_def,device_ready_def]
          >> gvs[IN_DEF,evaluates_to_word_def,eval_def,asmTheory.word_cmp_def,wordLangTheory.word_op_def,wordLangTheory.word_sh_def,var_eq_def,
                 evaluates_to_false_def,panPropsTheory.eval_upd_clock_eq,has_kvar_vw_def,lookup_kvar_def]
          >> gvs[finite_mapTheory.DOMSUB_FAPPLY_THM]
          >- (qexistsl [‘head’, ‘mid’] >> gvs[])
          >- (qexistsl [‘head’, ‘mid’] >> gvs[])
          >- ASM_SET_TAC[]
          >- gvs[finite_mapTheory.FLOOKUP_DEF,IN_DEF]
          >- (qexistsl [‘s.ffi.io_events’, ‘[]’] >> gvs[finite_mapTheory.FLOOKUP_DEF,IN_DEF])
          >- (Cases_on ‘32w && w = 0w’ >> gvs[] >> FULL_BBLAST_TAC)
          >> qexistsl [‘head’, ‘mid’]
          >> gvs[finite_mapTheory.FLOOKUP_DEF,IN_DEF])
      >> irule refine_monotonic_while
      >> gvs[while_body_pre_def,while_body_post_def]
      >> unabbrev_all_tac
      >> apply_shmemload uart_ffi_def
      >> gvs[uart_globals_def,device_ready_def,has_kvar_vw_def,lookup_kvar_def,finite_mapTheory.FLOOKUP_DEF,IN_DEF]
      >- (rpt disj1_tac >> qexists ‘unbox (s.memory s.base_addr) + 84w’ >> gvs[registers_def,status_registers_def,AUX_MU_LSR_REG_def])
      >- (rpt disj1_tac >> qexists ‘unbox (s.memory s.base_addr) + 84w’ >> gvs[registers_def,status_registers_def,AUX_MU_LSR_REG_def])
      >> gvs[uart_ffi_def,registers_def,status_registers_def,AUX_MU_LSR_REG_def]
      >> rw[]
      >- BBLAST_TAC
      >> qexistsl [‘head’, ‘mid ++ [IO_event (SharedMem MappedRead) [4w]
             (ZIP
                (word_to_bytes (unbox (s.memory s.base_addr) + 84w) F,
                 word_to_bytes
                 (w2w (s.ffi.ffi_state.registers ' (unbox (s.memory s.base_addr) + 84w)) : word64) F))]’]
      >> gvs[])
  >> apply_seq ‘M = λs. FDOM s.locals (strlit "char") ∧
                        s.locals ' (strlit "char") = ValWord char ∧
                        s.memory = memory ∧
                        s.ffi.ffi_state = pre_state ∧
                        uart_globals base aux_base s ∧
                        device_ready aux_base s ∧
                        s.ffi.ffi_state.registers ' (AUX_MU_LSR_REG aux_base) ' 5 ∧
                        ∃head mid. s.ffi.io_events = (head ++ mid ++ [IO_event (SharedMem MappedWrite) [4w] (ZIP ((word_to_bytes (w2w32 char) F) ++ (word_to_bytes (AUX_MU_IO_REG aux_base) F),
                                                                                                                  (word_to_bytes (w2w32 char) F) ++ (word_to_bytes (AUX_MU_IO_REG aux_base) F)))]) ∧
                                   EVERY (λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b) mid ∧
                                   mid ≠ [] ∧
                                   pre head’
  >- (apply_shmemstore uart_ffi_def
      >> gvs[uart_globals_def,has_kvar_vw_def,lookup_kvar_def,finite_mapTheory.FLOOKUP_DEF,wordLangTheory.word_op_def,device_ready_def,
             registers_def,conf_registers_def,AUX_MU_IER_REG_def,uart_ffi_def,AUX_MU_IO_REG_def,IN_DEF]
      >> qexistsl [‘head’, ‘mid’]
      >> gvs[])
  >> apply_return
  >> rpt (HINT_EXISTS_TAC)
  >> gvs[device_ready_def,uart_globals_locals_eq]
QED

Definition fun_puts_contract:
  fun_puts_contract pre_state pre_events memory base aux_base buffer = 
  (FunContract [("buffer",the_word buffer)]
               (λs. uart_globals base aux_base s ∧ device_ready aux_base s ∧
                    zts_at buffer s.ffi.ffi_state.write_buffer (array (unbox (s.memory (s.base_addr + 16w))) (unbox (s.memory (s.base_addr + 24w)))) s.be ∧ s.memory = memory ∧
                    s.ffi.ffi_state = pre_state ∧ s.ffi.io_events = pre_events)
               (λt. uart_globals base aux_base t ∧ device_ready aux_base t ∧
                    zts_at buffer t.ffi.ffi_state.write_buffer (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w)))) t.be ∧ t.memory = memory ∧
                    t.ffi.ffi_state = pre_state ∧
                    pre_events ≼ t.ffi.io_events ∧
                    let rest = DROP (LENGTH pre_events) t.ffi.io_events in
                        FILTER (λe. ∃w. e = IO_event (SharedMem MappedWrite) [4w] w) rest =
                            MAP (λc. IO_event (SharedMem MappedWrite) [4w] (ZIP ((word_to_bytes (w2w c : word32) F) ++ word_to_bytes (AUX_MU_IO_REG aux_base) F,
                                                                                 (word_to_bytes (w2w c : word32) F) ++ word_to_bytes (AUX_MU_IO_REG aux_base) F)))
                                (FRONT (get_zts buffer t.ffi.ffi_state.write_buffer (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w)))) t.be)) ∧
                        EVERY (λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b ∨
                                       e = IO_event (SharedMem MappedRead) [1w] b) (FILTER (λe. ∀w. e ≠ IO_event (SharedMem MappedWrite) [4w] w) rest))
                (word_with (λr. r = (0w : word64))))
End

Theorem fun_puts:
  (fun_puts_contract pre_state pre_events memory base aux_base buffer) refine (PanC (code ^fun_puts))
Proof
  begin_refinement_tac fun_puts_contract
  >> apply_dec
  >> apply_seq ‘M = λt. uart_globals base aux_base t ∧
                        device_ready aux_base t ∧
                        t.ffi.ffi_state = pre_state ∧
                        zts_at buffer t.ffi.ffi_state.write_buffer (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w)))) t.be ∧
                        t.memory = memory ∧ t.ffi.oracle = uart_ffi memory base aux_base ∧
                        strlit "buffer" ∈ FDOM t.locals ∧ t.locals ' (strlit "buffer") = ValWord buffer ∧
                        FLOOKUP t.locals (strlit "char") = SOME (ValWord (w2w (get_byte buffer (t.ffi.ffi_state.write_buffer (byte_align buffer)) F))) ∧
                        (∃b. t.ffi.io_events = SNOC (IO_event (SharedMem MappedRead) [1w] b) pre_events) ∧
                        EVERY (λe. ∃b. e = IO_event (SharedMem MappedRead) [1w] b) (DROP (LENGTH pre_events) t.ffi.io_events)’
  >- (apply_shmemload uart_ffi_def
      >- ASM_SET_TAC[]
      >- (dxrule_all_then assume_tac zts_at_start_addrset >> gvs[uart_globals_def,IN_DEF])
      >> gvs[uart_globals_def,empty_locals_def,uart_ffi_def,device_ready_def]
      >> dxrule_all_then assume_tac zts_at_start_addrset
      >> gvs[has_kvar_vw_def,lookup_kvar_def,rich_listTheory.DROP_SNOC])
  >> apply_seq ‘M = λs. Q (SOME (Return (ValWord 0w)),s with locals := FEMPTY)’
  >- (qmatch_goalsub_abbrev_tac ‘(HoareC P Q) refine (PanC (While e subprog))’
      >> qabbrev_tac ‘i = (λt. uart_globals base aux_base t ∧ device_ready aux_base t ∧
                               zts_at buffer t.ffi.ffi_state.write_buffer (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w)))) t.be ∧
                               t.memory = memory ∧ t.ffi.oracle = uart_ffi memory base aux_base ∧
                               strlit "buffer" ∈ FDOM t.locals ∧ (∃w. t.locals ' (strlit "buffer") = ValWord w) ∧
                               strlit "char" ∈ FDOM t.locals ∧ (∃w. t.locals ' (strlit "char") = ValWord w) ∧
                               pre_events ≼ t.ffi.io_events ∧
                               t.ffi.ffi_state = pre_state ∧
                               let mid = DROP (LENGTH pre_events) t.ffi.io_events; cur = unboxv (t.locals ' (strlit "buffer")) in
                                 (cur ≠ buffer ⇒ mid ≠ []) ∧
                                 array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w))) (byte_align cur) ∧   
                                 zts_at cur t.ffi.ffi_state.write_buffer (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w)))) t.be ∧
                                 (evaluates_to_true e t ⇒ ∃len. len >+ 0w ∧
                                                                zts cur len t.ffi.ffi_state.write_buffer
                                                                    (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w)))) t.be) ∧
                                 FLOOKUP t.locals (strlit "char") = SOME (ValWord (w2w (get_byte cur (t.ffi.ffi_state.write_buffer (byte_align cur)) F))) ∧
                                 (FILTER (λe. ∃w. e = IO_event (SharedMem MappedWrite) [4w] w) mid) ++
                                     (MAP (λc. IO_event (SharedMem MappedWrite) [4w] (ZIP ((word_to_bytes (w2w c : word32) F) ++ word_to_bytes (AUX_MU_IO_REG aux_base) F,
                                                                                           (word_to_bytes (w2w c : word32) F) ++ word_to_bytes (AUX_MU_IO_REG aux_base) F)))
                                          (FRONT (get_zts cur t.ffi.ffi_state.write_buffer
                                                          (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w)))) t.be))) =
                                      MAP (λc. IO_event (SharedMem MappedWrite) [4w] (ZIP ((word_to_bytes (w2w c : word32) F) ++ word_to_bytes (AUX_MU_IO_REG aux_base) F,
                                                                                           (word_to_bytes (w2w c : word32) F) ++ word_to_bytes (AUX_MU_IO_REG aux_base) F)))
                                          (FRONT (get_zts buffer t.ffi.ffi_state.write_buffer
                                                          (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w)))) t.be)) ∧
                                 EVERY (λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b ∨
                                                e = IO_event (SharedMem MappedRead) [1w] b) (FILTER (λe. ∀w. e ≠ IO_event (SharedMem MappedWrite) [4w] w) mid))’
      >> irule refine_transitive
      >> qexists ‘WhileC e i (PanC subprog)’
      >> reverse (rw[])
      >- gvs[while_refinement_rule_pan]
      >> irule refine_transitive
      >> qexists ‘WhileC e i (WhileBC e i (λs. F) (λs. F) (λs. F) (λs. F))’
      >> conj_tac
      >- (irule while_refinement_rule
          >> unabbrev_all_tac
          >> rw[]
          >> gvs[finite_mapTheory.FLOOKUP_DEF,device_ready_def]
          >- gvs[uart_globals_def,has_kvar_vw_def,lookup_kvar_def]
          >- (first_x_assum $ irule >> gvs[evaluates_to_true_def,panPropsTheory.eval_upd_clock_eq])
          >- (gvs[zts_at_def,zts_def] >> first_x_assum $ irule >> irule start_in_wf_array >> gvs[] >> FULL_BBLAST_TAC)
          >- (gvs[evaluates_to_true_def,eval_def,asmTheory.word_cmp_def,AllCaseEqs()]
              >> irule (cj 2 zts_ne_then)
              >> gvs[uart_globals_def,finite_mapTheory.FLOOKUP_DEF]
              >> first_x_assum $ mp_tac
              >> BBLAST_TAC)
          >- (gvs[listTheory.FILTER_EQ_NIL,listTheory.SNOC_APPEND]
              >> irule listTheory.EVERY_MONOTONIC
              >> HINT_EXISTS_TAC
              >> rw[])
          >- (irule listTheory.EVERY_MONOTONIC
              >> qexists ‘λe. ∃b. e = IO_event (SharedMem MappedRead) [1w] b’
              >> rw[rich_listTheory.DROP_SNOC])
          >- gvs[evaluates_to_word_def,eval_def,asmTheory.word_cmp_def,finite_mapTheory.FLOOKUP_DEF]
          >- gvs[uart_globals_def,has_kvar_vw_def,lookup_kvar_def]
          >- (qpat_x_assum ‘_ = MAP _ _’ $ assume_tac o GSYM
              >> gvs[]
              >> irule rich_listTheory.FRONT_EQ_NIL
              >> rw[Ntimes get_zts_def 2]
              >> gvs[evaluates_to_false_def,eval_def,asmTheory.word_cmp_def,AllCaseEqs(),uart_globals_def,finite_mapTheory.FLOOKUP_DEF]
              >> FULL_BBLAST_TAC
              >> irule listTheory.EVERY_MONOTONIC
              >> HINT_EXISTS_TAC
              >> rw[])
           >> irule listTheory.EVERY_MONOTONIC
           >> HINT_EXISTS_TAC
           >> rw[])
      >> irule refine_monotonic_while
      >> unabbrev_all_tac
      >> gvs[while_body_pre_def,while_body_post_def]
      >> apply_seq ‘M = λs. uart_globals base aux_base s ∧
                            device_ready aux_base s ∧
                            zts_at buffer s.ffi.ffi_state.write_buffer (array (unbox (s.memory (s.base_addr + 16w))) (unbox (s.memory (s.base_addr + 24w)))) s.be ∧
                            s.memory = memory ∧
                            s.ffi.ffi_state = pre_state ∧
                            strlit "buffer" ∈ FDOM s.locals ∧
                            (∃w. FLOOKUP s.locals (strlit "buffer") = SOME (ValWord w)) ∧
                            strlit "char" ∈ FDOM s.locals ∧
                            pre_events ≼ s.ffi.io_events ∧
                            evaluates_to_true (Cmp NotEqual (Var Local (strlit "char")) (Const 0w)) s ∧
                            let mid  = FRONT (DROP (LENGTH pre_events) s.ffi.io_events);
                                cur  = unboxv (s.locals ' (strlit "buffer"));
                                char = unboxv (s.locals ' (strlit "char")) in
                                    DROP (LENGTH pre_events) s.ffi.io_events  ≠ [] ∧
                                    mid ≠ [] ∧
                                    LAST s.ffi.io_events = IO_event (SharedMem MappedWrite) [4w] (ZIP (word_to_bytes (w2w32 char) F ++
                                                                                                       word_to_bytes (AUX_MU_IO_REG aux_base) F,
                                                                                                       word_to_bytes (w2w32 char) F ++
                                                                                                       word_to_bytes (AUX_MU_IO_REG aux_base) F)) ∧
                                    zts_at cur s.ffi.ffi_state.write_buffer
                                           (array (unbox (s.memory (s.base_addr + 16w))) (unbox (s.memory (s.base_addr + 24w)))) s.be ∧
                                    (∃len. len >+ 0w ∧ zts cur len s.ffi.ffi_state.write_buffer
                                                           (array (unbox (s.memory (s.base_addr + 16w))) (unbox (s.memory (s.base_addr + 24w)))) s.be) ∧
                                    FLOOKUP s.locals (strlit "char") = SOME (ValWord (w2w (get_byte cur (s.ffi.ffi_state.write_buffer (byte_align cur)) F))) ∧
                                    FILTER (λe. ∃w. e = IO_event (SharedMem MappedWrite) [4w] w) mid ++
                                        MAP (λc.  IO_event (SharedMem MappedWrite) [4w] (ZIP (word_to_bytes (w2w32 c) F ++
                                                                                              word_to_bytes (AUX_MU_IO_REG aux_base) F,
                                                                                              word_to_bytes (w2w32 c) F ++
                                                                                              word_to_bytes (AUX_MU_IO_REG aux_base) F)))
                                            (FRONT (get_zts cur s.ffi.ffi_state.write_buffer
                                                            (array (unbox (s.memory (s.base_addr + 16w))) (unbox (s.memory (s.base_addr + 24w)))) s.be)) =
                                        MAP (λc.  IO_event (SharedMem MappedWrite) [4w] (ZIP (word_to_bytes (w2w32 c) F ++
                                                                                              word_to_bytes (AUX_MU_IO_REG aux_base) F,
                                                                                              word_to_bytes (w2w32 c) F ++
                                                                                              word_to_bytes (AUX_MU_IO_REG aux_base) F)))
                                            (FRONT (get_zts buffer s.ffi.ffi_state.write_buffer
                                                            (array (unbox (s.memory (s.base_addr + 16w))) (unbox (s.memory (s.base_addr + 24w)))) s.be)) ∧
                                    EVERY (λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b ∨
                                                   e = IO_event (SharedMem MappedRead) [1w] b) (FILTER (λe. ∀w. e ≠ IO_event (SharedMem MappedWrite) [4w] w) mid)’
      >- (unabbrev_all_tac
          >> irule standalonecall_refinement_rule
          >> rw[]
          >- gvs[eval_def,finite_mapTheory.FLOOKUP_DEF]
          >> gvs[lookup_code_def,uart_globals_def,finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FLOOKUP_UPDATE,
                 code_def,eval_def,finite_mapTheory.FLOOKUP_DEF,shape_of_def,finite_mapTheory.FAPPLY_FUPDATE_THM]
          >> irule refine_to_prog_hoare
          >> irule refine_transitive
          >> qexists ‘fun_putc_contract (λev. pre_events ≼ ev ∧ FILTER (λe. ∃w. e = IO_event (SharedMem MappedWrite) [4w] w)
                   (DROP (LENGTH pre_events) ev) ++
                 MAP
                   (λc.
                        IO_event (SharedMem MappedWrite) [4w]
                          (ZIP
                             (word_to_bytes (w2w32 c) F ++
                              word_to_bytes (AUX_MU_IO_REG aux_base) F,
                              word_to_bytes (w2w32 c) F ++
                              word_to_bytes (AUX_MU_IO_REG aux_base) F)))
                   (FRONT
                      (get_zts w t.ffi.ffi_state.write_buffer (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w)))) t.be)) =
                 MAP
                   (λc.
                        IO_event (SharedMem MappedWrite) [4w]
                          (ZIP
                             (word_to_bytes (w2w32 c) F ++
                              word_to_bytes (AUX_MU_IO_REG aux_base) F,
                              word_to_bytes (w2w32 c) F ++
                              word_to_bytes (AUX_MU_IO_REG aux_base) F)))
                   (FRONT
                      (get_zts buffer t.ffi.ffi_state.write_buffer (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w)))) t.be)) ∧
                                              EVERY (λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b ∨
                                                             e = IO_event (SharedMem MappedRead) [1w] b)
                   (FILTER
                      (λe. ∀w. e ≠ IO_event (SharedMem MappedWrite) [4w] w)
                      (DROP (LENGTH pre_events) ev))) t.ffi.ffi_state t.base_addr (w2w (get_byte w (t.ffi.ffi_state.write_buffer (byte_align w)) F)) t.memory aux_base’
          >> gvs[REWRITE_RULE [code_def] fun_putc]
          >> gvs[fun_putc_contract,fun_contract_def]
          >> irule both_pre_post_refinement_rule
          >> rw[]
          >- (pairarg_tac
              >> gvs[uart_globals_def,device_ready_def,has_kvar_vw_def,lookup_kvar_def]
              >> rw[]
              >- (irule (iffRL rich_listTheory.IS_PREFIX_APPEND)
                  >> dxrule_then assume_tac (iffLR rich_listTheory.IS_PREFIX_APPEND)
                  >> gvs[])
              >- gvs[evaluates_to_true_def,eval_def]
              >> qexists ‘len’
              >> rw[]
              >- (dxrule_then assume_tac (iffLR rich_listTheory.IS_PREFIX_APPEND)
                  >> gvs[]
                  >> pure_rewrite_tac[GSYM rich_listTheory.APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND]
                  >> qmatch_goalsub_abbrev_tac ‘FRONT (l ++ (mid ++ the_last)) ≠ []’
                  >> ‘mid ++ the_last ≠ []’ by gvs[]
                  >> ‘l ++ FRONT (mid ++ the_last) ≠ []’ suffices_by metis_tac[rich_listTheory.FRONT_APPEND_NOT_NIL]
                  >> spose_not_then assume_tac
                  >> gvs[listTheory.APPEND_eq_NIL,listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
                  >> ‘LENGTH the_last = 1’ by (unabbrev_all_tac >> gvs[])
                  >> ‘LENGTH (mid ++ the_last) > 1’ by gvs[rich_listTheory.LENGTH_APPEND]
                  >> gvs[rich_listTheory.FRONT_NON_NIL])
              >- (dxrule_then assume_tac (iffLR rich_listTheory.IS_PREFIX_APPEND)
                  >> gvs[]
                  >> pure_rewrite_tac[GSYM rich_listTheory.APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND]
                  >> qmatch_goalsub_abbrev_tac ‘FRONT (l ++ (mid ++ the_last)) ≠ []’
                  >> ‘mid ++ the_last ≠ []’ by gvs[]
                  >> ‘l ++ FRONT (mid ++ the_last) ≠ []’ suffices_by metis_tac[rich_listTheory.FRONT_APPEND_NOT_NIL]
                  >> spose_not_then assume_tac
                  >> gvs[listTheory.APPEND_eq_NIL,listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
                  >> ‘LENGTH the_last = 1’ by (unabbrev_all_tac >> gvs[])
                  >> ‘LENGTH (mid ++ the_last) > 1’ by gvs[rich_listTheory.LENGTH_APPEND]
                  >> gvs[rich_listTheory.FRONT_NON_NIL])
              >- (gvs[uart_globals_def]
                  >> qpat_x_assum ‘_ = MAP _ _’ $ (assume_tac o GSYM)
                  >> dxrule_then assume_tac (iffLR rich_listTheory.IS_PREFIX_APPEND)
                  >> gvs[rich_listTheory.DROP_LENGTH_APPEND]
                  >> qmatch_goalsub_abbrev_tac ‘FILTER P (FRONT (DROP _ (_ ++ [x]))) = FILTER _ _’
                  >> ‘FILTER P (FRONT (DROP (LENGTH pre_events) (pre_events ++ (SNOC x (l ++ mid))))) = FILTER P l’ suffices_by gvs[]
                  >> pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND,listTheory.FRONT_SNOC]
                  >> gvs[listTheory.FILTER_APPEND_DISTRIB,listTheory.FILTER_EQ_NIL]
                  >> irule listTheory.EVERY_MONOTONIC
                  >> qexists ‘(λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b)’
                  >> unabbrev_all_tac
                  >> rw[])
              >> dxrule_then assume_tac (iffLR rich_listTheory.IS_PREFIX_APPEND)
              >> gvs[]
              >> qmatch_goalsub_abbrev_tac ‘EVERY P1 (FILTER P2 (FRONT (DROP _ (_ ++ [x]))))’
              >> qsuff_tac ‘EVERY P1 (FILTER P2 (FRONT (DROP (LENGTH pre_events) (pre_events ++ (SNOC x (l ++ mid))))))’
              >- gvs[listTheory.SNOC_APPEND]
              >> gvs[rich_listTheory.DROP_LENGTH_APPEND,rich_listTheory.FILTER_APPEND]
              >> conj_tac
              >- (irule listTheory.EVERY_MONOTONIC
                  >> HINT_EXISTS_TAC
                  >> unabbrev_all_tac
                  >> gvs[]
                  >> rw[])
              >> gvs[listTheory.EVERY_FILTER]
              >> irule listTheory.EVERY_MONOTONIC
              >> qexists ‘P1’
              >> unabbrev_all_tac
              >> rw[]
              >> irule listTheory.EVERY_MONOTONIC
              >> qexists ‘λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b’
              >> rw[])
          >> gvs[the_word_def,uart_globals_def,has_kvar_vw_def,lookup_kvar_def,finite_mapTheory.FUPDATE_LIST,device_ready_def]
          >> irule listTheory.EVERY_MONOTONIC
          >> HINT_EXISTS_TAC
          >> gvs[]
          >> rw[])
      >> apply_seq ‘M = λs. P (s with locals := s.locals |+ (strlit "buffer", ValWord (unboxv (s.locals ' (strlit "buffer")) - 1w))) ∧
                            ∃w. FLOOKUP s.locals (strlit "buffer") = SOME (ValWord w)’
      >- (apply_assign >> qexists ‘len’ >> gvs[uart_globals_locals_eq,device_ready_def,evaluates_to_true_def,eval_def,asmTheory.word_cmp_def,finite_mapTheory.FLOOKUP_UPDATE])
      >> apply_shmemload uart_ffi_def
      >- (drule_all_then assume_tac zts_start_suc
          >> gvs[]
          >> drule_all_then assume_tac zts_therefore_zts_at
          >> drule_all_then assume_tac zts_at_start_addrset
          >> gvs[uart_globals_def,IN_DEF])
      >> gvs[uart_globals_def,uart_ffi_def]
      >> drule_all_then assume_tac zts_start_suc
      >> gvs[]
      >> drule_all_then assume_tac zts_therefore_zts_at
      >> drule_all_then assume_tac zts_at_start_addrset
      >> rw[]
      >> gvs[has_kvar_vw_def,lookup_kvar_def]
      >- gvs[device_ready_def]
      >- gvs[listTheory.isPREFIX_SNOC_EQ,GSYM listTheory.SNOC_APPEND]
      >- (irule (cj 2 zts_ne_then) >> rev_drule_all_then assume_tac zts_start_suc >> rw[zts_at_def]
          >> gvs[evaluates_to_true_def,eval_def,asmTheory.word_cmp_def,var_eq_def,finite_mapTheory.FLOOKUP_UPDATE,AllCaseEqs(),uart_globals_def]
          >- (qpat_x_assum ‘w2w _ ≠ 0w’ $ mp_tac >> BBLAST_TAC)
          >> qexists ‘len + -1w’ >> gvs[])
      >- (qpat_x_assum ‘_ = MAP _ _’ $ assume_tac o GSYM
          >> gvs[]
          >> first_x_assum $ kall_tac
          >> dxrule_then assume_tac (iffLR rich_listTheory.IS_PREFIX_APPEND)
          >> gvs[rich_listTheory.DROP_SNOC,rich_listTheory.DROP_LENGTH_APPEND,rich_listTheory.FILTER_SNOC]
          >> CONV_TAC (RHS_CONV (REWRITE_CONV [Once get_zts_def]))
          >> gvs[evaluates_to_true_def,eval_def,var_eq_def,finite_mapTheory.FAPPLY_FUPDATE_THM,asmTheory.word_cmp_def,AllCaseEqs(),finite_mapTheory.FLOOKUP_DEF]
          >> ‘get_byte (w + -1w) (s.ffi.ffi_state.write_buffer (byte_align (w + -1w))) F ≠ 0w’ by (rpt (qpat_x_assum ‘w2w _ ≠ 0w’ $ mp_tac) >> BBLAST_TAC)
          >> gvs[uart_globals_def]
          >> Cases_on ‘get_zts w s.ffi.ffi_state.write_buffer (array (unbox (s.memory (s.base_addr + 16w))) (unbox (s.memory (s.base_addr + 24w)))) F’
          >- (‘F’ suffices_by gvs[] >> pop_assum $ mp_tac >> gvs[] >> irule get_zts_not_null >> gvs[zts_at_def] >> qexists ‘len - 1w’ >> gvs[]
              >> qpat_x_assum ‘zts (w + -1w) len _ _ _’ $ assume_tac >> drule_all_then assume_tac zts_start_suc >> gvs[])
          >> gvs[GSYM listTheory.SNOC_APPEND,rich_listTheory.DROP_SNOC,listTheory.FRONT_CONS,rich_listTheory.DROP_LENGTH_APPEND]
          >> gvs[listTheory.SNOC_APPEND,rich_listTheory.FILTER_APPEND]
          >> qmatch_goalsub_abbrev_tac ‘FILTER P l = _ ++ [x]’
          >> ‘FILTER P l = SNOC x (FILTER P (FRONT l))’ suffices_by gvs[rich_listTheory.SNOC_APPEND]
          >> ‘P x’ by (unabbrev_all_tac >> gvs[])
          >> ‘FILTER P l = FILTER P (SNOC x (FRONT l))’ suffices_by gvs[rich_listTheory.FILTER_SNOC]
          >> ‘l ≠ []’ by (spose_not_then assume_tac >> gvs[])
          >> ‘x = LAST l’ suffices_by gvs[listTheory.SNOC_LAST_FRONT]
          >> gvs[rich_listTheory.LAST_APPEND_NOT_NIL]
          >> unabbrev_all_tac
          >> gvs[w2w_w2w_8_64_32])
      >- (dxrule_then assume_tac (iffLR rich_listTheory.IS_PREFIX_APPEND)
          >> gvs[rich_listTheory.DROP_SNOC,rich_listTheory.DROP_LENGTH_APPEND,rich_listTheory.FILTER_SNOC]
          >> gvs[GSYM listTheory.SNOC_APPEND,rich_listTheory.DROP_SNOC,listTheory.FRONT_CONS,rich_listTheory.DROP_LENGTH_APPEND]
          >> gvs[listTheory.SNOC_APPEND,rich_listTheory.FILTER_APPEND]
          >> qmatch_goalsub_abbrev_tac ‘EVERY P1 (FILTER P2 l)’
          >> ‘l ≠ []’ by (spose_not_then assume_tac >> gvs[])
          >> ‘EVERY P1 (FILTER P2 (FRONT l ++ [LAST l]))’ suffices_by gvs[listTheory.APPEND_FRONT_LAST]
          >> gvs[listTheory.FILTER_APPEND_DISTRIB]
          >> unabbrev_all_tac
          >> gvs[]
          >> ‘LAST l = LAST (pre_events ++ l)’ suffices_by gvs[]
          >> gvs[rich_listTheory.LAST_APPEND_NOT_NIL,w2w_w2w_8_64_32]))
  >> apply_return
QED

Definition fun_notified_contract:
  fun_notified_contract pre_state pre_events memory base aux_base channel = 
  (FunContract [("channel",the_word channel)]
               (λs. uart_globals base aux_base s ∧ device_ready aux_base s ∧ s.memory = memory ∧
                    s.ffi.ffi_state = pre_state ∧ s.ffi.io_events = pre_events ∧
                    (channel = 1w ⇒ zts_at (unbox (s.memory (s.base_addr + 16w)))
                                          s.ffi.ffi_state.write_buffer
                                          (array (unbox (s.memory (s.base_addr + 16w))) (unbox (s.memory (s.base_addr + 24w))))
                                          s.be))
               (λt. uart_globals base aux_base t ∧ device_ready aux_base t ∧ t.ffi.ffi_state = pre_state ∧ t.memory = memory ∧
                    (channel ≠ 1w ⇒ t.ffi.io_events = pre_events) ∧
                    (channel = 1w ⇒
                    zts_at (unbox (t.memory (t.base_addr + 16w)))
                           t.ffi.ffi_state.write_buffer
                           (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w))))
                           t.be ∧ 
                    pre_events ≼ t.ffi.io_events ∧
                    let rest = DROP (LENGTH pre_events) t.ffi.io_events in
                        FILTER (λe. ∃w. e = IO_event (SharedMem MappedWrite) [4w] w) rest =
                            MAP (λc. IO_event (SharedMem MappedWrite) [4w] (ZIP ((word_to_bytes (w2w c : word32) F) ++ word_to_bytes (AUX_MU_IO_REG aux_base) F,
                                                                                 (word_to_bytes (w2w c : word32) F) ++ word_to_bytes (AUX_MU_IO_REG aux_base) F)))
                                (FRONT (get_zts (unbox (t.memory (t.base_addr + 16w)))
                                                t.ffi.ffi_state.write_buffer
                                                (array (unbox (t.memory (t.base_addr + 16w))) (unbox (t.memory (t.base_addr + 24w))))
                                                t.be)) ∧
                        EVERY (λe. ∃b. e = IO_event (SharedMem MappedRead) [4w] b ∨
                                       e = IO_event (SharedMem MappedRead) [1w] b) (FILTER (λe. ∀w. e ≠ IO_event (SharedMem MappedWrite) [4w] w) rest)))
                (word_with (λr. r = if channel = 1w then (0w : word64) else 1w)))
End

Theorem fun_notified:
  (fun_notified_contract pre_state pre_events memory base aux_base channel) refine (PanC (code ^fun_notified))
Proof
  begin_refinement_tac fun_notified_contract
  >> apply_seq ‘M = λs. channel = 1w ∧ Q (SOME (Return (ValWord 0w)),empty_locals s)’
  >- (apply_if
      >- (irule standalonecall_refinement_rule
          >> unabbrev_all_tac
          >> rw[]
          >> gvs[eval_def,uart_globals_def,has_kvar_vw_def,lookup_kvar_def,asmTheory.word_cmp_def,AllCaseEqs(),lookup_code_def,finite_mapTheory.FLOOKUP_UPDATE]
          >> irule refine_to_prog_hoare
          >> irule refine_transitive
          >> qexists ‘fun_puts_contract s.ffi.ffi_state s.ffi.io_events s.memory s.base_addr aux_base (unbox (s.memory (s.base_addr + 16w)))’
          >> gvs[REWRITE_RULE [code_def] fun_puts]
          >> gvs[fun_puts_contract,fun_contract_def]
          >> irule both_pre_post_refinement_rule
          >> rw[]
          >- (pairarg_tac
              >> gvs[empty_locals_def,uart_globals_def,device_ready_def,listTheory.EVERY_FILTER,finite_mapTheory.FLOOKUP_DEF]
              >> irule listTheory.EVERY_MONOTONIC
              >> HINT_EXISTS_TAC
              >> rw[]
              >> gvs[])
          >> gvs[finite_mapTheory.FUPDATE_LIST,finite_mapTheory.FAPPLY_FUPDATE_THM,the_word_def,uart_globals_def,device_ready_def,
                 has_kvar_vw_def,lookup_kvar_def,finite_mapTheory.FLOOKUP_DEF])
      >> apply_return
      >> gvs[asmTheory.word_cmp_def,device_ready_def,uart_globals_def,has_kvar_vw_def,lookup_kvar_def])
  >> apply_return
QED
