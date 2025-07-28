(* These proves are based on cakeml/pancake/semantics/panSemScript.sml *)

Definition hoare_def:
  hoare P prog Q ⇔ ∀s. s ∈ P ⇒ let (r, t) = evaluate (prog, s) in
                               r = NONE ∧ t ∈ Q
End

Definition wp_def:
  wp prog Q = BIGUNION {P | hoare P prog Q}
End

Theorem wp_is_weakest_precondition:
  R = wp prog Q ⇒ (hoare R prog Q ∧ ∀P. hoare P prog Q ⇒ P ⊆ R)
Proof
  rw[wp_def]
  >- (rw[hoare_def] >> gvs[])
  >- (rw[BIGUNION,SUBSET_DEF] >> qexists_tac ‘P’ >> rw[])
QED

Theorem weakest_precondition_is_wp:
  (hoare R prog Q ∧ ∀P. hoare P prog Q ⇒ P ⊆ R) ⇒ R = wp prog Q
Proof
  rw[EXTENSION]
  >> iff_tac
  >> rw[]
  >- (rw[wp_def] >> qexists_tac ‘R’ >> rw[])
  >- (gvs[wp_def] >> ‘s ⊆ R’ by (rw[]) >> gvs[SUBSET_DEF])
QED

Theorem wp_causes_termination:
  ∀s prog Q. s ∈ wp prog Q ⇒ FST (evaluate (prog, s)) = NONE
Proof
  rw[wp_def,hoare_def]
  >> first_x_assum $ (drule_then assume_tac)
  >> first_x_assum $ (fn thm => assume_tac (CONV_RULE GEN_BETA_CONV thm))
  >> rw[]
QED

Theorem wp_causes_postcondition:
  ∀s prog Q. s ∈ wp prog Q ⇒ SND (evaluate (prog, s)) ∈ Q
Proof
  rw[wp_def,hoare_def]
  >> first_x_assum $ (drule_then assume_tac)
  >> first_x_assum $ (fn thm => assume_tac (CONV_RULE GEN_BETA_CONV thm))
  >> rw[]
QED

Theorem all_preconditions_in_wp:
  ∀P prog Q. hoare P prog Q ⇒ P ⊆ wp prog Q
Proof
  rw[hoare_def,wp_def,BIGUNION,SUBSET_DEF]
  >> qexists_tac ‘P’
  >> rw[]
QED

Theorem all_prestates_in_wp:
  ∀x P prog Q. hoare {x} prog Q ⇒ x ∈ wp prog Q
Proof
  rw[]
  >> assume_tac all_preconditions_in_wp
  >> first_x_assum $ (drule_then assume_tac)
  >> gvs[SUBSET_DEF]
QED

Theorem wp_skip:
  wp Skip Q = Q
Proof
  rw[wp_def,hoare_def,evaluate_def,BIGUNION,EXTENSION]
  >> iff_tac >> rw[]
  >- gvs[]
  >- (qexists_tac ‘Q’ >> rw[])
QED

Theorem wp_seq:
  wp p1 (wp p2 Q) = wp (Seq p1 p2) Q
Proof
  rw[EXTENSION,BIGUNION,wp_def]
  >> iff_tac
  >> rw[]
  >> qexists_tac ‘s’
  >> gvs[hoare_def,evaluate_def]
  >> rw[]
  >> rpt (first_x_assum $ (drule_then assume_tac)
          >> first_x_assum (fn thm => assume_tac (CONV_RULE GEN_BETA_CONV thm))
          >> gvs[])
  >> CONV_TAC GEN_BETA_CONV
  >> rw[]
  >- (CONV_TAC (LAND_CONV $ RAND_CONV $ GEN_BETA_CONV) >> rw[])
  >- (CONV_TAC (LAND_CONV $ RAND_CONV $ GEN_BETA_CONV) >> rw[])
  >> rpt (first_x_assum (fn thm => assume_tac (CONV_RULE (LAND_CONV $ RAND_CONV $ GEN_BETA_CONV) thm)))
  >> Cases_on ‘FST (evaluate (p1,s'))’
  >> gvs[]
  >> qexists_tac ‘wp p2 Q’
  >> rw[]
  >- (CONV_TAC GEN_BETA_CONV
      >> assume_tac wp_causes_termination
      >> assume_tac wp_causes_postcondition
      >> rpt (first_x_assum $ (drule_then assume_tac))
      >> rw[])
  >> ‘hoare {(SND (evaluate (p1,s')))} p2 Q’ suffices_by (gvs[all_prestates_in_wp])
  >> rw[hoare_def]
  >> CONV_TAC GEN_BETA_CONV
  >> rw[]
QED

