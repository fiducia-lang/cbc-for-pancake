signature panRefinementLib =
sig

  include Abbrev 

  val parse                : 'a quotation -> term
  val begin_refinement_tac : thm -> tactic

  val apply_dec            : tactic
  val apply_assign         : tactic
  val apply_seq            : term quotation -> tactic
  val apply_if             : tactic

  val apply_return         : tactic

  val apply_shmemload      : thm -> tactic
  val apply_shmemstore     : thm -> tactic

end
