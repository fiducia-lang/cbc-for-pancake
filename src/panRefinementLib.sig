signature panRefinementLib =
sig
    include Abbrev

    val pan_refinement_ss       : simpLib.simpset
    val pan_refinement_thms_tac : thm -> thm list -> tactic
    val pan_refinement_tac      : thm -> tactic
end