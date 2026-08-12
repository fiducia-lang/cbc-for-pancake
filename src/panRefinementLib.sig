signature panRefinementLib =
sig
    include Abbrev

    val fun_contract_ss               : simpLib.simpset

    val pan_refinement_ss             : simpLib.simpset

    val pan_refinement_tac            : thm -> tactic
    val pan_refinement_tac_blast      : thm -> tactic
    val pan_refinement_tac_z3         : thm -> tactic
    val pan_refinement_tac_z3o        : thm -> tactic

    val pan_refinement_thms_tac       : thm -> thm list -> tactic
    val pan_refinement_thms_tac_blast : thm -> thm list -> tactic
    val pan_refinement_thms_tac_z3    : thm -> thm list -> tactic
    val pan_refinement_thms_tac_z3o   : thm -> thm list -> tactic
end