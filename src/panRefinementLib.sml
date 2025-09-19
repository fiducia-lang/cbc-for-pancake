structure panRefinementLib :> panRefinementLib =
struct

open HolKernel BasicProvers boolLib bossLib blastLib
open asmTheory finite_mapTheory wordsTheory
open wordLangTheory
open panSemTheory panPredicateTheory panRefinementTheory

val pan_refinement_ss = srw_ss() && [clkfree_p_def,clkfree_q_def,
                                     while_body_pre_def,while_body_post_def,is_variant_def,
                                     subst_def,eval_def,
                                     evaluates_to_word_def,evaluates_to_false_def,evaluates_to_true_def,
                                     valid_value_def,is_valid_value_def,shape_of_def,
                                     word_cmp_def,word_op_def,
                                     FLOOKUP_UPDATE,
                                     GSYM WORD_LO];

val pan_refinement_thms_tac = fn refinement_rule =>
                              fn extra_thms =>
                                rw[]
                                >> irule refinement_rule
                                >> unabbrev_all_tac
                                >> rpt (CHANGED_TAC (rw_tac pan_refinement_ss extra_thms))
                                >> every_case_tac
                                >> gvs[]
                                >> FULL_BBLAST_TAC;

val pan_refinement_tac = fn rule => pan_refinement_thms_tac rule [];

end
