load "HolSmtLib";

structure panRefinementLib :> panRefinementLib =
struct

open HolKernel BasicProvers boolLib bossLib blastLib simpLib HolSmtLib
open asmTheory pred_setTheory finite_mapTheory wordsTheory
open wordLangTheory
open panLangTheory panMiscTheory panSemTheory panPropsTheory panPredicateTheory panRefinementTheory

val fun_contract_ss   = srw_ss() && [word_def, word_with_def, the_word_def,
                                     fun_contract_def, immutable_def];

val pan_refinement_ss = srw_ss() && [varfree_p_def,varfree_q_def,
                                     evaluates_def,
                                     evaluates_shape_def,
                                     evaluates_to_def,
                                     evaluates_to_word_def,
                                     evaluates_to_true_def,
                                     evaluates_to_false_def,
                                     evaluates_to_word_lem,evaluates_to_word_contradict,

                                     while_body_pre_def,
                                     while_body_post_def,

                                     empty_locals_def,size_of_shape_def,

                                     eval_def,
                                     var_eq_def,
                                     var_exp_def,
                                     subst_def,
                                     valid_value_def,is_valid_value_def,shape_of_def,shape_of_val,
                                     word_cmp_def,word_op_def,pan_op_def,
                                     mem_load_def,
                                     FLOOKUP_UPDATE,DOMSUB_FLOOKUP_NEQ,
                                     GSYM WORD_LO,
                                     EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF, SING_DEF,
                                     NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_INTER, IN_DIFF,
                                     IN_INSERT, IN_DELETE, IN_REST, IN_BIGINTER, IN_BIGUNION, IN_IMAGE,
                                     GSPECIFICATION, IN_DEF,
				     AllCaseEqs()];

val pan_refinement_thms_tac = fn refinement_rule =>
                              fn extra_thms =>
                                 rw[]
                                 >> irule refinement_rule
                                 >> unabbrev_all_tac
                                 >> gvs[]
                                 >> rpt (CHANGED_TAC (rw_tac pan_refinement_ss extra_thms))
                                 >> TRY HINT_EXISTS_TAC
                                 >> fs[]
                                 >> rpt (CHANGED_TAC (global_simp_tac {elimvars = true,
                                                                       strip = true,
                                                                       droptrues = true,
                                                                       oldestfirst = true}
                                                                      pan_refinement_ss
                                                                      extra_thms))
                                 >> TRY (first_x_assum $ irule)
				 >> TRY (first_x_assum $ drule_then assume_tac)
                                 >> spose_not_then assume_tac
                                 >> gvs[eval_upd_clock_eq];

val pan_refinement_thms_tac_blast = fn refinement_rule =>
                                    fn extra_thms =>
                                       pan_refinement_thms_tac refinement_rule extra_thms
                                       >> FULL_BBLAST_TAC;

val pan_refinement_thms_tac_z3 = fn refinement_rule =>
                                 fn extra_thms =>
                                    pan_refinement_thms_tac refinement_rule extra_thms
                                    >> z3_tac extra_thms;

val pan_refinement_thms_tac_z3o = fn refinement_rule =>
                                  fn extra_thms =>
                                     pan_refinement_thms_tac refinement_rule extra_thms
                                     >> z3o_tac extra_thms;

val pan_refinement_tac       = fn rule => pan_refinement_thms_tac       rule [];
val pan_refinement_tac_blast = fn rule => pan_refinement_thms_tac_blast rule [];
val pan_refinement_tac_z3    = fn rule => pan_refinement_thms_tac_z3    rule [];
val pan_refinement_tac_z3o   = fn rule => pan_refinement_thms_tac_z3o   rule [];

end
