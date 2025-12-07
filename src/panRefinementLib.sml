load "HolSmtLib";

structure panRefinementLib :> panRefinementLib =
struct

open HolKernel BasicProvers boolLib bossLib blastLib simpLib HolSmtLib
open asmTheory pred_setTheory finite_mapTheory wordsTheory
open wordLangTheory
open panReducedLangTheory panReducedSemTheory panReducedPropsTheory panPredicateTheory panRefinementTheory

val pan_refinement_ss = srw_ss() && [clkfree_p_cases,clkfree_p_conj,clkfree_p_disj,clkfree_p_neg,
                                     clkfree_p_monotonic,
                                     clkfree_p_cases,clkfree_q_conj,clkfree_q_disj,clkfree_q_neg,
                                     clkfree_q_monotonic,
                                     clkfree_pq,clkfree_qp,clkfree_qqn,clkfree_qnif,
                                     clkfree_pqr,clkfree_qr_cases,
                                     clkfree_pqe,clkfree_qe_cases,
                                     varfree_p_def,varfree_q_def,
                                     evaluates_def,clkfree_evaluates,
                                     evaluates_shape_def,clkfree_evaluates_shape,
                                     evaluates_to_def,clkfree_evaluates_to,evaluates_to_const,
                                     evaluates_to_word_def,clkfree_evaluates_to_word,
                                     evaluates_to_true_def,clkfree_evaluates_to_true,
                                     evaluates_to_false_def,clkfree_evaluates_to_false,
                                     evaluates_to_word_lem,evaluates_to_word_contradict,
                                     var_eq_val_def,clkfree_var_eq_val,clkfree_var_eq_val_ex_pred,
                                     var_eq_mem_def,clkfree_var_eq_mem,

                                     while_body_pre_def,clkfree_while_body_pre,
                                     while_body_post_def,clkfree_while_body_post,

                                     empty_locals_def,size_of_shape_def,

                                     eval_def,

                                     var_exp_def,
                                     is_variant_def,
                                     subst_def,
                                     valid_value_def,is_valid_value_def,shape_of_def,shape_of_val,
                                     word_cmp_def,word_op_def,pan_op_def,
                                     mem_load_def,
                                     FLOOKUP_UPDATE,DOMSUB_FLOOKUP_NEQ,
                                     GSYM WORD_LO,
                                     EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF, SING_DEF,
                                     NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_INTER, IN_DIFF,
                                     IN_INSERT, IN_DELETE, IN_REST, IN_BIGINTER, IN_BIGUNION, IN_IMAGE,
                                     GSPECIFICATION, IN_DEF];

val pan_refinement_thms_tac = fn refinement_rule =>
                              fn extra_thms =>
                                 rw[]
                                 >> irule refinement_rule
                                 >> unabbrev_all_tac
                                 >> gvs[]
                                 >> rpt (CHANGED_TAC (rw_tac pan_refinement_ss extra_thms))
                                 >> TRY (HINT_EXISTS_TAC)
                                 >> every_case_tac
                                 >> fs[]
                                 >> rpt (CHANGED_TAC (global_simp_tac {elimvars = true,
                                                                       strip = true,
                                                                       droptrues = true,
                                                                       oldestfirst = true}
                                                                      pan_refinement_ss
                                                                      extra_thms
                                                      >> every_case_tac))
                                 >> TRY (first_x_assum $ irule)
                                 >> spose_not_then assume_tac
                                 >> gvs[clkfree_p_def,clkfree_q_def,clkfree_qr_def,clkfree_qe_def,
                                        eval_upd_clock_eq];

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
