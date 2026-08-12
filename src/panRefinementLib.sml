load "helperLib";
load "stringLib";

structure panRefinementLib :> panRefinementLib =
struct

open panMiscTheory panPredicateTheory panPtreeConversionTheory panRefinementTheory panSemTheory
open helperLib stringLib hurdUtils bossLib pred_setLib
open Tactical Tactic Conv 
open Drule 
open boolSyntax 
open HolKernel

local
  val f = List.mapPartial (fn s => case remove_whitespace s of "" => NONE | x => SOME x) o String.tokens (fn c => c = #"\n")
in
  fun quote_to_strings q = f (Portable.quote_to_string (fn _ => raise General.Bind) q)
end

fun parse q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    (rhs o concl o EVAL o (inst_ty [``:'a`` |-> ``:64``]) o rhs o concl) (EVAL ``case ((HD o OUTL o panPtreeConversion$parse_topdecs_to_ast) ^code) of
                                                                                 | Function f => (f.params,drop_annot f.body)``)
  end

val pred_simp_tac = fn more => simp_tac
                               (srw_ss() ++ boolSimps.CONJ_ss ++ boolSimps.DNF_ss)
                               ((GSYM boolTheory.CONJ_ASSOC) :: (more @ [finite_mapTheory.DOMSUB_FAPPLY_THM,
			                                                 finite_mapTheory.FAPPLY_FUPDATE_THM,
                                                                         finite_mapTheory.FLOOKUP_UPDATE]));

val begin_refinement_tac = fn contract => rpt (strip_tac)
                                          >> pred_simp_tac (contract :: [panMiscTheory.word_def,
				                                         panMiscTheory.word_with_def,
                                                                         panMiscTheory.the_word_def,
                                                                         panMiscTheory.fun_contract_def,
                                                                         panMiscTheory.code_def]);

val apply_dec = qmatch_goalsub_abbrev_tac ‘(HoareC P Q) refine (PanC (Dec v sh src subprog))’
                >> irule refine_transitive
                >> qexists ‘DecC v sh src (PanC subprog)’
                >> gvs[dec_refinement_rule_pan]
                >> irule refine_transitive
                >> qexists ‘DecC v sh src (DecBC P v src Q)’
                >> conj_tac
                >| [irule dec_refinement_rule >> unabbrev_all_tac >> rw[] >> gvs[GSYM mlstringTheory.mlstring_11],
                    irule refine_monotonic_dec >> unabbrev_all_tac >> pred_simp_tac [finite_mapTheory.FLOOKUP_DEF,
                                                                                     panPredicateTheory.var_eq_def,
                                                                                     panSemTheory.eval_def]
                                               >> qmatch_goalsub_abbrev_tac ‘(HoareC P Q) refine (PanC _)’];

val apply_assign = irule assign_refinement_rule
                   >> unabbrev_all_tac
		   >> rw[panPredicateTheory.valid_value_def,panSemTheory.eval_def,panSemTheory.is_valid_value_def,
			 panPredicateTheory.evaluates_def,wordLangTheory.word_op_def,wordLangTheory.word_sh_def,
			 panPredicateTheory.subst_def,panSemTheory.pan_op_def,
			 finite_mapTheory.FLOOKUP_DEF,pred_setTheory.DELETE_INSERT]
	           >> gvs[]
		   >> TRY IF_CASES_TAC
		   >> gvs[finite_mapTheory.FAPPLY_FUPDATE_THM,panLangTheory.size_of_shape_def,panSemTheory.shape_of_def]
		   >> TRY (ASM_SET_TAC[]);

val apply_seq = fn tm => qmatch_goalsub_abbrev_tac ‘(HoareC P Q) refine (PanC (Seq subprogL subprogR))’
                         >> irule refine_transitive
                         >> qexists ‘SeqC (PanC subprogL) (PanC subprogR)’
                         >> gvs[seq_refinement_rule_pan]           
                         >> qabbrev_tac tm
                         >> irule refine_transitive
                         >> qexists ‘SeqC (SeqBC P M Q) (HoareC M Q)’
                         >> conj_tac
                         >- gvs[seq_refinement_rule]
                         >> irule refine_transitive
                         >> qexists ‘SeqC (PanC subprogL) (HoareC M Q)’
                         >> conj_tac
                         >| [irule (cj 1 refine_monotonic_seq) >> unabbrev_all_tac >> pred_simp_tac [] >> qmatch_goalsub_abbrev_tac ‘(HoareC P Q) refine (PanC _)’,
                             irule (cj 2 refine_monotonic_seq) >> unabbrev_all_tac >> pred_simp_tac [] >> qmatch_goalsub_abbrev_tac ‘(HoareC P Q) refine (PanC _)’];

val apply_if = qmatch_goalsub_abbrev_tac ‘(HoareC P Q) refine (PanC (If e subprogL subprogR))’
               >> irule refine_transitive
               >> qexists ‘IfC e (PanC subprogL) (PanC subprogR)’
               >> gvs[if_refinement_rule_pan]
               >> irule refine_transitive
               >> qexists ‘IfC e (IfBCT P e Q) (IfBCF P e Q)’
               >> conj_tac
               >- (irule if_refinement_rule
	           >> unabbrev_all_tac
		   >> gvs[evaluates_to_word_def,eval_def,finite_mapTheory.FLOOKUP_DEF,finite_mapTheory.FAPPLY_FUPDATE_THM,
		          wordLangTheory.word_op_def,asmTheory.word_cmp_def]
		   >> rw[]
		   >> gvs[]
		   >> TRY (BasicProvers.FULL_CASE_TAC >> gvs[])
		   >> ASM_SET_TAC[])
               >> irule refine_transitive
               >> qexists ‘IfC e (PanC subprogL) (IfBCF P e Q)’
               >> conj_tac
               >| [irule (cj 1 refine_monotonic_if) >> unabbrev_all_tac >> pred_simp_tac [evaluates_to_true_def,eval_def] >> qmatch_goalsub_abbrev_tac ‘(HoareC P Q) refine (PanC _)’,
                   irule (cj 2 refine_monotonic_if) >> unabbrev_all_tac >> pred_simp_tac [evaluates_to_false_def,eval_def] >> qmatch_goalsub_abbrev_tac ‘(HoareC P Q) refine (PanC _)’];

val apply_shmemload = fn ffi => irule shmemload_refinement_rule
                                >> unabbrev_all_tac
	                        >> rw[panPredicateTheory.evaluates_to_word_def,panSemTheory.eval_def,finite_mapTheory.FLOOKUP_DEF,finite_mapTheory.DOMSUB_FAPPLY_THM,
                                      panPredicateTheory.in_sh_memaddrs_def,panPredicateTheory.the_eval_vw_def,panPredicateTheory.the_eval_def,
                                      panPredicateTheory.has_kvar_vw_def,panSemTheory.lookup_kvar_def,panPredicateTheory.var_eq_def]
                                >>~- ([`?w. x IN FDOM s /\ s ' x = ValWord w`],(gvs[SF SFY_ss] >> ASM_SET_TAC[]))
                                >> TRY IF_CASES_TAC
                                >>~- ([`THE NONE`],ASM_SET_TAC[])
                                >> rw (ffi :: [panWeakestPreconditionTheory.hoareFFI_def,ffiTheory.call_FFI_def,panSemTheory.nb_op_def,
				               panSemTheory.set_kvar_def,panSemTheory.set_var_def,
					       pred_setTheory.DELETE_INSERT,finite_mapTheory.FAPPLY_FUPDATE_THM,
					       wordLangTheory.word_op_def]);
                                 
val apply_shmemstore = fn ffi => irule shmemstore_refinement_rule
                                 >> unabbrev_all_tac
				 >> rw[panPredicateTheory.evaluates_to_word_def,panSemTheory.eval_def,finite_mapTheory.FLOOKUP_DEF,finite_mapTheory.DOMSUB_FAPPLY_THM,
                                       panPredicateTheory.in_sh_memaddrs_def,panPredicateTheory.the_eval_vw_def,panPredicateTheory.the_eval_def]
				 >> TRY IF_CASES_TAC
                                 >>~- ([`THE NONE`],ASM_SET_TAC[])
				 >> rw(ffi :: [panWeakestPreconditionTheory.hoareFFI_def,ffiTheory.call_FFI_def,panSemTheory.nb_op_def,
				               wordLangTheory.word_op_def]);

val apply_return = irule return_refinement_rule
                   >> unabbrev_all_tac
		   >> rw[panPredicateTheory.the_eval_def,
			 panSemTheory.eval_def,
			 panPredicateTheory.evaluates_def,wordLangTheory.word_op_def,wordLangTheory.word_sh_def,
			 finite_mapTheory.FLOOKUP_DEF,pred_setTheory.DELETE_INSERT]
	           >> gvs[panSemTheory.empty_locals_def]
		   >> TRY IF_CASES_TAC
		   >> gvs[finite_mapTheory.FAPPLY_FUPDATE_THM,panLangTheory.size_of_shape_def,panSemTheory.shape_of_def]
		   >> TRY (ASM_SET_TAC[])
end;


