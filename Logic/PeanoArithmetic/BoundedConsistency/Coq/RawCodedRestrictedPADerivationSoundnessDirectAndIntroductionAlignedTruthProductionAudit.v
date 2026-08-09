(**
  Audit surface for aligned And-I parent-truth production.

  The two compiler interfaces below distinguish literal append resources from
  the growing global source they produce.  The remaining checks expose every
  theorem used to identify that source with truth of the And-I conclusion and
  then discharge the final one-root semantic residual on a witnessed tail.
*)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProductionAudit.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

(** Literal append resources and their derived growing-source interface. *)
Check
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt.
Check RawCoqRestrictedPADirectModeZeroGlobalSourceStandardTailCompilerAt.
Check
  raw_modeZeroGlobalSourceStandardTailCompilerAt_of_append_concrete_row.

(** The concrete And-I root is stable under row opening and native alignment
    identifies its generated source with parent-conjunction truth. *)
Check coqRestrictedPADirectAndIntroduction_mode_zero_parent_rows_stable.
Check raw_andIntroduction_mode_zero_parent_source_aligned.

(** The resulting compiler closes the exact truth component expected by the
    synchronized And-I child/truth integration boundary. *)
Check
  raw_restrictedPADirectAndIntroductionTruthCoreStandardTailCompiler_of_aligned_append_concrete_row.
Check raw_selectedAndIntroductionCoreTail_of_aligned_append_concrete_row.

Print Assumptions
  raw_modeZeroGlobalSourceStandardTailCompilerAt_of_append_concrete_row.
Print Assumptions
  coqRestrictedPADirectAndIntroduction_mode_zero_parent_rows_stable.
Print Assumptions raw_andIntroduction_mode_zero_parent_source_aligned.
Print Assumptions
  raw_restrictedPADirectAndIntroductionTruthCoreStandardTailCompiler_of_aligned_append_concrete_row.
Print Assumptions
  raw_selectedAndIntroductionCoreTail_of_aligned_append_concrete_row.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProductionAudit.
