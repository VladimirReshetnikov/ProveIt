(** Kernel audit for reverse-order carried consistency closure. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthNativeFinalCarriedConsistencyAfterOrdinarySoundness.

Module
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterOrdinarySoundnessAudit.

Import
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterOrdinarySoundness.

(** The generic endpoint merges the ordinary certificate's hidden witnessed
    context after the carried bridge has already been constructed. *)
Check
  raw_dynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridge_of_carried_then_ordinary.

(** The direct specialization and final-stage closer preserve the literal
    derivation-soundness code selected by the carried package. *)
Check
  raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_carried_then_ordinary.
Check
  raw_dynamicTruthNativeFinalStagedNextFinalProof_of_direct_carried_then_ordinary.

Print Assumptions
  raw_dynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridge_of_carried_then_ordinary.
Print Assumptions
  raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_carried_then_ordinary.
Print Assumptions
  raw_dynamicTruthNativeFinalStagedNextFinalProof_of_direct_carried_then_ordinary.

End
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterOrdinarySoundnessAudit.
