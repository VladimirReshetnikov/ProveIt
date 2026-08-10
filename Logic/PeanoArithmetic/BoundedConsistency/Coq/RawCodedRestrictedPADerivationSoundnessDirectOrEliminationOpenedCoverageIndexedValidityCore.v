(** Compatibility core for the split Or-E indexed-validity development.

    Keeping this module as a tiny export layer avoids rebuilding one large proof
    term: the constructor-indexed view and the final law assembly are checked in
    separate files. *)

From BoundedPAConsistency Require Export
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageIndexedChildView
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLawAssembly.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageIndexedValidityCore.

Export
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageIndexedChildView.
Export
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLawAssembly.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageIndexedValidityCore.
