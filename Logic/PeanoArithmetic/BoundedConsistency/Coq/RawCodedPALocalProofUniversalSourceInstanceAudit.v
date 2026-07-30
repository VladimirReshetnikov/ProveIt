(** Audit surface for generic universal-source proof-code compilation. *)

From BoundedPAConsistency Require Import
  RawCodedPALocalProofUniversalSourceInstance.

Import PABoundedRawCodedPALocalProofUniversalSourceInstance.

Check raw_codedPALocalProof_universalSourceInstance_under_directPrefix.

Print Assumptions
  raw_codedPALocalProof_universalSourceInstance_under_directPrefix.
