(** Assumption audit for predecessor joint-state discharge. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthPredecessorJointStateDischarge.

Import PABoundedRawCodedDynamicTruthPredecessorJointStateDischarge.

Check raw_codedPALocalProofOf_predecessor_joint_state_discharge.

Print Assumptions
  raw_codedPALocalProofOf_predecessor_joint_state_discharge.
