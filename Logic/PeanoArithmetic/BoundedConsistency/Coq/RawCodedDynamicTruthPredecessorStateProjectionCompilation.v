(**
  Represented projections of the two predecessor-state assumptions.

  The collision context has Pi state membership at its head and Sigma state
  membership immediately beneath it.  Each membership is itself a
  conjunction of a strict row bound and a synchronized four-table lookup.
  This module exposes those four atoms as local PA proof roots.  It assumes
  only realizability of the caller's tail; no witnessed-axiom structure or
  context self-shift is needed for assumption introduction and [And-E].
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedProofAtomicAdequacyStandard
  RawCodedProofAssumptionLeaf
  RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation.

Module PABoundedRawCodedDynamicTruthPredecessorStateProjectionCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.

(** The four literal PA atoms under the two conjunction heads. *)
Definition dynamicTruthPredecessorSigmaStateBoundBodyFormula : formula :=
  Formula.ltTermAt (tVar 2) (tVar 7).

Definition dynamicTruthPredecessorSigmaStateLookupBodyFormula : formula :=
  fixedLevelStateLookupTermAt
    (tVar 15) (tVar 14) (tVar 13) (tVar 12)
    (tVar 11) (tVar 10) (tVar 9) (tVar 8)
    (tVar 2) tZero (tVar 0) (tVar 4) (tVar 3).

Definition dynamicTruthPredecessorPiStateBoundBodyFormula : formula :=
  Formula.ltTermAt (tVar 1) (tVar 7).

Definition dynamicTruthPredecessorPiStateLookupBodyFormula : formula :=
  fixedLevelStateLookupTermAt
    (tVar 15) (tVar 14) (tVar 13) (tVar 12)
    (tVar 11) (tVar 10) (tVar 9) (tVar 8)
    (tVar 1) (Term.numeral 1) (tVar 0) (tVar 4) (tVar 3).

Lemma dynamicTruthPredecessorSigmaStateMemberBodyFormula_shape :
  dynamicTruthPredecessorSigmaStateMemberBodyFormula =
  pAnd dynamicTruthPredecessorSigmaStateBoundBodyFormula
    dynamicTruthPredecessorSigmaStateLookupBodyFormula.
Proof. reflexivity. Qed.

Lemma dynamicTruthPredecessorPiStateMemberBodyFormula_shape :
  dynamicTruthPredecessorPiStateMemberBodyFormula =
  pAnd dynamicTruthPredecessorPiStateBoundBodyFormula
    dynamicTruthPredecessorPiStateLookupBodyFormula.
Proof. reflexivity. Qed.

Definition rawDynamicTruthPredecessorSigmaStateBoundBodyCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    dynamicTruthPredecessorSigmaStateBoundBodyFormula.

Definition rawDynamicTruthPredecessorSigmaStateLookupBodyCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    dynamicTruthPredecessorSigmaStateLookupBodyFormula.

Definition rawDynamicTruthPredecessorPiStateBoundBodyCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    dynamicTruthPredecessorPiStateBoundBodyFormula.

Definition rawDynamicTruthPredecessorPiStateLookupBodyCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    dynamicTruthPredecessorPiStateLookupBodyFormula.

Arguments rawDynamicTruthPredecessorSigmaStateBoundBodyCode M
  : clear implicits.
Arguments rawDynamicTruthPredecessorSigmaStateLookupBodyCode M
  : clear implicits.
Arguments rawDynamicTruthPredecessorPiStateBoundBodyCode M
  : clear implicits.
Arguments rawDynamicTruthPredecessorPiStateLookupBodyCode M
  : clear implicits.

Lemma rawDynamicTruthPredecessorSigmaStateMemberBodyCode_shape : forall
    (M : RawPAModel),
  rawDynamicTruthPredecessorSigmaStateMemberBodyCode M =
  rawFormulaAndCode M
    (rawDynamicTruthPredecessorSigmaStateBoundBodyCode M)
    (rawDynamicTruthPredecessorSigmaStateLookupBodyCode M).
Proof. reflexivity. Qed.

Lemma rawDynamicTruthPredecessorPiStateMemberBodyCode_shape : forall
    (M : RawPAModel),
  rawDynamicTruthPredecessorPiStateMemberBodyCode M =
  rawFormulaAndCode M
    (rawDynamicTruthPredecessorPiStateBoundBodyCode M)
    (rawDynamicTruthPredecessorPiStateLookupBodyCode M).
Proof. reflexivity. Qed.

(** The four resources remain existential in their proof codes. *)
Record RawDynamicTruthPredecessorStateProjectionRootsAt
    (M : RawPAModel) (baseContext : M) : Prop := {
  rawDynamicTruthPredecessorStateProjection_sigmaBound : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthPredecessorSigmaStateBoundBodyCode M) root;
  rawDynamicTruthPredecessorStateProjection_sigmaLookup : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthPredecessorSigmaStateLookupBodyCode M) root;
  rawDynamicTruthPredecessorStateProjection_piBound : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthPredecessorPiStateBoundBodyCode M) root;
  rawDynamicTruthPredecessorStateProjection_piLookup : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthPredecessorPiStateLookupBodyCode M) root
}.

Arguments RawDynamicTruthPredecessorStateProjectionRootsAt M baseContext
  : clear implicits.

(** Project both assumptions in their final joint context.  The Sigma leaf
    is first introduced in the one-head Sigma context and then transplanted
    beneath the adequate Pi head; the Pi leaf is already the outer head. *)
Theorem raw_dynamicTruthPredecessorStateProjectionRootsAt_of_realizable :
  forall (M : RawPAModel), RawPASatisfies M -> forall baseContext,
  RawContextListRealizable M baseContext ->
  RawDynamicTruthPredecessorStateProjectionRootsAt M baseContext.
Proof.
  intros M hPA baseContext hbase.
  assert (hsigmaContext : RawContextListRealizable M
      (rawDynamicTruthPredecessorSigmaStateContext M baseContext)).
  {
    exact (raw_contextList_cons_realizable M hPA baseContext
      (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M) hbase).
  }
  pose proof (raw_codedPALocalProofOf_assumption M hPA baseContext
    (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M) hbase)
    as hsigmaAtSigmaContext.
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    (rawDynamicTruthPredecessorSigmaStateContext M baseContext)
    (rawDynamicTruthPredecessorPiStateMemberBodyCode M)
    (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M)
    (rawProofAssumptionRoot M
      (rawDynamicTruthPredecessorSigmaStateContext M baseContext)
      (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M))
    (raw_quotedFormula_atomically_adequate M hPA
      dynamicTruthPredecessorPiStateMemberBodyFormula)
    hsigmaContext hsigmaAtSigmaContext)
    as [sigmaJointRoot hsigmaJoint].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    (rawDynamicTruthPredecessorSigmaStateContext M baseContext)
    (rawDynamicTruthPredecessorPiStateMemberBodyCode M) hsigmaContext)
    as hpiJoint.
  rewrite rawDynamicTruthPredecessorSigmaStateMemberBodyCode_shape
    in hsigmaJoint.
  rewrite rawDynamicTruthPredecessorPiStateMemberBodyCode_shape
    in hpiJoint.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawDynamicTruthPredecessorSigmaStateBoundBodyCode M)
    (rawDynamicTruthPredecessorSigmaStateLookupBodyCode M)
    sigmaJointRoot hsigmaJoint) as hsigmaBound.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA
    (rawDynamicTruthPredecessorJointStateContext M baseContext)
    (rawDynamicTruthPredecessorSigmaStateBoundBodyCode M)
    (rawDynamicTruthPredecessorSigmaStateLookupBodyCode M)
    sigmaJointRoot hsigmaJoint) as hsigmaLookup.
  lazymatch type of hpiJoint with
  | RawCodedPALocalProofOf _ _ _ ?piJointRoot =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA
        (rawDynamicTruthPredecessorJointStateContext M baseContext)
        (rawDynamicTruthPredecessorPiStateBoundBodyCode M)
        (rawDynamicTruthPredecessorPiStateLookupBodyCode M)
        piJointRoot hpiJoint) as hpiBound;
      pose proof (raw_codedPALocalProofOf_andE2 M hPA
        (rawDynamicTruthPredecessorJointStateContext M baseContext)
        (rawDynamicTruthPredecessorPiStateBoundBodyCode M)
        (rawDynamicTruthPredecessorPiStateLookupBodyCode M)
        piJointRoot hpiJoint) as hpiLookup;
      constructor;
      [ exists (rawProofAndERoot M RawAndLeft
          (rawDynamicTruthPredecessorJointStateContext M baseContext)
          (rawDynamicTruthPredecessorSigmaStateBoundBodyCode M)
          (rawDynamicTruthPredecessorSigmaStateLookupBodyCode M)
          sigmaJointRoot); exact hsigmaBound
      | exists (rawProofAndERoot M RawAndRight
          (rawDynamicTruthPredecessorJointStateContext M baseContext)
          (rawDynamicTruthPredecessorSigmaStateBoundBodyCode M)
          (rawDynamicTruthPredecessorSigmaStateLookupBodyCode M)
          sigmaJointRoot); exact hsigmaLookup
      | exists (rawProofAndERoot M RawAndLeft
          (rawDynamicTruthPredecessorJointStateContext M baseContext)
          (rawDynamicTruthPredecessorPiStateBoundBodyCode M)
          (rawDynamicTruthPredecessorPiStateLookupBodyCode M)
          piJointRoot); exact hpiBound
      | exists (rawProofAndERoot M RawAndRight
          (rawDynamicTruthPredecessorJointStateContext M baseContext)
          (rawDynamicTruthPredecessorPiStateBoundBodyCode M)
          (rawDynamicTruthPredecessorPiStateLookupBodyCode M)
          piJointRoot); exact hpiLookup ]
  end.
Qed.

End PABoundedRawCodedDynamicTruthPredecessorStateProjectionCompilation.
