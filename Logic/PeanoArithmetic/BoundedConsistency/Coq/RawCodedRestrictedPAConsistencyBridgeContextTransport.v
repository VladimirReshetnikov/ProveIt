(**
  Transport local proofs when the witnessed base of the restricted-
  consistency bridge grows.

  The canonical bridge context is a fixed four-formula prefix over its PA
  base: the three shifted existential witnesses and the projected proof
  fields.  Several independent proof compilers may extend that base by
  finite standard PA-axiom prefixes.  Their roots must consequently be
  transported between bridge contexts built from different bases.

  This module isolates the structural fact needed for that transport.  An
  inclusion between the two bases lifts through the four identical bridge
  heads.  Atomic adequacy of the target bridge supplies binder readiness,
  so the complete represented weakening theorem transports an arbitrary
  (possibly nonstandard) local proof.  The direct body-context corollary
  adds the common universal-soundness assumption with the binder-ready cons
  lemma; it does not require that temporary head to be independently
  adequate.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAtomicAdequacy
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAConsistencyShiftOrbit
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.

Module PABoundedRawCodedRestrictedPAConsistencyBridgeContextTransport.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.

(** Adding the same temporary assumption preserves all four inputs of the
    binder-safe weakening theorem.  Factoring this one-head adapter avoids
    rebuilding its inclusion and readiness arguments at every logical
    shell. *)
Lemma raw_codedPALocalProof_contextInclusionWeakening_shared_head : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      source target head conclusion root,
  RawContextListRealizable M source ->
  RawContextListRealizable M target ->
  RawContextListIncluded M source target ->
  RawContextBinderReady M source target ->
  RawCodedPALocalProofOf M
    (rawListNode M head source) conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M head target) conclusion transportedRoot.
Proof.
  intros M hPA source target head conclusion root
    hsource htarget hincluded hready hproof.
  apply (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
    M hPA
    (rawListNode M head source) (rawListNode M head target)
    conclusion root).
  - exact (raw_contextList_cons_realizable M hPA source head hsource).
  - exact (raw_contextList_cons_realizable M hPA target head htarget).
  - exact (raw_contextListIncluded_cons M hPA
      source target head head hsource htarget eq_refl hincluded).
  - exact (raw_contextBinderReady_cons M hPA
      source target head hsource htarget hready).
  - exact hproof.
Qed.

(** The canonical bridge prefix has the same literal heads for both bases.
    Its inclusion therefore needs only realizability and inclusion of the
    tails; it does not need a numeral-code trace or any formula semantics. *)
Lemma raw_coqRestrictedPAConsistencyBridgeContext_included : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      numeralCode sourceBase targetBase,
  RawContextListRealizable M sourceBase ->
  RawContextListRealizable M targetBase ->
  RawContextListIncluded M sourceBase targetBase ->
  RawContextListIncluded M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode sourceBase)
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode targetBase).
Proof.
  intros M hPA numeralCode sourceBase targetBase
    hsource htarget hincluded.
  unfold rawCoqRestrictedPAConsistencyBridgeContextCode,
    rawRestrictedPAFieldsContextCode,
    rawRestrictedPACanonicalShiftedProofContextCode,
    rawRestrictedPAShiftedProofContextCode.
  apply (raw_contextListIncluded_cons M hPA).
  - repeat apply (raw_contextList_cons_realizable M hPA).
    exact hsource.
  - repeat apply (raw_contextList_cons_realizable M hPA).
    exact htarget.
  - reflexivity.
  - apply (raw_contextListIncluded_cons M hPA).
    + repeat apply (raw_contextList_cons_realizable M hPA).
      exact hsource.
    + repeat apply (raw_contextList_cons_realizable M hPA).
      exact htarget.
    + reflexivity.
    + apply (raw_contextListIncluded_cons M hPA).
      * apply (raw_contextList_cons_realizable M hPA).
        exact hsource.
      * apply (raw_contextList_cons_realizable M hPA).
        exact htarget.
      * reflexivity.
      * exact (raw_contextListIncluded_cons M hPA
          sourceBase targetBase _ _ hsource htarget eq_refl hincluded).
Qed.

(** Every local derivation over the old bridge can be rebuilt over the new
    bridge.  Target atomic adequacy is the exact binder hypothesis: it is
    already available in the final staged construction from the represented
    three-shift orbit and projected-fields trace. *)
Theorem
    raw_codedPALocalProof_coqRestrictedPAConsistencyBridgeContext_transport
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      numeralCode sourceBase targetBase conclusion root,
  RawContextListRealizable M sourceBase ->
  RawContextListRealizable M targetBase ->
  RawContextListIncluded M sourceBase targetBase ->
  RawContextAllAtomicallyAdequate M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode targetBase) ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode sourceBase)
    conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode targetBase)
      conclusion transportedRoot.
Proof.
  intros M hPA numeralCode sourceBase targetBase conclusion root
    hsourceBase htargetBase hincluded htargetAdequate hproof.
  assert (hsourceBridge : RawContextListRealizable M
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode sourceBase)).
  {
    unfold rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    repeat apply (raw_contextList_cons_realizable M hPA).
    exact hsourceBase.
  }
  assert (htargetBridge : RawContextListRealizable M
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode targetBase)).
  {
    unfold rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    repeat apply (raw_contextList_cons_realizable M hPA).
    exact htargetBase.
  }
  pose proof
    (raw_coqRestrictedPAConsistencyBridgeContext_included
      M hPA numeralCode sourceBase targetBase
      hsourceBase htargetBase hincluded) as hbridgeIncluded.
  pose proof
    (raw_contextBinderReady_of_target_all_atomically_adequate
      M hPA
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode sourceBase)
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode targetBase)
      hbridgeIncluded htargetAdequate) as hbridgeReady.
  exact
    (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
      M hPA
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode sourceBase)
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode targetBase)
      conclusion root hsourceBridge htargetBridge
      hbridgeIncluded hbridgeReady hproof).
Qed.

(** The arithmetic shell works one common universal-soundness assumption
    deeper.  Binder readiness, rather than adequacy of that temporary head,
    is what makes this additional transport valid. *)
Corollary
    raw_codedPALocalProof_coqRestrictedPAConsistencyBridgeBodyDirectContext_transport
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      numeralCode sourceBase targetBase conclusion root,
  RawContextListRealizable M sourceBase ->
  RawContextListRealizable M targetBase ->
  RawContextListIncluded M sourceBase targetBase ->
  RawContextAllAtomicallyAdequate M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode targetBase) ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode sourceBase)
    conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode targetBase)
      conclusion transportedRoot.
Proof.
  intros M hPA inputs numeralCode sourceBase targetBase conclusion root
    hsourceBase htargetBase hincluded htargetAdequate hproof.
  assert (hsourceBridge : RawContextListRealizable M
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode sourceBase)).
  {
    unfold rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    repeat apply (raw_contextList_cons_realizable M hPA).
    exact hsourceBase.
  }
  assert (htargetBridge : RawContextListRealizable M
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode targetBase)).
  {
    unfold rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    repeat apply (raw_contextList_cons_realizable M hPA).
    exact htargetBase.
  }
  pose proof
    (raw_coqRestrictedPAConsistencyBridgeContext_included
      M hPA numeralCode sourceBase targetBase
      hsourceBase htargetBase hincluded) as hbridgeIncluded.
  pose proof
    (raw_contextBinderReady_of_target_all_atomically_adequate
      M hPA
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode sourceBase)
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode targetBase)
      hbridgeIncluded htargetAdequate) as hbridgeReady.
  unfold rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
    in hproof |- *.
  exact
    (raw_codedPALocalProof_contextInclusionWeakening_shared_head
      M hPA
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode sourceBase)
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode targetBase)
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      conclusion root hsourceBridge htargetBridge
      hbridgeIncluded hbridgeReady hproof).
Qed.

End PABoundedRawCodedRestrictedPAConsistencyBridgeContextTransport.
