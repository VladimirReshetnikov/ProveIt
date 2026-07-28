(**
  Reusable proof transport through adjoined witnessed and open contexts.

  Two context extensions recur in the bounded-consistency compilers:

  - the same represented PA induction axiom is adjoined to two witnessed
    bases related by literal membership inclusion; and
  - a temporary, closed formula is prepended to an already witnessed tail.

  Proof nodes store their context literally, so neither operation follows
  from ordinary metatheoretic weakening.  This file packages the checked
  carrier-level transformations.  The induction extension uses completed
  witnessed-context inclusion weakening.  The open-head extension uses an
  explicit formula-shift edge to build the exact binder-readiness square;
  the temporary head is never mislabeled as a PA axiom.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitness
  RawCodedPALocalProofExistential
  RawCodedPAInductionAxiomCertificate
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete.

Module PABoundedRawCodedPALocalProofAdjoinedContextTransport.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.

(** Literal base inclusion is preserved when the same induction-axiom code
    is prepended to both witnessed contexts.  Witnessing is used here only
    to obtain the two honest list traversals required by cons inclusion. *)
Theorem raw_contextListIncluded_same_induction_extension : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      oldWitnessList oldContext newWitnessList newContext axiom,
  RawCodedPAAxiomWitnessContext M oldWitnessList oldContext ->
  RawCodedPAAxiomWitnessContext M newWitnessList newContext ->
  RawContextListIncluded M oldContext newContext ->
  RawContextListIncluded M
    (rawPAInductionExtendedContext M oldContext axiom)
    (rawPAInductionExtendedContext M newContext axiom).
Proof.
  intros M hPA oldWitnessList oldContext
    newWitnessList newContext axiom hold hnew hincluded.
  unfold rawPAInductionExtendedContext.
  exact (raw_contextListIncluded_cons M hPA
    oldContext newContext axiom axiom
    (raw_codedPAAxiomWitnessContext_context_realizable
      M oldWitnessList oldContext hold)
    (raw_codedPAAxiomWitnessContext_context_realizable
      M newWitnessList newContext hnew)
    eq_refl hincluded).
Qed.

(** Checked weakening through the same represented induction axiom.  Both
    extended contexts remain witnessed PA contexts, so the completed
    binder-safe witnessed-context transformer applies directly. *)
Theorem raw_codedPALocalProof_same_induction_extension_weakening : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      oldWitnessList oldContext newWitnessList newContext
      inductionSource axiom conclusion root,
  RawCodedPAAxiomWitnessContext M oldWitnessList oldContext ->
  RawCodedPAAxiomWitnessContext M newWitnessList newContext ->
  RawCodedPAAxiomInduction M inductionSource axiom ->
  RawContextListIncluded M oldContext newContext ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M oldContext axiom)
    conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M
      (rawPAInductionExtendedContext M newContext axiom)
      conclusion transportedRoot.
Proof.
  intros M hPA oldWitnessList oldContext newWitnessList newContext
    inductionSource axiom conclusion root
    hold hnew hinduction hincluded hproof.
  pose proof (raw_codedPAAxiomWitnessContext_add_induction M hPA
    oldWitnessList oldContext inductionSource axiom
    hold hinduction) as holdExtended.
  pose proof (raw_codedPAAxiomWitnessContext_add_induction M hPA
    newWitnessList newContext inductionSource axiom
    hnew hinduction) as hnewExtended.
  exact
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawPAInductionExtendedWitnessList M
        oldWitnessList inductionSource)
      (rawPAInductionExtendedContext M oldContext axiom)
      (rawPAInductionExtendedWitnessList M
        newWitnessList inductionSource)
      (rawPAInductionExtendedContext M newContext axiom)
      conclusion root holdExtended hnewExtended
      (raw_contextListIncluded_same_induction_extension M hPA
        oldWitnessList oldContext newWitnessList newContext axiom
        hold hnew hincluded)
      hproof).
Qed.

(** An explicit unit shift of the new head builds binder readiness from a
    context to its one-head extension.  Given any source shift selected by a
    binder rule, prepend the supplied head image to that same shifted tail.
    Membership inclusion is then just inclusion into a cons target. *)
Theorem raw_contextBinderReady_prepend_target_of_formulaShift : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context head shiftedHead,
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1) head shiftedHead ->
  RawContextBinderReady M context (rawListNode M head context).
Proof.
  intros M hPA context head shiftedHead hheadShift
    shiftedContext hcontextShift.
  exists (rawListNode M shiftedHead shiftedContext).
  split.
  - exact (raw_contextShift_cons M hPA
      context shiftedContext head shiftedHead
      hcontextShift hheadShift).
  - exact (raw_contextListIncluded_cons_target M hPA
      shiftedContext shiftedContext shiftedHead
      (raw_contextListIncluded_refl M shiftedContext)).
Qed.

(** Prepend one open-context head to an existing local proof.  Unlike a
    generic adequacy-based insertion, this endpoint exposes the actual head
    shift used below binders and feeds it to the binder-ready weakening
    theorem. *)
Theorem raw_codedPALocalProof_prepend_context_of_formulaShift : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context head shiftedHead conclusion root,
  RawContextListRealizable M context ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1) head shiftedHead ->
  RawCodedPALocalProofOf M context conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M head context) conclusion transportedRoot.
Proof.
  intros M hPA context head shiftedHead conclusion root
    hcontext hheadShift hproof.
  apply (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
    M hPA context (rawListNode M head context) conclusion root).
  - exact hcontext.
  - exact (raw_contextList_cons_realizable M hPA
      context head hcontext).
  - exact (raw_contextListIncluded_cons_target M hPA
      context context head
      (raw_contextListIncluded_refl M context)).
  - exact (raw_contextBinderReady_prepend_target_of_formulaShift
      M hPA context head shiftedHead hheadShift).
  - exact hproof.
Qed.

(** Closed heads are the principal client: their unit shift has the same
    source and target code. *)
Corollary raw_codedPALocalProof_prepend_closed_context : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context head conclusion root,
  RawContextListRealizable M context ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1) head head ->
  RawCodedPALocalProofOf M context conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M head context) conclusion transportedRoot.
Proof.
  intros M hPA context head conclusion root
    hcontext hheadShift hproof.
  exact (raw_codedPALocalProof_prepend_context_of_formulaShift
    M hPA context head head conclusion root
    hcontext hheadShift hproof).
Qed.

(** If a proof is already below a common temporary head, witnessed-tail
    inclusion can also be lifted through that head.  Binder readiness for
    the witnessed tails is preserved by adding the same local assumption;
    no independent adequacy claim about the head is needed. *)
Theorem
    raw_codedPALocalProof_same_prepend_weakening_between_witnessed_tails
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      oldWitnessList oldContext newWitnessList newContext
      head conclusion root,
  RawCodedPAAxiomWitnessContext M oldWitnessList oldContext ->
  RawCodedPAAxiomWitnessContext M newWitnessList newContext ->
  RawContextListIncluded M oldContext newContext ->
  RawCodedPALocalProofOf M
    (rawListNode M head oldContext) conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M head newContext) conclusion transportedRoot.
Proof.
  intros M hPA oldWitnessList oldContext newWitnessList newContext
    head conclusion root hold hnew hincluded hproof.
  pose proof (raw_codedPAAxiomWitnessContext_context_realizable
    M oldWitnessList oldContext hold) as holdRealizable.
  pose proof (raw_codedPAAxiomWitnessContext_context_realizable
    M newWitnessList newContext hnew) as hnewRealizable.
  apply (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
    M hPA
    (rawListNode M head oldContext)
    (rawListNode M head newContext)
    conclusion root).
  - exact (raw_contextList_cons_realizable M hPA
      oldContext head holdRealizable).
  - exact (raw_contextList_cons_realizable M hPA
      newContext head hnewRealizable).
  - exact (raw_contextListIncluded_cons M hPA
      oldContext newContext head head
      holdRealizable hnewRealizable eq_refl hincluded).
  - exact (raw_contextBinderReady_cons M hPA
      oldContext newContext head
      holdRealizable hnewRealizable
      (raw_contextBinderReady_witnessed_target M hPA
        oldContext newContext newWitnessList hincluded hnew)).
  - exact hproof.
Qed.

(** Combined endpoint used by growing compilers: first move a proof through
    the same induction axiom above an included witnessed base, then prepend
    a closed temporary head using its explicit self-shift certificate. *)
Theorem
    raw_codedPALocalProof_same_induction_extension_then_prepend_closed_context
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      oldWitnessList oldContext newWitnessList newContext
      inductionSource axiom head conclusion root,
  RawCodedPAAxiomWitnessContext M oldWitnessList oldContext ->
  RawCodedPAAxiomWitnessContext M newWitnessList newContext ->
  RawCodedPAAxiomInduction M inductionSource axiom ->
  RawContextListIncluded M oldContext newContext ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1) head head ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M oldContext axiom)
    conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M head
        (rawPAInductionExtendedContext M newContext axiom))
      conclusion transportedRoot.
Proof.
  intros M hPA oldWitnessList oldContext newWitnessList newContext
    inductionSource axiom head conclusion root
    hold hnew hinduction hincluded hheadShift hproof.
  destruct
    (raw_codedPALocalProof_same_induction_extension_weakening
      M hPA oldWitnessList oldContext newWitnessList newContext
      inductionSource axiom conclusion root
      hold hnew hinduction hincluded hproof)
    as [extendedRoot hextended].
  apply (raw_codedPALocalProof_prepend_closed_context M hPA
    (rawPAInductionExtendedContext M newContext axiom)
    head conclusion extendedRoot).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawPAInductionExtendedWitnessList M
        newWitnessList inductionSource)
      (rawPAInductionExtendedContext M newContext axiom)
      (raw_codedPAAxiomWitnessContext_add_induction M hPA
        newWitnessList newContext inductionSource axiom
        hnew hinduction)).
  - exact hheadShift.
  - exact hextended.
Qed.

End PABoundedRawCodedPALocalProofAdjoinedContextTransport.
