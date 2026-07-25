(**
  The weakest sufficient form of coded-proof context transplant, and the
  split of the dynamic-soundness producer that it enables.

  General weakening — moving a coded derivation from a context [Gamma] into
  an arbitrary context containing it — is not needed by this development.
  The context the producer must reach is, by definition, exactly four
  [rawListNode] steps above the caller's witnessed PA-axiom base:

    fields :: afterProofShift :: afterWitnessShift :: assumptionShift :: base

  ([raw_restrictedPADynamicSoundnessTargetContext_cons_view] below proves
  this by [reflexivity]; it is a definitional fact about the canonical
  descent contexts, not an observation.)

  So the transplant obligation can be stated in its weakest form: extend a
  context by ONE head.  Iterating it four times covers the producer's shape.
  This matters because a single-cons transplant is the cheapest possible
  version of the model-internal proof-tree recursion — every node code in
  this formalism stores its own context, so even this form requires rebuilding
  the tree, but it needs no containment relation, no permutation, and no
  membership bookkeeping beyond the cons-extension facts already proved in
  [RawCodedContextStructure].

  The second definition below isolates what is then still missing: a coded
  derivation of the dynamic-soundness implication over the *bare* witnessed
  base, with no descent assumptions in scope.  Together the two premises give
  the producer, hence the requested PA theorem.

  Neither premise is established here.  Subsequent analysis sharpened this
  historical factorisation further: the unrestricted transplant is too broad
  for malformed carrier-valued heads, because binder rules must shift them,
  and the exact-context base proof is too rigid when a compiler needs to add a
  witnessed induction axiom.  The constructive replacements are
  [RawCodedPALocalProofContextInsertInduction] (guarded by atomic formula
  adequacy) and [RawCodedRestrictedPAConsistencyGrowingOpenCompiler].  The
  implications in this file remain valid, but these two legacy premises are
  not the interfaces future code should try to prove.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedProofAssumptionLeaf
  RawCodedPALocalProofExistential
  RawCodedPAProofImpICertificates
  CompactPAUniformProvability
  RawCodedRestrictedPAConsistencyShiftOrbit
  RawCodedRestrictedPAConsistencyShiftRealization
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPADynamicSoundnessComposition
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedRestrictedPADynamicSoundnessProducer.

Import ListNotations.

Module PABoundedRawCodedPALocalProofConsTransplant.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.
Import PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPADynamicSoundnessComposition.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedRestrictedPADynamicSoundnessProducer.

(** ** The transplant obligation

    One new assumption is pushed underneath a finished derivation.  The
    realizability hypothesis is the same side condition already required by
    [raw_codedPALocalProofOf_assumption]: it says the incoming context has an
    honest model-internal traversal, so that the rebuilt assumption leaves
    can be certified.  It is preserved by [raw_contextList_cons_realizable],
    which is why iterating the obligation costs nothing extra. *)
Definition RawCodedPALocalProofConsTransplant (M : RawPAModel) : Prop :=
  forall context head target proof : M,
    RawContextListRealizable M context ->
    RawCodedPALocalProofOf M context target proof ->
    exists transplanted : M,
      RawCodedPALocalProofOf M
        (rawListNode M head context) target transplanted.

Arguments RawCodedPALocalProofConsTransplant M : clear implicits.

Definition RawCodedPALocalProofConsTransplantInAllModels : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawCodedPALocalProofConsTransplant M.

(** The producer's target context is a four-step cons extension of the
    caller's witnessed PA-axiom base. *)
Lemma raw_restrictedPADynamicSoundnessTargetContext_cons_view : forall
    (M : RawPAModel) baseContext numeralCode,
  rawRestrictedPAFieldsContextCode M numeralCode
    (rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext numeralCode) =
  rawListNode M (rawRestrictedPAProofFieldsCode M numeralCode)
    (rawListNode M
      (rawRestrictedPAProofAfterProofIteratedShiftCode M numeralCode 1)
      (rawListNode M
        (rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 2)
        (rawListNode M
          (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 3)
          baseContext))).
Proof. reflexivity. Qed.

(** ** The base-relative obligation

    A coded PA derivation of the dynamic-soundness implication over the bare
    witnessed base, at a possibly nonstandard numeral code.  No descent
    assumption is in scope, so this is the context-free form of the remaining
    arithmetical content. *)
Definition RawRestrictedPADynamicSoundnessBaseProof
    (M : RawPAModel) : Prop :=
  forall (value numeralCode baseWitnessList baseContext : M),
    RawNumeralTermCodeAt M value numeralCode ->
    RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
    exists child : M,
      RawCodedPALocalProofOf M baseContext
        (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode)
        child.

Arguments RawRestrictedPADynamicSoundnessBaseProof M : clear implicits.

Definition RawRestrictedPADynamicSoundnessBaseProofInAllModels : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedPADynamicSoundnessBaseProof M.

(** Four transplant steps carry the base derivation into the exact context
    demanded by existential descent. *)
Theorem raw_restrictedPADynamicSoundnessProducer_of_baseProof_and_transplant
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofConsTransplant M ->
  RawRestrictedPADynamicSoundnessBaseProof M ->
  RawRestrictedPADynamicSoundnessProducer M.
Proof.
  intros M hPA htransplant hbase
    value numeralCode baseWitnessList baseContext hnumeral hwitness.
  destruct (hbase value numeralCode baseWitnessList baseContext
    hnumeral hwitness) as [child0 hchild0].
  assert (hrealizable0 : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      baseWitnessList baseContext hwitness).
  }
  set (assumptionShift :=
    rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 3).
  set (witnessShift :=
    rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 2).
  set (proofShift :=
    rawRestrictedPAProofAfterProofIteratedShiftCode M numeralCode 1).
  set (fields := rawRestrictedPAProofFieldsCode M numeralCode).
  destruct (htransplant baseContext assumptionShift
    (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode)
    child0 hrealizable0 hchild0) as [child1 hchild1].
  assert (hrealizable1 : RawContextListRealizable M
      (rawListNode M assumptionShift baseContext)).
  {
    exact (raw_contextList_cons_realizable M hPA
      baseContext assumptionShift hrealizable0).
  }
  destruct (htransplant (rawListNode M assumptionShift baseContext)
    witnessShift
    (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode)
    child1 hrealizable1 hchild1) as [child2 hchild2].
  assert (hrealizable2 : RawContextListRealizable M
      (rawListNode M witnessShift
        (rawListNode M assumptionShift baseContext))).
  {
    exact (raw_contextList_cons_realizable M hPA
      (rawListNode M assumptionShift baseContext)
      witnessShift hrealizable1).
  }
  destruct (htransplant
    (rawListNode M witnessShift
      (rawListNode M assumptionShift baseContext))
    proofShift
    (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode)
    child2 hrealizable2 hchild2) as [child3 hchild3].
  assert (hrealizable3 : RawContextListRealizable M
      (rawListNode M proofShift
        (rawListNode M witnessShift
          (rawListNode M assumptionShift baseContext)))).
  {
    exact (raw_contextList_cons_realizable M hPA
      (rawListNode M witnessShift
        (rawListNode M assumptionShift baseContext))
      proofShift hrealizable2).
  }
  destruct (htransplant
    (rawListNode M proofShift
      (rawListNode M witnessShift
        (rawListNode M assumptionShift baseContext)))
    fields
    (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode)
    child3 hrealizable3 hchild3) as [child4 hchild4].
  exists child4.
  exact hchild4.
Qed.

Corollary
    raw_restrictedPADynamicSoundnessProducerInAllModels_of_baseProof_and_transplant
    : RawCodedPALocalProofConsTransplantInAllModels ->
  RawRestrictedPADynamicSoundnessBaseProofInAllModels ->
  RawRestrictedPADynamicSoundnessProducerInAllModels.
Proof.
  intros htransplant hbase M hPA.
  exact
    (raw_restrictedPADynamicSoundnessProducer_of_baseProof_and_transplant
      M hPA (htransplant M hPA) (hbase M hPA)).
Qed.

(** The historical two-premise implication.  Both premises are stronger than
    the guarded/growing interfaces used by the current construction plan; the
    theorem is retained because the implication itself is valid. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_baseProof_and_transplant
    : RawCodedPALocalProofConsTransplantInAllModels ->
  RawRestrictedPADynamicSoundnessBaseProofInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intros htransplant hbase.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dynamicSoundnessProducer.
  exact
    (raw_restrictedPADynamicSoundnessProducerInAllModels_of_baseProof_and_transplant
      htransplant hbase).
Qed.

(** ** The one context-inspecting constructor case

    [RawProofEndpointCases] has seventeen constructor rows.  Exactly one row —
    the assumption leaf, tag [0] — directly tests context membership.  The
    other rows are structural, but binder rules do more than carry the context:
    All-I and Ex-E require a pointwise shifted context, while Imp-I, Or-E, and
    Ex-E introduce local assumptions and therefore change insertion depth.

    That case is discharged here outright.  Membership survives a cons
    extension ([raw_contextList_cons_tail_member]), so the rebuilt leaf is an
    honest covered proof over the extended context.  The guarded arbitrary-
    depth version now appears in
    [raw_codedPALocalProof_contextInsert_assumption]; the remaining work is the
    constructor-local rebuilding step described in the newer induction
    module. *)
Theorem raw_codedPALocalProofOf_consTransplant_assumptionLeaf : forall
    (M : RawPAModel), RawPASatisfies M -> forall context head target,
  RawContextListMember M context target ->
  RawCodedPALocalProofOf M
    (rawListNode M head context) target
    (rawProofAssumptionRoot M (rawListNode M head context) target).
Proof.
  intros M hPA context head target hmember.
  split.
  - exact (raw_proofAssumption_ruleCoverage M hPA
      (rawListNode M head context) target
      (raw_contextList_cons_tail_member M hPA
        context head target hmember)).
  - exact (raw_proofAssumption_endpoint M
      (rawListNode M head context) target).
Qed.

(** The same statement in transplant form: an assumption leaf over [context]
    is transplanted by rebuilding it over the extended context. *)
Corollary raw_codedPALocalProofOf_consTransplant_of_member : forall
    (M : RawPAModel), RawPASatisfies M -> forall context head target,
  RawContextListMember M context target ->
  exists transplanted : M,
    RawCodedPALocalProofOf M
      (rawListNode M head context) target transplanted.
Proof.
  intros M hPA context head target hmember.
  exists (rawProofAssumptionRoot M (rawListNode M head context) target).
  exact (raw_codedPALocalProofOf_consTransplant_assumptionLeaf
    M hPA context head target hmember).
Qed.

(** ** Design notes for the remaining transplant recursion

    These three findings were established by inspection of the definitions
    named below.  They are recorded here because they determine the shape of
    the development that discharges
    [RawCodedPALocalProofConsTransplant], and that reasoning should not live
    only outside the repository.

    *** 1. The support certificate does not transport.

    It is tempting to hope that a transplanted tree can reuse the support
    certificate of the original, since it has the same shape and the same
    node tags and only the stored context changes.  It cannot.
    [RawProofRuleCoverageWithSupport] carries a pair [(supportCode,
    supportStep)] whose supported set is a beta-coded set of *node code
    values* — [rawProofCodeSupported M supportCode supportStep code] — and it
    additionally bounds them by [rawLt M code (raw_succ M root)].  Every node
    code is [rawListCode M [tag; context; ...]], so changing the stored
    context changes every node's code value and the root bound with it.  The
    old table therefore certifies a set of values that the new tree does not
    contain, and re-indexing it into the new set is precisely the transplant
    map one is trying to build.

    The consequence is a change of design rather than an obstruction: the
    recursion should *re-derive* coverage bottom up instead of transporting
    it.  Every constructor-level coverage lemma already builds a parent's
    support from its children's — see [raw_proofAssumption_ruleCoverage],
    [raw_proofExE_ruleCoverage], [raw_proofAllE_ruleCoverage], and the
    [raw_codedPALocalProofOf_*] combinators, each of which consumes children's
    [RawCodedPALocalProofOf] and produces the parent's.  So rebuilding the
    certificate for the transplanted tree costs no more than building one for
    any tree assembled from the constructors.

    *** 2. The root-only obligation needs a represented insertion depth.

    [RawCodedPALocalProofConsTransplant] inserts the new assumption at the
    *head* of the context.  That is the correct statement at the root, but it
    is not preserved by descent.  Under an [RP_impI] node with context
    [Gamma] the child's context is [a :: Gamma], and transplanting the parent
    from [Gamma] to [head :: Gamma] requires the child to move from
    [a :: Gamma] to [a :: head :: Gamma] — an insertion one layer down.  The
    induction hypothesis must therefore be indexed by the number of locally
    introduced assumptions.

    Crucially that index is a *model element*, not a metatheoretic natural
    number: a nonstandard proof code may have nonstandard depth.  So the
    relation "target is source with [head] inserted below [depth] layers" is a
    represented graph, in the style of [RawContextShift].
    [RawCodedContextInsert] now supplies it, and
    [RawCodedPALocalProofContextInsertInduction] represents the strong
    below-proof-code invariant and applies PA induction.  Its honest statement
    guards [head] by atomic formula adequacy, because binder descent must shift
    it.  The remaining context theorem is the insertion/shift commuting square.

    *** 3. Closing the loop wants a growing witnessed base.

    [RawRestrictedPADynamicSoundnessBaseProof] is stated over the *caller's*
    [baseContext].  The first derivability condition
    ([raw_codedPAProofOf_of_BProv], used through the internalization engine
    in [RawCodedPAInternalizedUniversalInstance]) produces its derivation in
    a witnessed context of its own choosing, and cons transplant moves proofs
    up from [baseContext] rather than across from an unrelated context.  So
    D1 does not plug into the base obligation directly.

    The current safe interface is
    [RawRestrictedPAConsistencyGrowingOpenContradictionCompiler]: it may return
    an enlarged witnessed PA base and feeds the certificate successor directly.
    The preferred final construction mirrors Lean's six-field master package,
    retaining the reusable dynamic-truth laws and forcing bounded consistency
    into the final coordinate.  This avoids trying to prove the exact-context
    [RawRestrictedPADynamicSoundnessBaseProof] premise above. *)

End PABoundedRawCodedPALocalProofConsTransplant.
