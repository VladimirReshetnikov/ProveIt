(**
  Proof compilation for the native dynamic PA-axiom-soundness field.

  The positive graph constructs the exact carrier polynomial

      All (Imp (And witnessed-axiom lower-admissible) next-Sigma).

  Its arbitrary-carrier object proof has two logically separate parts.  The
  outer implication and universal quantifier are ordinary raw proof
  constructors, and this file compiles them without any semantic-validity or
  completeness premise.  The only genuinely dynamic part is a local proof of
  [next-Sigma] while the transparent antecedent is the head assumption.

  [RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler] names precisely that
  remaining structural obligation.  It is indexed by the adequate orbit and
  the literal successor/substitution/application trace, but deliberately does
  not mention the final field code or an ordinary PA certificate.  Thus it is
  strictly below the proof compiler exposed by the positive graph rather than
  a restatement of that compiler.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedRestrictedProofStandardAdequacy
  RawCodedRestrictedPAProof
  RawCodedContextShift
  RawCodedProofEndpoints
  RawCodedProofRuleCoverage
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedProofImpIConstructor
  RawCodedProofAllIConstructor
  RawCodedPALocalProofPropositionalRules
  RawCodedDynamicTruthAxiomSoundnessBaseGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.

(** The literal antecedent used by the transparent carrier polynomial. *)
Definition rawDynamicTruthNativeAxiomSoundnessAntecedentCode
    (M : RawPAModel) (sigmaDomain piDomain : M) : M :=
  rawFormulaAndCode M
    (rawNumeralValue M
      (formulaCode
        (witnessedPAAxiomRecognitionTermAt (tVar 0))))
    (rawDynamicTruthNativeAxiomLowerAdmissibleCode M
      sigmaDomain piDomain).

Arguments rawDynamicTruthNativeAxiomSoundnessAntecedentCode
  M sigmaDomain piDomain : clear implicits.

Lemma rawDynamicTruthNativeAxiomSoundnessFieldCode_as_all_imp : forall
    (M : RawPAModel) sigmaDomain piDomain nextSigmaEvidence,
  rawDynamicTruthNativeAxiomSoundnessFieldCode M
      sigmaDomain piDomain nextSigmaEvidence =
    rawFormulaAllCode M
      (rawFormulaImpCode M
        (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
          sigmaDomain piDomain)
        nextSigmaEvidence).
Proof.
  reflexivity.
Qed.

(**
  The pointwise dynamic leaf obligation.  The base context is literally
  empty; the sole head is the carrier antecedent that [RP_impI] will later
  discharge.  Coverage and the endpoint are retained as proof syntax, not
  replaced by truth of the consequent in the ambient model.
*)
Definition RawDynamicTruthNativeAxiomSoundnessLocalRootAt
    (M : RawPAModel)
    (sigmaDomain piDomain nextSigmaEvidence : M) : Prop :=
  exists child : M,
    RawCodedPALocalProofOf M
      (rawListNode M
        (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
          sigmaDomain piDomain)
        (raw_zero M))
      nextSigmaEvidence child.

Arguments RawDynamicTruthNativeAxiomSoundnessLocalRootAt
  M sigmaDomain piDomain nextSigmaEvidence : clear implicits.

(**
  The exact structural trace needed by a local-root construction.  Compared
  with [RawDynamicTruthNativeAxiomSoundnessFieldTransformAt], this record has
  no output [fieldCode] and no final field-code equality.  The adequate orbit
  remains explicit because it is the syntactic invariant available to a
  future induction over a possibly nonstandard carrier predecessor.
*)
Definition RawDynamicTruthNativeAxiomSoundnessProofTraceAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence : M) : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
  exists currentLevel nextGlobalSigma nextGlobalPi currentLevelNumeral : M,
    currentLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      currentGlobalSigma currentGlobalPi currentLevel
      nextGlobalSigma nextGlobalPi /\
    RawNumeralTermCodeAt M currentLevel currentLevelNumeral /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthNativeAxiomPiDomainTemplate))
      piDomain /\
    RawDynamicTruthNativeAxiomApplication M
      nextGlobalSigma nextSigmaEvidence.

Arguments RawDynamicTruthNativeAxiomSoundnessProofTraceAt
  M tail predecessorLevel currentGlobalSigma currentGlobalPi
  sigmaDomain piDomain nextSigmaEvidence : clear implicits.

(**
  Smallest honest interface left by the existing library: turn the actual
  structural trace into the local proof root.  It neither asks for the final
  [All (Imp ...)] certificate nor assumes semantic validity/completeness.
*)
Definition RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence,
    RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence ->
    RawDynamicTruthNativeAxiomSoundnessLocalRootAt M
      sigmaDomain piDomain nextSigmaEvidence.

Arguments RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M
  : clear implicits.

(** The concrete certificate is [allI] above [impI] above the local root. *)
Definition rawDynamicTruthNativeAxiomSoundnessProofCertificate
    (M : RawPAModel)
    (sigmaDomain piDomain nextSigmaEvidence child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) (raw_zero M)
    (rawProofAllIRoot M (raw_zero M)
      (rawFormulaImpCode M
        (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
          sigmaDomain piDomain)
        nextSigmaEvidence)
      (rawProofImpIRoot M (raw_zero M)
        (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
          sigmaDomain piDomain)
        nextSigmaEvidence child)).

Arguments rawDynamicTruthNativeAxiomSoundnessProofCertificate
  M sigmaDomain piDomain nextSigmaEvidence child : clear implicits.

(** Empty witnessed PA contexts are reconstructed here from the standard
    adequacy theorem.  Keeping this two-line derivation local avoids relying
    on an unrelated higher-level leaf-certificate wrapper. *)
Lemma raw_dynamicTruthNativeAxiomSoundness_empty_witness_context : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPAAxiomWitnessContext M (raw_zero M) (raw_zero M).
Proof.
  intros M hPA.
  pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
  cbn [rawQuotedPAAxiomWitnessList rawQuotedContextCode
    rawListCode map] in h.
  exact h.
Qed.

(**
  All non-dynamic proof construction is now unconditional.  The empty
  context is fixed by context shift, so universal introduction needs no
  carrier-specific synchronization witness.  The proof below applies the
  low-level [RP_allI] coverage and endpoint constructors directly.
*)
Theorem
    raw_codedPAProofOf_dynamicTruthNativeAxiomSoundnessField_of_local_root :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain nextSigmaEvidence,
    RawDynamicTruthNativeAxiomSoundnessLocalRootAt M
      sigmaDomain piDomain nextSigmaEvidence ->
    exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthNativeAxiomSoundnessFieldCode M
          sigmaDomain piDomain nextSigmaEvidence)
        certificate.
Proof.
  intros M hPA sigmaDomain piDomain nextSigmaEvidence
    [child hlocal].
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (raw_zero M)
    (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain)
    nextSigmaEvidence child hlocal) as himp.
  destruct himp as [hcoverage hendpoint].
  exists (rawDynamicTruthNativeAxiomSoundnessProofCertificate M
    sigmaDomain piDomain nextSigmaEvidence child).
  rewrite rawDynamicTruthNativeAxiomSoundnessFieldCode_as_all_imp.
  unfold rawDynamicTruthNativeAxiomSoundnessProofCertificate.
  exists (raw_zero M),
    (rawProofAllIRoot M (raw_zero M)
      (rawFormulaImpCode M
        (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
          sigmaDomain piDomain)
        nextSigmaEvidence)
      (rawProofImpIRoot M (raw_zero M)
        (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
          sigmaDomain piDomain)
        nextSigmaEvidence child)),
    (raw_zero M).
  split; [reflexivity |].
  repeat split.
  - exact
      (raw_dynamicTruthNativeAxiomSoundness_empty_witness_context M hPA).
  - exact (raw_proofAllI_ruleCoverage M hPA
      (raw_zero M) (raw_zero M)
      (rawFormulaImpCode M
        (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
          sigmaDomain piDomain)
        nextSigmaEvidence)
      (rawProofImpIRoot M (raw_zero M)
        (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
          sigmaDomain piDomain)
        nextSigmaEvidence child)
      (raw_contextShift_empty M hPA) hcoverage hendpoint).
  - exact (raw_proofAllI_endpoint M (raw_zero M)
      (rawFormulaImpCode M
        (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
          sigmaDomain piDomain)
        nextSigmaEvidence)
      (rawProofImpIRoot M (raw_zero M)
        (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
          sigmaDomain piDomain)
        nextSigmaEvidence child)).
Qed.

(** Extract the proof-relevant trace from the graph transform, omitting only
    the already transparent final constructor equality. *)
Lemma raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_of_transform : forall
    (M : RawPAModel) (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode,
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail (raw_succ M predecessorLevel)
    currentGlobalSigma currentGlobalPi ->
  RawDynamicTruthNativeAxiomSoundnessFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
  exists sigmaDomain piDomain nextSigmaEvidence : M,
    fieldCode = rawDynamicTruthNativeAxiomSoundnessFieldCode M
      sigmaDomain piDomain nextSigmaEvidence /\
    RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence.
Proof.
  intros M tail predecessorLevel currentGlobalSigma currentGlobalPi
    fieldCode horbit
    (currentLevel & nextGlobalSigma & nextGlobalPi & currentLevelNumeral &
      sigmaDomain & piDomain & nextSigmaEvidence &
      hlevel & hsuccessor & hnumeral & hsigmaDomain & hpiDomain &
      hnextSigma & hfield).
  exists sigmaDomain, piDomain, nextSigmaEvidence.
  split; [exact hfield |].
  split; [exact horbit |].
  exists currentLevel, nextGlobalSigma, nextGlobalPi, currentLevelNumeral.
  repeat split; assumption.
Qed.

(**
  Reduction of the original arbitrary-carrier compiler to the local-root
  interface.  This theorem performs genuine proof-code construction: after
  the transform is destructed, [impI] discharges its exact antecedent and
  [allI] binds the axiom variable in the literal transparent field code.
*)
Theorem raw_dynamicTruthNativeAxiomSoundnessProofCompiler_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessProofCompiler M.
Proof.
  intros M hPA hlocal tail predecessorLevel
    currentGlobalSigma currentGlobalPi fieldCode horbit htransform.
  destruct
    (raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_of_transform
      M tail predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
      horbit htransform) as
    (sigmaDomain & piDomain & nextSigmaEvidence & hfield & htrace).
  rewrite hfield.
  exact
    (raw_codedPAProofOf_dynamicTruthNativeAxiomSoundnessField_of_local_root
      M hPA sigmaDomain piDomain nextSigmaEvidence
      (hlocal tail predecessorLevel currentGlobalSigma currentGlobalPi
        sigmaDomain piDomain nextSigmaEvidence htrace)).
Qed.

Corollary
    dynamicTruthNativeAxiomSoundnessPositiveGraph_raw_proof_total_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessPositiveProofTotal M.
Proof.
  intros M hPA hlocal.
  exact
    (dynamicTruthNativeAxiomSoundnessPositiveGraph_raw_proof_total_of_compiler
      M hPA
      (raw_dynamicTruthNativeAxiomSoundnessProofCompiler_of_local_roots
        M hPA hlocal)).
Qed.

End PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
