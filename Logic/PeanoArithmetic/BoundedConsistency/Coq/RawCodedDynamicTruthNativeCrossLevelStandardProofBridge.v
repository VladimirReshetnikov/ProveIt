(**
  Package the externally indexed cross-level proof theorem as an explicit
  standard-carrier bridge.

  The native cross-level graph is indexed by an arbitrary element of a raw PA
  model.  Its object-proof compiler therefore remains a genuinely open
  nonstandard construction.  The fixed-level development, however, already
  proves a PA proof for every *metatheoretic* predecessor [p].  This module
  gives that fact a small, reusable interface instead of repeating the long
  six-argument code expression at each future standard-syntax adapter.

  The bridge is deliberately honest: its trace interface includes an
  explicit equality between the selected field code and the canonical
  standard-level code.  We do not infer that equality from semantic graph
  satisfaction, and we do not claim an arbitrary-carrier compiler.  A later
  standard-trace normalization theorem can discharge the equality while this
  module supplies the proof certificate itself.
*)

From Stdlib Require Import Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
    RawCodedFixedLevelTruthTraversal
    RawCodedFixedLevelTruthTotality
    RawCodedFixedLevelTruthCoherence
    RawCodedFixedLevelTruthAdmissibleCoherence
    RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
    RawCodedDynamicTruthNativeCrossLevelPositiveGraph.

Module PABoundedRawCodedDynamicTruthNativeCrossLevelStandardProofBridge.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthCoherence.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.

(** The carrier value obtained by instantiating the native field polynomial
    with the six quoted fixed-level ingredients at levels [S p] and
    [S (S p)].  Keeping this definition named is important: downstream
    dependent proof interfaces can rewrite by one short identifier rather
    than unfolding the large constructor polynomial. *)
Definition rawDynamicTruthNativeCrossLevelStandardFieldCode
    (M : RawPAModel) (predecessor : nat) : M :=
  rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
    (rawQuotedFormulaCode M
      (fixedLevelSigmaDomainTermAt (S predecessor) (tVar 2)))
    (rawQuotedFormulaCode M
      (fixedLevelPiDomainTermAt (S predecessor) (tVar 2)))
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
        (tVar 2) (tVar 1) (tVar 0)))
    (rawQuotedFormulaCode M
      (fixedLevelPiFalsityCertificateTermAt (S predecessor)
        (tVar 2) (tVar 1) (tVar 0)))
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt (S (S predecessor))
        (tVar 2) (tVar 1) (tVar 0)))
    (rawQuotedFormulaCode M
      (fixedLevelPiFalsityCertificateTermAt (S (S predecessor))
        (tVar 2) (tVar 1) (tVar 0))).

Arguments rawDynamicTruthNativeCrossLevelStandardFieldCode M predecessor
  : clear implicits.

(** The named carrier code is not merely semantically related to the fixed
    source: PA proves the exact code equality.  Keeping this rewrite as a
    theorem makes standard-trace adapters independent of the large six-field
    expression above. *)
Theorem
    raw_dynamicTruthNativeCrossLevelStandardFieldCode_eq_quoted_fixedLevel_coherence
    : forall (M : RawPAModel), RawPASatisfies M -> forall predecessor,
  rawDynamicTruthNativeCrossLevelStandardFieldCode M predecessor =
  rawQuotedFormulaCode M
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula (S predecessor)).
Proof.
  intros M hPA predecessor.
  unfold rawDynamicTruthNativeCrossLevelStandardFieldCode.
  exact (rawDynamicTruthNativeCrossLevelCoherenceFieldCode_quoted_successor_levels
    M hPA predecessor).
Qed.

(** A proof-producing standard-level package.  This is a Prop-valued
    compiler, not a function selecting a unique certificate; the raw PA
    proof predicate need not be functional. *)
Definition RawDynamicTruthNativeCrossLevelStandardFieldProofCompiler
    (M : RawPAModel) : Prop :=
  forall predecessor : nat,
    exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthNativeCrossLevelStandardFieldCode M predecessor)
        certificate.

Arguments RawDynamicTruthNativeCrossLevelStandardFieldProofCompiler M
  : clear implicits.

Theorem
    raw_dynamicTruthNativeCrossLevelStandardFieldProofCompiler_of_PA :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelStandardFieldProofCompiler M.
Proof.
  intros M hPA predecessor.
  unfold rawDynamicTruthNativeCrossLevelStandardFieldCode.
  exact (rawDynamicTruthNativeCrossLevelCoherenceFieldCode_standard_proof
    M hPA predecessor).
Qed.

(** A canonical-output relation for a standard predecessor.  The equality
    is kept as data because graph traces are relational; a semantic trace
    alone does not provide an object-level proof of this code identity. *)
Definition RawDynamicTruthNativeCrossLevelStandardCanonicalOutputAt
    (M : RawPAModel) (predecessor : nat) (fieldCode : M) : Prop :=
  fieldCode = rawDynamicTruthNativeCrossLevelStandardFieldCode M predecessor.

Arguments RawDynamicTruthNativeCrossLevelStandardCanonicalOutputAt
  M predecessor fieldCode : clear implicits.

(** This adapter is the form consumed by a future standard-trace
    normalization theorem: once it identifies a transform output with the
    canonical code, the fixed-level PA proof is transported by rewriting. *)
Definition RawDynamicTruthNativeCrossLevelStandardCanonicalOutputProofCompiler
    (M : RawPAModel) : Prop :=
  forall predecessor fieldCode,
    RawDynamicTruthNativeCrossLevelStandardCanonicalOutputAt
      M predecessor fieldCode ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.

Arguments
  RawDynamicTruthNativeCrossLevelStandardCanonicalOutputProofCompiler M
  : clear implicits.

Theorem
    raw_dynamicTruthNativeCrossLevelStandardCanonicalOutputProofCompiler_of_PA :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelStandardCanonicalOutputProofCompiler M.
Proof.
  intros M hPA predecessor fieldCode hfield.
  subst fieldCode.
  exact (raw_dynamicTruthNativeCrossLevelStandardFieldProofCompiler_of_PA
    M hPA predecessor).
Qed.

(** Exact standard-indexed counterpart of the open native compiler seam.
    The orbit and transform hypotheses are retained in the interface so a
    caller can pass this compiler to the same dependency-ordered shell used
    for arbitrary carrier predecessors.  The canonical-output equality is
    explicit: semantic graph satisfaction alone does not identify an output
    with the standard fixed-level code. *)
Definition
    RawDynamicTruthNativeCrossLevelStandardCoherenceProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessor
      currentGlobalSigma currentGlobalPi fieldCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M tail
      (raw_succ M (rawNumeralValue M predecessor))
      currentGlobalSigma currentGlobalPi ->
    RawDynamicTruthNativeCrossLevelFieldTransformAt M
      currentGlobalSigma currentGlobalPi
      (rawNumeralValue M predecessor) fieldCode ->
    RawDynamicTruthNativeCrossLevelStandardCanonicalOutputAt
      M predecessor fieldCode ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeCrossLevelStandardCoherenceProofCompiler M
  : clear implicits.

Theorem
    raw_dynamicTruthNativeCrossLevelStandardCoherenceProofCompiler_of_PA :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelStandardCoherenceProofCompiler M.
Proof.
  intros M hPA tail predecessor currentGlobalSigma currentGlobalPi fieldCode
    _horbit _htransform hcanonical.
  exact
    (raw_dynamicTruthNativeCrossLevelStandardCanonicalOutputProofCompiler_of_PA
      M hPA predecessor fieldCode hcanonical).
Qed.

(** The full transform trace can be retained alongside the canonical-output
    equality.  This named relation is intentionally only standard-indexed;
    it is the precise input expected when the remaining fixed-level bridge is
    assembled with the positive graph. *)
Definition RawDynamicTruthNativeCrossLevelStandardCarrierTraceAt
    (M : RawPAModel) (tail : nat -> M) (predecessor : nat)
    (currentGlobalSigma currentGlobalPi fieldCode : M) : Prop :=
  RawDynamicTruthNativeCrossLevelFieldTransformAt M
    currentGlobalSigma currentGlobalPi
    (rawNumeralValue M predecessor) fieldCode /\
  RawDynamicTruthNativeCrossLevelStandardCanonicalOutputAt
    M predecessor fieldCode.

Arguments RawDynamicTruthNativeCrossLevelStandardCarrierTraceAt
  M tail predecessor currentGlobalSigma currentGlobalPi fieldCode
  : clear implicits.

Theorem
    raw_dynamicTruthNativeCrossLevelStandardCarrierTraceAt_proof_of_PA :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (tail : nat -> M) predecessor
    currentGlobalSigma currentGlobalPi fieldCode,
  RawDynamicTruthNativeCrossLevelStandardCarrierTraceAt M tail predecessor
    currentGlobalSigma currentGlobalPi fieldCode ->
  exists certificate : M,
    RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA tail predecessor currentGlobalSigma currentGlobalPi fieldCode
    [_ hfield].
  exact (raw_dynamicTruthNativeCrossLevelStandardCanonicalOutputProofCompiler_of_PA
    M hPA predecessor fieldCode hfield).
Qed.

End PABoundedRawCodedDynamicTruthNativeCrossLevelStandardProofBridge.
