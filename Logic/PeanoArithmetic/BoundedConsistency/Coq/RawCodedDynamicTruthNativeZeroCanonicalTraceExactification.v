(**
  Exact rank-zero applications of the canonical first global successor.

  The first global successor was already fixed to standard quotations by
  [RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation].  This
  module isolates and exactifies the two applications of that first
  successor.  They are the global traversal formulas that must next be
  compared semantically with the fixed level-one evidence formulas needed by
  the predecessor callback.  Keeping the argument separate from the large
  callback module makes the syntax bridge reusable by any future rank-zero
  consumer.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardRealization
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacy
  RawCodedProofAtomicAdequacyStandard
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeDecision
  RawCodedTernaryPredicateRootClosure
  RawCodedTemplateTernaryApplication
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalTernaryApplicationAlignment
  RawCodedDynamicTruthNativeLocalPositiveExactification
  RawCodedDynamicTruthPairedGlobalStandardSuccessor
  RawCodedDynamicTruthPairedGlobalOrbitFunctionality
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeDecision.
Import PABoundedRawCodedTernaryPredicateRootClosure.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalTernaryApplicationAlignment.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveExactification.
Import PABoundedRawCodedDynamicTruthPairedGlobalStandardSuccessor.
Import PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.

(** The first-successor predicates have exactly three free argument slots.
    The boolean scope decision is used here as a compact audit of the large
    concrete syntax tree. *)
Lemma dynamicTruthZeroInputGlobalSigmaFormula_scoped :
  StandardFormulaScoped 3 dynamicTruthZeroInputGlobalSigmaFormula.
Proof.
  apply (proj1 (standardFormulaScopedb_spec 3 _)).
  vm_compute. reflexivity.
Qed.

Lemma dynamicTruthZeroInputGlobalPiFormula_scoped :
  StandardFormulaScoped 3 dynamicTruthZeroInputGlobalPiFormula.
Proof.
  apply (proj1 (standardFormulaScopedb_spec 3 _)).
  vm_compute. reflexivity.
Qed.

(** These concrete scope facts discharge the complete carrier-facing root
    closure interface, including substitutions by nonstandard represented
    terms.  No trace-side adequacy premise is required. *)
Theorem raw_dynamicTruthZeroInputGlobalSigma_root_closed : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTernaryPredicateRootClosed M
    (rawQuotedFormulaCode M dynamicTruthZeroInputGlobalSigmaFormula).
Proof.
  intros M hPA.
  exact (raw_quotedFormula_ternaryPredicateRootClosed M hPA
    dynamicTruthZeroInputGlobalSigmaFormula
    dynamicTruthZeroInputGlobalSigmaFormula_scoped).
Qed.

Theorem raw_dynamicTruthZeroInputGlobalPi_root_closed : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTernaryPredicateRootClosed M
    (rawQuotedFormulaCode M dynamicTruthZeroInputGlobalPiFormula).
Proof.
  intros M hPA.
  exact (raw_quotedFormula_ternaryPredicateRootClosed M hPA
    dynamicTruthZeroInputGlobalPiFormula
    dynamicTruthZeroInputGlobalPiFormula_scoped).
Qed.

(** Applying the literal first-successor predicates in the local three-
    argument layout produces these canonical traversal formulas.  They are
    intentionally named separately from the fixed certificates: the global
    construction reorders ten existential witnesses, so the two views are
    semantically equivalent rather than definitionally equal. *)
Definition dynamicTruthZeroInputGlobalSigmaApplicationFormula : formula :=
  standardTernaryApplication dynamicTruthZeroInputGlobalSigmaFormula
    (tVar 2) (tVar 1) (tVar 0).

Definition dynamicTruthZeroInputGlobalPiApplicationFormula : formula :=
  standardTernaryApplication dynamicTruthZeroInputGlobalPiFormula
    (tVar 2) (tVar 1) (tVar 0).

Lemma dynamicTruthZeroInputGlobalSigmaApplicationFormula_scoped :
  StandardFormulaScoped 3
    dynamicTruthZeroInputGlobalSigmaApplicationFormula.
Proof.
  apply (proj1 (standardFormulaScopedb_spec 3 _)).
  vm_compute. reflexivity.
Qed.

Lemma dynamicTruthZeroInputGlobalPiApplicationFormula_scoped :
  StandardFormulaScoped 3
    dynamicTruthZeroInputGlobalPiApplicationFormula.
Proof.
  apply (proj1 (standardFormulaScopedb_spec 3 _)).
  vm_compute. reflexivity.
Qed.

(** Standard quotation realizes the exact five-operation application trace
    consumed by the native local compiler. *)
Theorem raw_dynamicTruthZeroInputGlobalSigma_application_standard : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthLocalTernaryApplication M
    (rawQuotedFormulaCode M dynamicTruthZeroInputGlobalSigmaFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula).
Proof.
  intros M hPA.
  apply (proj2
    (raw_dynamicTruthLocalTernaryApplication_ternary_iff M hPA
      (rawQuotedFormulaCode M dynamicTruthZeroInputGlobalSigmaFormula)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula))).
  unfold dynamicTruthZeroInputGlobalSigmaApplicationFormula.
  exact (raw_codedTernaryApplication_standard M hPA
    dynamicTruthZeroInputGlobalSigmaFormula
    (tVar 2) (tVar 1) (tVar 0)).
Qed.

Theorem raw_dynamicTruthZeroInputGlobalPi_application_standard : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthLocalTernaryApplication M
    (rawQuotedFormulaCode M dynamicTruthZeroInputGlobalPiFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA.
  apply (proj2
    (raw_dynamicTruthLocalTernaryApplication_ternary_iff M hPA
      (rawQuotedFormulaCode M dynamicTruthZeroInputGlobalPiFormula)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula))).
  unfold dynamicTruthZeroInputGlobalPiApplicationFormula.
  exact (raw_codedTernaryApplication_standard M hPA
    dynamicTruthZeroInputGlobalPiFormula
    (tVar 2) (tVar 1) (tVar 0)).
Qed.

(** Functionality upgrades any carrier-level applications of the canonical
    first successor to literal quotation equalities.  This is the precise
    handoff needed by a proof-producing global-row traversal: it may choose
    its own operation witnesses without creating another output parameter. *)
Theorem raw_dynamicTruthZeroInputGlobal_applications_exact : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaApplication piApplication,
  RawDynamicTruthLocalTernaryApplication M
    (rawQuotedFormulaCode M dynamicTruthZeroInputGlobalSigmaFormula)
    sigmaApplication ->
  RawDynamicTruthLocalTernaryApplication M
    (rawQuotedFormulaCode M dynamicTruthZeroInputGlobalPiFormula)
    piApplication ->
  sigmaApplication = rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula /\
  piApplication = rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula.
Proof.
  intros M hPA sigmaApplication piApplication hsigma hpi.
  split.
  - exact (raw_dynamicTruthLocalTernaryApplication_functional M hPA
      (rawQuotedFormulaCode M dynamicTruthZeroInputGlobalSigmaFormula)
      sigmaApplication
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      hsigma
      (raw_dynamicTruthZeroInputGlobalSigma_application_standard M hPA)).
  - exact (raw_dynamicTruthLocalTernaryApplication_functional M hPA
      (rawQuotedFormulaCode M dynamicTruthZeroInputGlobalPiFormula)
      piApplication
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      hpi
      (raw_dynamicTruthZeroInputGlobalPi_application_standard M hPA)).
Qed.

(** Quotation also supplies atomic adequacy of the two normalized outputs;
    downstream proof transport can therefore use them as context heads. *)
Corollary
    raw_dynamicTruthZeroInputGlobalSigmaApplication_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaAtomicallyAdequate M
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula).
Proof.
  intros M hPA.
  exact (raw_quotedFormula_atomically_adequate M hPA
    dynamicTruthZeroInputGlobalSigmaApplicationFormula).
Qed.

Corollary
    raw_dynamicTruthZeroInputGlobalPiApplication_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaAtomicallyAdequate M
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA.
  exact (raw_quotedFormula_atomically_adequate M hPA
    dynamicTruthZeroInputGlobalPiApplicationFormula).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.
