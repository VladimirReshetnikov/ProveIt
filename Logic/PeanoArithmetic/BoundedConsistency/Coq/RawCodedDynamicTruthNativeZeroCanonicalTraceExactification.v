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

From Stdlib Require Import Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
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
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
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
  RawCodedDynamicTruthGlobalBaseRootClosure
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalTernaryApplicationAlignment
  RawCodedDynamicTruthNativeLocalPositiveExactification
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthPairedGlobalStandardSuccessor
  RawCodedDynamicTruthPairedGlobalOrbitFunctionality
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

Import PA.
Import PAListRepresentability.
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
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
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
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalTernaryApplicationAlignment.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveExactification.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
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

(** At the first successor, each dynamically constructed local row is
    literally the corresponding native level-one witness row.  Only the
    recursively called rank-zero predicate is left abstract here; separating
    this syntactic fact keeps the later semantic replacement small. *)
Lemma dynamicTruthZeroSigmaSuccessorRow_native_shape :
  dynamicTruthSigmaSuccessorRowFormula (Term.numeral 1)
      dynamicTruthGlobalPiBaseFormula =
  fixedLevelEx8
    (fixedLevelSigmaSuccessorWitnessRowTermAt 0
      (Formula.rename dynamicTruthCoqLowerApplicationRenaming
        dynamicTruthGlobalPiBaseFormula)
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 10) (tVar 9) (tVar 8)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)).
Proof.
  vm_compute. reflexivity.
Qed.

Lemma dynamicTruthZeroPiSuccessorRow_native_shape :
  dynamicTruthPiSuccessorRowFormula (Term.numeral 1)
      dynamicTruthGlobalSigmaBaseFormula =
  fixedLevelEx8
    (fixedLevelPiSuccessorWitnessRowTermAt 0
      (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
        dynamicTruthGlobalSigmaBaseFormula)
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 10) (tVar 9) (tVar 8)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)).
Proof.
  vm_compute. reflexivity.
Qed.

(** Write the recursive rank-zero calls as honest ternary applications.
    In the eight-witness row layout these applications reduce to the
    specialized renamings used by the represented successor constructors. *)
Definition dynamicTruthZeroLowerSigmaApplication
    (root assignmentCode assignmentStep : term) : formula :=
  standardTernaryApplication dynamicTruthGlobalSigmaBaseFormula
    root assignmentCode assignmentStep.

Definition dynamicTruthZeroLowerPiApplication
    (root assignmentCode assignmentStep : term) : formula :=
  standardTernaryApplication dynamicTruthGlobalPiBaseFormula
    root assignmentCode assignmentStep.

Lemma dynamicTruthZeroLowerSigmaApplication_row_eq :
  dynamicTruthZeroLowerSigmaApplication
      (liftTerm 3 (tVar 6)) (tVar 1) (tVar 0) =
  Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
    dynamicTruthGlobalSigmaBaseFormula.
Proof.
  change (standardDynamicTruthPiCoqLowerApplication
      dynamicTruthGlobalSigmaBaseFormula =
    Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
      dynamicTruthGlobalSigmaBaseFormula).
  apply standardDynamicTruthPiCoqLowerApplication_eq_rename.
  exact dynamicTruthGlobalSigmaBaseFormula_scoped.
Qed.

Lemma dynamicTruthZeroLowerPiApplication_row_eq :
  dynamicTruthZeroLowerPiApplication
      (liftTerm 3 (tVar 6)) (tVar 1) (tVar 0) =
  Formula.rename dynamicTruthCoqLowerApplicationRenaming
    dynamicTruthGlobalPiBaseFormula.
Proof.
  change (standardDynamicTruthCoqLowerApplication
      dynamicTruthGlobalPiBaseFormula =
    Formula.rename dynamicTruthCoqLowerApplicationRenaming
      dynamicTruthGlobalPiBaseFormula).
  apply standardDynamicTruthCoqLowerApplication_eq_rename.
  exact dynamicTruthGlobalPiBaseFormula_scoped.
Qed.

(** Formula-level selected row, shared by both fixed canonical modes. *)
Definition dynamicTruthZeroClosedSuccessorRowFormula
    (mode : term) : formula :=
  pOr
    (pAnd (pEq mode tZero)
      (dynamicTruthSigmaSuccessorRowFormula (Term.numeral 1)
        dynamicTruthGlobalPiBaseFormula))
    (pAnd (pEq mode (Term.numeral 1))
      (dynamicTruthPiSuccessorRowFormula (Term.numeral 1)
        dynamicTruthGlobalSigmaBaseFormula)).

(** The complete selected-row disjunction used by the append compiler is
    exactly the native level-one closed-row constructor.  This packages the
    two polarity-specific shape lemmas and the two lower-application
    renamings into one rewrite at the abstraction level used by fixed-level
    truth traversal.  Before the eight row witnesses are opened, the current
    row index is [#4] (and becomes [#12] in the witness body); the selected
    mode is left abstract so the same lemma serves both canonical modes. *)
Lemma dynamicTruthZeroClosedSuccessorRow_native_shape : forall mode,
  dynamicTruthZeroClosedSuccessorRowFormula mode =
  fixedLevelClosedSuccessorRowTermAt 0
    dynamicTruthZeroLowerSigmaApplication
    dynamicTruthZeroLowerPiApplication
    (tVar 12) (tVar 11) (tVar 10) (tVar 9)
    (tVar 8) (tVar 7) (tVar 6) (tVar 5)
    (tVar 4) mode (tVar 2) (tVar 1) (tVar 0).
Proof.
  intro mode.
  unfold dynamicTruthZeroClosedSuccessorRowFormula.
  unfold fixedLevelClosedSuccessorRowTermAt.
  rewrite dynamicTruthZeroSigmaSuccessorRow_native_shape,
    dynamicTruthZeroPiSuccessorRow_native_shape.
  rewrite dynamicTruthZeroLowerPiApplication_row_eq,
    dynamicTruthZeroLowerSigmaApplication_row_eq.
  reflexivity.
Qed.

(** The lower applications inherit the exact native rank-zero meaning of
    the two global base predicates.  Stating this for arbitrary argument
    terms, rather than only the row variables above, makes it directly
    consumable by the generic successor-traversal semantics theorem. *)
Lemma raw_sat_dynamicTruthZeroLowerSigmaApplication_native_iff : forall
    (M : RawPAModel) e root assignmentCode assignmentStep,
  raw_formula_sat M e
      (dynamicTruthZeroLowerSigmaApplication
        root assignmentCode assignmentStep) <->
  raw_formula_sat M e
      (fixedLevelSigmaTruthCertificateTermAt 0
        root assignmentCode assignmentStep).
Proof.
  intros M e root assignmentCode assignmentStep.
  unfold dynamicTruthZeroLowerSigmaApplication.
  rewrite (standardTernaryApplication_eq_subst
    dynamicTruthGlobalSigmaBaseFormula root assignmentCode assignmentStep
    dynamicTruthGlobalSigmaBaseFormula_scoped).
  rewrite raw_formula_sat_subst.
  set (appliedEnvironment := fun index =>
    raw_term_eval M e
      (standardTernarySubstitution
        root assignmentCode assignmentStep index)).
  assert (henvironment : appliedEnvironment =
      scons M (raw_term_eval M e root)
        (scons M (raw_term_eval M e assignmentCode)
          (scons M (raw_term_eval M e assignmentStep) e))).
  {
    apply functional_extensionality. intro index.
    destruct index as [|[|[|tailIndex]]]; reflexivity.
  }
  change (raw_formula_sat M appliedEnvironment
      dynamicTruthGlobalSigmaBaseFormula <->
    raw_formula_sat M e
      (fixedLevelSigmaTruthCertificateTermAt 0
        root assignmentCode assignmentStep)).
  rewrite henvironment.
  rewrite raw_sat_dynamicTruthGlobalSigmaBaseFormula_native_iff.
  rewrite !raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_sat_dynamicTruthZeroLowerPiApplication_native_iff : forall
    (M : RawPAModel) e root assignmentCode assignmentStep,
  raw_formula_sat M e
      (dynamicTruthZeroLowerPiApplication
        root assignmentCode assignmentStep) <->
  raw_formula_sat M e
      (fixedLevelPiFalsityCertificateTermAt 0
        root assignmentCode assignmentStep).
Proof.
  intros M e root assignmentCode assignmentStep.
  unfold dynamicTruthZeroLowerPiApplication.
  rewrite (standardTernaryApplication_eq_subst
    dynamicTruthGlobalPiBaseFormula root assignmentCode assignmentStep
    dynamicTruthGlobalPiBaseFormula_scoped).
  rewrite raw_formula_sat_subst.
  set (appliedEnvironment := fun index =>
    raw_term_eval M e
      (standardTernarySubstitution
        root assignmentCode assignmentStep index)).
  assert (henvironment : appliedEnvironment =
      scons M (raw_term_eval M e root)
        (scons M (raw_term_eval M e assignmentCode)
          (scons M (raw_term_eval M e assignmentStep) e))).
  {
    apply functional_extensionality. intro index.
    destruct index as [|[|[|tailIndex]]]; reflexivity.
  }
  change (raw_formula_sat M appliedEnvironment
      dynamicTruthGlobalPiBaseFormula <->
    raw_formula_sat M e
      (fixedLevelPiFalsityCertificateTermAt 0
        root assignmentCode assignmentStep)).
  rewrite henvironment.
  rewrite raw_sat_dynamicTruthGlobalPiBaseFormula_native_iff.
  rewrite !raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Semantic counterpart of the closed-row shape theorem.  The dynamic base
    predicates are eliminated in favor of the native rank-zero certificate
    relations, so downstream construction can work entirely with the mature
    fixed-level truth API. *)
Theorem raw_sat_dynamicTruthZeroClosedSuccessorRowFormula_native_iff :
  forall (M : RawPAModel) e mode,
  raw_formula_sat M e
    (dynamicTruthZeroClosedSuccessorRowFormula mode) <->
  RawFixedLevelClosedSuccessorRow M 0
    (RawFixedLevelSigmaTruthCertificate M 0)
    (RawFixedLevelPiFalsityCertificate M 0)
    (raw_term_eval M e (tVar 12))
    (raw_term_eval M e (tVar 11))
    (raw_term_eval M e (tVar 10))
    (raw_term_eval M e (tVar 9))
    (raw_term_eval M e (tVar 8))
    (raw_term_eval M e (tVar 7))
    (raw_term_eval M e (tVar 6))
    (raw_term_eval M e (tVar 5))
    (raw_term_eval M e (tVar 4))
    (raw_term_eval M e mode)
    (raw_term_eval M e (tVar 2))
    (raw_term_eval M e (tVar 1))
    (raw_term_eval M e (tVar 0)).
Proof.
  intros M e mode.
  rewrite dynamicTruthZeroClosedSuccessorRow_native_shape.
  apply
    (raw_sat_fixedLevelClosedSuccessorRowTermAt_iff M
      dynamicTruthZeroLowerSigmaApplication
      dynamicTruthZeroLowerPiApplication
      (RawFixedLevelSigmaTruthCertificate M 0)
      (RawFixedLevelPiFalsityCertificate M 0)).
  - intros localEnvironment code assignmentCode assignmentStep.
    rewrite raw_sat_dynamicTruthZeroLowerSigmaApplication_native_iff.
    apply raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  - intros localEnvironment code assignmentCode assignmentStep.
    rewrite raw_sat_dynamicTruthZeroLowerPiApplication_native_iff.
    apply raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
Qed.

(** After exposing the two local-row shapes, the reordered global body is
    definitionally the native level-one traversal body.  The remaining
    discrepancy with the recursive certificate is solely the meaning of the
    two lower applications. *)
Lemma dynamicTruthZeroGlobalTraversalBody_native_shape : forall rootMode,
  dynamicTruthGlobalTraversalBodyFormula rootMode
      (dynamicTruthSigmaSuccessorRowFormula (Term.numeral 1)
        dynamicTruthGlobalPiBaseFormula)
      (dynamicTruthPiSuccessorRowFormula (Term.numeral 1)
        dynamicTruthGlobalSigmaBaseFormula) =
  fixedLevelSuccessorTruthTraversalTermAt 0
      dynamicTruthZeroLowerSigmaApplication
      dynamicTruthZeroLowerPiApplication
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)
      (tVar 9) (tVar 8) rootMode
      (tVar 10) (tVar 11) (tVar 12).
Proof.
  intro rootMode.
  unfold dynamicTruthGlobalTraversalBodyFormula,
    dynamicTruthGlobalModeDefinedFormula,
    dynamicTruthGlobalFormulaDefinedFormula,
    dynamicTruthGlobalAssignmentCodeDefinedFormula,
    dynamicTruthGlobalAssignmentStepDefinedFormula,
    dynamicTruthGlobalRootBoundFormula,
    dynamicTruthGlobalRootLookupFormula,
    dynamicTruthGlobalRowsFormula,
    fixedLevelSuccessorTruthTraversalTermAt,
    fixedLevelSuccessorTruthTraversalRowsTermAt.
  rewrite dynamicTruthZeroSigmaSuccessorRow_native_shape,
    dynamicTruthZeroPiSuccessorRow_native_shape.
  rewrite <- dynamicTruthZeroLowerPiApplication_row_eq,
    <- dynamicTruthZeroLowerSigmaApplication_row_eq.
  reflexivity.
Qed.

(** The complete first global successor has the native level-one meaning.
    This is the semantic permutation step: the global wrapper binds [bound]
    and [rootIndex] first, whereas the recursive certificate binds them last.
    The traversal relation itself is unchanged. *)
Theorem raw_sat_dynamicTruthZeroInputGlobalSigmaFormula_native_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthZeroInputGlobalSigmaFormula <->
  raw_formula_sat M e
    (fixedLevelSigmaTruthCertificateTermAt 1
      (tVar 0) (tVar 1) (tVar 2)).
Proof.
  intros M e.
  assert (hlowerSigma : forall localEnvironment child
      childAssignmentCode childAssignmentStep,
    raw_formula_sat M localEnvironment
      (dynamicTruthZeroLowerSigmaApplication
        child childAssignmentCode childAssignmentStep) <->
    RawFixedLevelSigmaTruthCertificate M 0
      (raw_term_eval M localEnvironment child)
      (raw_term_eval M localEnvironment childAssignmentCode)
      (raw_term_eval M localEnvironment childAssignmentStep)).
  {
    intros localEnvironment child childAssignmentCode childAssignmentStep.
    rewrite raw_sat_dynamicTruthZeroLowerSigmaApplication_native_iff.
    apply raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  }
  assert (hlowerPi : forall localEnvironment child
      childAssignmentCode childAssignmentStep,
    raw_formula_sat M localEnvironment
      (dynamicTruthZeroLowerPiApplication
        child childAssignmentCode childAssignmentStep) <->
    RawFixedLevelPiFalsityCertificate M 0
      (raw_term_eval M localEnvironment child)
      (raw_term_eval M localEnvironment childAssignmentCode)
      (raw_term_eval M localEnvironment childAssignmentStep)).
  {
    intros localEnvironment child childAssignmentCode childAssignmentStep.
    rewrite raw_sat_dynamicTruthZeroLowerPiApplication_native_iff.
    apply raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  }
  unfold dynamicTruthZeroInputGlobalSigmaFormula,
    dynamicTruthGlobalFormula.
  rewrite dynamicTruthZeroGlobalTraversalBody_native_shape.
  cbn [fixedTruthTraversalEx10 fixedLevelEx8 raw_formula_sat].
  setoid_rewrite (raw_sat_fixedLevelSuccessorTruthTraversalTermAt_iff
    M dynamicTruthZeroLowerSigmaApplication
    dynamicTruthZeroLowerPiApplication
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M 0
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M 0
        child childAssignmentCode childAssignmentStep)
    hlowerSigma hlowerPi).
  rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  cbn [RawFixedLevelSigmaTruthCertificate raw_term_eval scons].
  split.
  - intros (bound & rootIndex & modeCode & modeStep & formulaCode &
      formulaStep & assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & htraversal).
    exists modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep, bound, rootIndex.
    exact htraversal.
  - intros (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & bound & rootIndex &
      htraversal).
    exists bound, rootIndex, modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep.
    exact htraversal.
Qed.

Theorem raw_sat_dynamicTruthZeroInputGlobalPiFormula_native_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthZeroInputGlobalPiFormula <->
  raw_formula_sat M e
    (fixedLevelPiFalsityCertificateTermAt 1
      (tVar 0) (tVar 1) (tVar 2)).
Proof.
  intros M e.
  assert (hlowerSigma : forall localEnvironment child
      childAssignmentCode childAssignmentStep,
    raw_formula_sat M localEnvironment
      (dynamicTruthZeroLowerSigmaApplication
        child childAssignmentCode childAssignmentStep) <->
    RawFixedLevelSigmaTruthCertificate M 0
      (raw_term_eval M localEnvironment child)
      (raw_term_eval M localEnvironment childAssignmentCode)
      (raw_term_eval M localEnvironment childAssignmentStep)).
  {
    intros localEnvironment child childAssignmentCode childAssignmentStep.
    rewrite raw_sat_dynamicTruthZeroLowerSigmaApplication_native_iff.
    apply raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  }
  assert (hlowerPi : forall localEnvironment child
      childAssignmentCode childAssignmentStep,
    raw_formula_sat M localEnvironment
      (dynamicTruthZeroLowerPiApplication
        child childAssignmentCode childAssignmentStep) <->
    RawFixedLevelPiFalsityCertificate M 0
      (raw_term_eval M localEnvironment child)
      (raw_term_eval M localEnvironment childAssignmentCode)
      (raw_term_eval M localEnvironment childAssignmentStep)).
  {
    intros localEnvironment child childAssignmentCode childAssignmentStep.
    rewrite raw_sat_dynamicTruthZeroLowerPiApplication_native_iff.
    apply raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  }
  unfold dynamicTruthZeroInputGlobalPiFormula,
    dynamicTruthGlobalFormula.
  rewrite dynamicTruthZeroGlobalTraversalBody_native_shape.
  cbn [fixedTruthTraversalEx10 fixedLevelEx8 raw_formula_sat].
  setoid_rewrite (raw_sat_fixedLevelSuccessorTruthTraversalTermAt_iff
    M dynamicTruthZeroLowerSigmaApplication
    dynamicTruthZeroLowerPiApplication
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M 0
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M 0
        child childAssignmentCode childAssignmentStep)
    hlowerSigma hlowerPi).
  rewrite raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  cbn [RawFixedLevelPiFalsityCertificate raw_term_eval scons].
  split.
  - intros (bound & rootIndex & modeCode & modeStep & formulaCode &
      formulaStep & assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & htraversal).
    exists modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep, bound, rootIndex.
    exact htraversal.
  - intros (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & bound & rootIndex &
      htraversal).
    exists bound, rootIndex, modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep.
    exact htraversal.
Qed.

(** Applying the ternary predicates in the local-field argument order
    therefore has exactly the fixed level-one evidence semantics. *)
Theorem
    raw_sat_dynamicTruthZeroInputGlobalSigmaApplicationFormula_native_iff :
    forall (M : RawPAModel) e,
  raw_formula_sat M e
      dynamicTruthZeroInputGlobalSigmaApplicationFormula <->
  raw_formula_sat M e dynamicTruthZeroSigmaEvidenceFormula.
Proof.
  intros M e.
  unfold dynamicTruthZeroInputGlobalSigmaApplicationFormula.
  rewrite (standardTernaryApplication_eq_subst
    dynamicTruthZeroInputGlobalSigmaFormula
    (tVar 2) (tVar 1) (tVar 0)
    dynamicTruthZeroInputGlobalSigmaFormula_scoped).
  rewrite raw_formula_sat_subst.
  rewrite raw_sat_dynamicTruthZeroInputGlobalSigmaFormula_native_iff.
  unfold dynamicTruthZeroSigmaEvidenceFormula.
  rewrite !raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  cbn [standardTernarySubstitution raw_term_eval]. reflexivity.
Qed.

Theorem
    raw_sat_dynamicTruthZeroInputGlobalPiApplicationFormula_native_iff :
    forall (M : RawPAModel) e,
  raw_formula_sat M e
      dynamicTruthZeroInputGlobalPiApplicationFormula <->
  raw_formula_sat M e dynamicTruthZeroPiEvidenceFormula.
Proof.
  intros M e.
  unfold dynamicTruthZeroInputGlobalPiApplicationFormula.
  rewrite (standardTernaryApplication_eq_subst
    dynamicTruthZeroInputGlobalPiFormula
    (tVar 2) (tVar 1) (tVar 0)
    dynamicTruthZeroInputGlobalPiFormula_scoped).
  rewrite raw_formula_sat_subst.
  rewrite raw_sat_dynamicTruthZeroInputGlobalPiFormula_native_iff.
  unfold dynamicTruthZeroPiEvidenceFormula.
  rewrite !raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  cbn [standardTernarySubstitution raw_term_eval]. reflexivity.
Qed.

(** Forward semantic transports are ordinary open PA theorems.  These are
    the proof-producing form needed downstream: a represented proof of a
    canonical global application can be followed by one [Imp-E] to obtain
    the fixed evidence root expected by the predecessor callback. *)
Definition dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula :
    formula :=
  pImp dynamicTruthZeroInputGlobalSigmaApplicationFormula
    dynamicTruthZeroSigmaEvidenceFormula.

Definition dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula :
    formula :=
  pImp dynamicTruthZeroInputGlobalPiApplicationFormula
    dynamicTruthZeroPiEvidenceFormula.

Lemma
    dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula_raw_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula.
Proof.
  intros M _hPA e.
  unfold dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula.
  cbn [raw_formula_sat]. intro happlication.
  exact (proj1
    (raw_sat_dynamicTruthZeroInputGlobalSigmaApplicationFormula_native_iff
      M e) happlication).
Qed.

Lemma
    dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula_raw_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula.
Proof.
  intros M _hPA e.
  unfold dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula.
  cbn [raw_formula_sat]. intro happlication.
  exact (proj1
    (raw_sat_dynamicTruthZeroInputGlobalPiApplicationFormula_native_iff
      M e) happlication).
Qed.

Theorem
    PA_proves_dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula :
  Formula.BProv Formula.Ax_s nil
    dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact
    dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula_raw_valid.
Qed.

Theorem
    PA_proves_dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula :
  Formula.BProv Formula.Ax_s nil
    dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact
    dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula_raw_valid.
Qed.

(** The semantic comparison above is an equivalence, so the converse
    transports are PA theorems as well.  Naming both directions avoids
    forcing later proof-producing clients to choose one of the two
    extensionally equal presentations as their primitive resource. *)
Definition dynamicTruthZeroInputGlobalSigmaApplicationNativeBackwardFormula :
    formula :=
  pImp dynamicTruthZeroSigmaEvidenceFormula
    dynamicTruthZeroInputGlobalSigmaApplicationFormula.

Definition dynamicTruthZeroInputGlobalPiApplicationNativeBackwardFormula :
    formula :=
  pImp dynamicTruthZeroPiEvidenceFormula
    dynamicTruthZeroInputGlobalPiApplicationFormula.

Lemma
    dynamicTruthZeroInputGlobalSigmaApplicationNativeBackwardFormula_raw_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    dynamicTruthZeroInputGlobalSigmaApplicationNativeBackwardFormula.
Proof.
  intros M _hPA e.
  unfold dynamicTruthZeroInputGlobalSigmaApplicationNativeBackwardFormula.
  cbn [raw_formula_sat]. intro hevidence.
  exact (proj2
    (raw_sat_dynamicTruthZeroInputGlobalSigmaApplicationFormula_native_iff
      M e) hevidence).
Qed.

Lemma
    dynamicTruthZeroInputGlobalPiApplicationNativeBackwardFormula_raw_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    dynamicTruthZeroInputGlobalPiApplicationNativeBackwardFormula.
Proof.
  intros M _hPA e.
  unfold dynamicTruthZeroInputGlobalPiApplicationNativeBackwardFormula.
  cbn [raw_formula_sat]. intro hevidence.
  exact (proj2
    (raw_sat_dynamicTruthZeroInputGlobalPiApplicationFormula_native_iff
      M e) hevidence).
Qed.

Theorem
    PA_proves_dynamicTruthZeroInputGlobalSigmaApplicationNativeBackwardFormula :
  Formula.BProv Formula.Ax_s nil
    dynamicTruthZeroInputGlobalSigmaApplicationNativeBackwardFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact
    dynamicTruthZeroInputGlobalSigmaApplicationNativeBackwardFormula_raw_valid.
Qed.

Theorem
    PA_proves_dynamicTruthZeroInputGlobalPiApplicationNativeBackwardFormula :
  Formula.BProv Formula.Ax_s nil
    dynamicTruthZeroInputGlobalPiApplicationNativeBackwardFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact
    dynamicTruthZeroInputGlobalPiApplicationNativeBackwardFormula_raw_valid.
Qed.

(** The local decision field exposes only one of the two native
    certificates.  Transporting that disjunction branch-by-branch is more
    useful than first demanding both certificates: it preserves exactly the
    information supplied by rank-zero totality. *)
Definition dynamicTruthZeroNativeEvidenceDecisionFormula : formula :=
  pOr dynamicTruthZeroSigmaEvidenceFormula
    dynamicTruthZeroPiEvidenceFormula.

Definition dynamicTruthZeroCanonicalApplicationDecisionFormula : formula :=
  pOr dynamicTruthZeroInputGlobalSigmaApplicationFormula
    dynamicTruthZeroInputGlobalPiApplicationFormula.

Definition
    dynamicTruthZeroNativeEvidenceToCanonicalApplicationDecisionFormula
    : formula :=
  pImp dynamicTruthZeroNativeEvidenceDecisionFormula
    dynamicTruthZeroCanonicalApplicationDecisionFormula.

(** This validity proof deliberately consumes only the two one-polarity
    semantic equivalences.  In particular, it does not strengthen a local
    decision into a pair of certificates. *)
Lemma
    dynamicTruthZeroNativeEvidenceToCanonicalApplicationDecisionFormula_raw_valid
    : forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    dynamicTruthZeroNativeEvidenceToCanonicalApplicationDecisionFormula.
Proof.
  intros M _hPA e.
  unfold
    dynamicTruthZeroNativeEvidenceToCanonicalApplicationDecisionFormula,
    dynamicTruthZeroNativeEvidenceDecisionFormula,
    dynamicTruthZeroCanonicalApplicationDecisionFormula.
  cbn [raw_formula_sat].
  intros [hsigma | hpi].
  - left.
    exact (proj2
      (raw_sat_dynamicTruthZeroInputGlobalSigmaApplicationFormula_native_iff
        M e) hsigma).
  - right.
    exact (proj2
      (raw_sat_dynamicTruthZeroInputGlobalPiApplicationFormula_native_iff
        M e) hpi).
Qed.

Theorem
    PA_proves_dynamicTruthZeroNativeEvidenceToCanonicalApplicationDecisionFormula
    : Formula.BProv Formula.Ax_s nil
      dynamicTruthZeroNativeEvidenceToCanonicalApplicationDecisionFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact
    dynamicTruthZeroNativeEvidenceToCanonicalApplicationDecisionFormula_raw_valid.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.
