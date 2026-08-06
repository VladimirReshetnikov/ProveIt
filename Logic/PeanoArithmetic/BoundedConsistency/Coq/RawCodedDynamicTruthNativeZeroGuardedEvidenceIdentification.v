(**
  Identify the rank-zero local evidence leaves at guarded coordinates.

  The historical rank-zero direct-template identification records the two
  opaque evidence atoms only at the local coordinates [#2,#1,#0].  That
  interface intentionally forgets the ternary-application selectors used to
  construct its direct translation.  Consequently it cannot determine the
  same opaque atoms after changing their arguments to the guarded branch
  coordinates [#2,#6,#5].

  This module retains exactly the extra information needed by that branch.
  It constructs the same direct translation while the two selectors are
  still in scope, uses ternary-application functionality to identify their
  guarded outputs with ordinary quoted PA formulae, and packages those two
  equalities beside the older local-exclusive identification.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardRealization
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedTernaryPredicateDeepClosure
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
Import
  PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.

(** Rename the three local output coordinates [#2,#1,#0] to the guarded
    child and assignment coordinates [#2,#6,#5].  Values above two do not
    occur freely in either evidence formula; preserving them makes the map
    a useful honest renaming outside this specialization as well. *)
Definition dynamicTruthZeroGuardedEvidenceRenaming (index : nat) : nat :=
  match index with
  | 0 => 5
  | 1 => 6
  | 2 => 2
  | S (S (S outer)) => S (S (S outer))
  end.

(** The guarded template openings are literally the corresponding opaque
    local atoms renamed by the map above. *)
Lemma coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate_rename :
  coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate =
  templateFormulaRename dynamicTruthZeroGuardedEvidenceRenaming
    coqDynamicTruthLocalSigmaEvidenceTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicTruthImpGuardedLocalPiEvidenceTemplate_rename :
  coqDynamicTruthImpGuardedLocalPiEvidenceTemplate =
  templateFormulaRename dynamicTruthZeroGuardedEvidenceRenaming
    coqDynamicTruthLocalPiEvidenceTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Applying either fixed rank-zero predicate at [#2,#6,#5] gives exactly
    the corresponding renamed native evidence formula.  These finite
    computations include the binder lifting performed by protected ternary
    application. *)
Lemma dynamicTruthZeroSigmaPredicateFormula_guarded_application :
  standardTernaryApplication dynamicTruthZeroSigmaPredicateFormula
      (tVar 2) (tVar 6) (tVar 5) =
  Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
    dynamicTruthZeroSigmaEvidenceFormula.
Proof. vm_compute. reflexivity. Qed.

Lemma dynamicTruthZeroPiPredicateFormula_guarded_application :
  standardTernaryApplication dynamicTruthZeroPiPredicateFormula
      (tVar 2) (tVar 6) (tVar 5) =
  Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
    dynamicTruthZeroPiEvidenceFormula.
Proof. vm_compute. reflexivity. Qed.

(** Every selector agrees with protected application on quoted terms.  This
    formula-generic lemma extracts the functionality argument shared by the
    Sigma and Pi coordinates below. *)
Lemma rawTernaryApplicationOutput_quoted_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      predicate (selector : RawCodedTernaryApplicationSelector M
        (rawQuotedFormulaCode M predicate)) first second third,
  RawCodedTermSyntax M (rawQuotedTermCode M first) ->
  RawCodedTermSyntax M (rawQuotedTermCode M second) ->
  RawCodedTermSyntax M (rawQuotedTermCode M third) ->
  rawTernaryApplicationOutput selector
      (rawQuotedTermCode M first)
      (rawQuotedTermCode M second)
      (rawQuotedTermCode M third) =
  rawQuotedFormulaCode M
    (standardTernaryApplication predicate first second third).
Proof.
  intros M hPA predicate selector first second third
    hfirst hsecond hthird.
  apply (rawTernaryApplicationOutput_unique M hPA
    (rawQuotedFormulaCode M predicate) selector
    (rawQuotedTermCode M first)
    (rawQuotedTermCode M second)
    (rawQuotedTermCode M third)); try assumption.
  exact (raw_codedTernaryApplication_standard M hPA
    predicate first second third).
Qed.

(** The strengthened witness used by the guarded predecessor compiler.
    Its first field is deliberately the established selector-free record,
    so all existing clients can project back to their old interface. *)
Record RawDynamicTruthZeroGuardedEvidenceIdentification
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop := {
  rawDynamicTruthZeroGuardedEvidence_localExclusive :
    RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaDomainFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiDomainFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula);
  (** The append traversal reserves parameter name six.  Every successor
      parameter name is interpreted by the shared upper-level numeral, so
      retaining its rank-zero code is enough to run the vacuous inherited
      row compiler under this same selector-bearing translation. *)
  rawDynamicTruthZeroGuardedEvidence_appendBoundZero :
    rawDirectTemplateTerm inputs
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    rawQuotedTermCode M tZero;
  rawDynamicTruthZeroGuardedEvidence_sigma :
    rawDirectTemplateFormula inputs
        coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate =
    rawQuotedFormulaCode M
      (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
        dynamicTruthZeroSigmaEvidenceFormula);
  rawDynamicTruthZeroGuardedEvidence_pi :
    rawDirectTemplateFormula inputs
        coqDynamicTruthImpGuardedLocalPiEvidenceTemplate =
    rawQuotedFormulaCode M
      (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
        dynamicTruthZeroPiEvidenceFormula)
}.

Arguments RawDynamicTruthZeroGuardedEvidenceIdentification M inputs
  : clear implicits.

(** Construct one direct translation while its selectors are still visible.
    The domain and local-coordinate fields repeat the established finite
    identification argument.  The final two fields compare the selected
    guarded applications with standard applications of the same predicates;
    cross-trace functionality then forces the carrier codes to agree. *)
Theorem raw_dynamicTruthZeroGuardedEvidenceIdentification_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawDynamicTruthZeroGuardedEvidenceIdentification M inputs.
Proof.
  intros M hPA.
  pose proof
    (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
      dynamicTruthZeroSigmaPredicateFormula
      dynamicTruthZeroSigmaPredicateFormula_scoped) as hsigmaDeep.
  pose proof
    (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
      dynamicTruthZeroPiPredicateFormula
      dynamicTruthZeroPiPredicateFormula_scoped) as hpiDeep.
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
      hsigmaDeep) as [sigmaSelector hsigmaCommuting].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA
      (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
      hpiDeep) as [piSelector hpiCommuting].
  pose proof (raw_numeralTermCodeAt_standard M hPA 0) as hzeroNumeral.
  pose (parameters :=
    rawCoqDynamicTruthTemplateNumeralParameters M
      (raw_zero M) (raw_zero M)
      (rawQuotedTermCode M tZero) (rawQuotedTermCode M tZero)
      hzeroNumeral hzeroNumeral).
  pose (package :=
    rawCoqDynamicTruthTemplateNumeralTermPackage M hPA
      (raw_zero M) (raw_zero M)
      (rawCoqDynamicTruthLocalExclusiveOpaqueCode
        sigmaSelector piSelector)
      parameters eq_refl eq_refl).
  pose (inputs :=
    rawCoqDynamicTruthLocalExclusiveDirectStructuralInputs
      M hPA (raw_zero M) (raw_zero M)
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
      sigmaSelector piSelector hsigmaCommuting hpiCommuting package).
  assert (hterm2 : RawCodedTermSyntax M
      (rawQuotedTermCode M (tVar 2))).
  {
    change (RawCodedTermSyntax M
      (rawDirectTemplateTerm inputs (ttVar 2))).
    exact (rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax
      M hPA (raw_zero M) (raw_zero M)
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
      sigmaSelector piSelector package (ttVar 2)).
  }
  assert (hterm6 : RawCodedTermSyntax M
      (rawQuotedTermCode M (tVar 6))).
  {
    change (RawCodedTermSyntax M
      (rawDirectTemplateTerm inputs (ttVar 6))).
    exact (rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax
      M hPA (raw_zero M) (raw_zero M)
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
      sigmaSelector piSelector package (ttVar 6)).
  }
  assert (hterm5 : RawCodedTermSyntax M
      (rawQuotedTermCode M (tVar 5))).
  {
    change (RawCodedTermSyntax M
      (rawDirectTemplateTerm inputs (ttVar 5))).
    exact (rawCoqDynamicTruthLocalExclusiveTemplateTerm_syntax
      M hPA (raw_zero M) (raw_zero M)
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
      sigmaSelector piSelector package (ttVar 5)).
  }
  exists inputs. constructor.
  - constructor.
    + apply (raw_codedFormulaSingleSubstitution_functional M hPA
        (rawQuotedTermCode M tZero)
        (rawNumeralValue M
          (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
        (rawDirectTemplateFormula inputs
          coqDynamicTruthLocalSigmaDomainTemplate)
        (rawQuotedFormulaCode M dynamicTruthZeroSigmaDomainFormula)).
      * change (RawCodedFormulaSingleSubstitution M
          (rawCoqDynamicTruthUpperNumeralCode package)
          (rawNumeralValue M
            (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
          (rawDirectTemplateFormula inputs
            coqDynamicTruthLocalSigmaDomainTemplate)).
        exact (rawCoqDynamicTruthLocalSigmaDomain_opening_trace
          M hPA (raw_zero M) (raw_zero M)
          (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
          (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
          sigmaSelector piSelector hsigmaCommuting hpiCommuting package).
      * repeat rewrite <- rawQuotedFormulaCode_standard by exact hPA.
        exact (raw_dynamicTruthZeroSigmaDomain_substitution M hPA).
    + apply (raw_codedFormulaSingleSubstitution_functional M hPA
        (rawQuotedTermCode M tZero)
        (rawNumeralValue M
          (formulaCode dynamicTruthLocalPiInputDomainTemplate))
        (rawDirectTemplateFormula inputs
          coqDynamicTruthLocalPiDomainTemplate)
        (rawQuotedFormulaCode M dynamicTruthZeroPiDomainFormula)).
      * change (RawCodedFormulaSingleSubstitution M
          (rawCoqDynamicTruthUpperNumeralCode package)
          (rawNumeralValue M
            (formulaCode dynamicTruthLocalPiInputDomainTemplate))
          (rawDirectTemplateFormula inputs
            coqDynamicTruthLocalPiDomainTemplate)).
        exact (rawCoqDynamicTruthLocalPiDomain_opening_trace
          M hPA (raw_zero M) (raw_zero M)
          (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
          (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
          sigmaSelector piSelector hsigmaCommuting hpiCommuting package).
      * repeat rewrite <- rawQuotedFormulaCode_standard by exact hPA.
        exact (raw_dynamicTruthZeroPiDomain_substitution M hPA).
    + exact (rawCoqDynamicTruthLocalSigmaEvidence_identifies_native
        M hPA (raw_zero M) (raw_zero M)
        (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
        (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
        sigmaSelector piSelector hsigmaCommuting hpiCommuting package
        (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
        (raw_dynamicTruthZeroSigmaEvidence_application M hPA)).
    + exact (rawCoqDynamicTruthLocalPiEvidence_identifies_native
        M hPA (raw_zero M) (raw_zero M)
        (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
        (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
        sigmaSelector piSelector hsigmaCommuting hpiCommuting package
        (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula)
        (raw_dynamicTruthZeroPiEvidence_application M hPA)).
    + reflexivity.
  - reflexivity.
  - change
      (rawTernaryApplicationOutput sigmaSelector
        (rawQuotedTermCode M (tVar 2))
        (rawQuotedTermCode M (tVar 6))
        (rawQuotedTermCode M (tVar 5)) =
       rawQuotedFormulaCode M
        (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
          dynamicTruthZeroSigmaEvidenceFormula)).
    rewrite <- dynamicTruthZeroSigmaPredicateFormula_guarded_application.
    apply (rawTernaryApplicationOutput_quoted_standard M hPA);
      assumption.
  - change
      (rawTernaryApplicationOutput piSelector
        (rawQuotedTermCode M (tVar 2))
        (rawQuotedTermCode M (tVar 6))
        (rawQuotedTermCode M (tVar 5)) =
       rawQuotedFormulaCode M
        (Formula.rename dynamicTruthZeroGuardedEvidenceRenaming
          dynamicTruthZeroPiEvidenceFormula)).
    rewrite <- dynamicTruthZeroPiPredicateFormula_guarded_application.
    apply (rawTernaryApplicationOutput_quoted_standard M hPA);
      assumption.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification.
