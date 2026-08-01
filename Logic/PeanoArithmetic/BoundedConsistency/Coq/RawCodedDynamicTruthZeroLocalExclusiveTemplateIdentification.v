(**
  A finite direct-template presentation of the rank-zero local exclusivity
  field.

  The spliced native recursion stores the rank-zero local theorem as an
  ordinary quoted PA formula.  Predecessor-state closure, however, consumes
  the same theorem through the four-leaf direct template interface used at
  nonstandard successor levels.  This module identifies those presentations.

  The evidence predicate sources reverse their three formal variables.  A
  protected application at [#2,#1,#0] reverses them back, giving the literal
  fixed-level-one Sigma and Pi evidence formulas in the rank-zero field.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardRealization
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPADerivationSoundnessScope
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedStandardFormulaScopeDecision
  RawCodedTernaryPredicateDeepClosure
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalTernaryApplicationAlignment
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.

Module PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPADerivationSoundnessScope.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedStandardFormulaScopeDecision.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalTernaryApplicationAlignment.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.

Definition dynamicTruthZeroSigmaDomainFormula : formula :=
  fixedLevelSigmaDomainTermAt 0 (tVar 2).

Definition dynamicTruthZeroPiDomainFormula : formula :=
  fixedLevelPiDomainTermAt 0 (tVar 2).

Definition dynamicTruthZeroSigmaEvidenceFormula : formula :=
  fixedLevelSigmaTruthCertificateTermAt 1
    (tVar 2) (tVar 1) (tVar 0).

Definition dynamicTruthZeroPiEvidenceFormula : formula :=
  fixedLevelPiFalsityCertificateTermAt 1
    (tVar 2) (tVar 1) (tVar 0).

(** Reverse only the three formal predicate slots. *)
Definition dynamicTruthZeroReverseFirstThreeRenaming (index : nat) : nat :=
  match index with
  | 0 => 2
  | 1 => 1
  | 2 => 0
  | S (S (S outer)) => S (S (S outer))
  end.

Definition dynamicTruthZeroSigmaPredicateFormula : formula :=
  Formula.rename dynamicTruthZeroReverseFirstThreeRenaming
    dynamicTruthZeroSigmaEvidenceFormula.

Definition dynamicTruthZeroPiPredicateFormula : formula :=
  Formula.rename dynamicTruthZeroReverseFirstThreeRenaming
    dynamicTruthZeroPiEvidenceFormula.

Lemma dynamicTruthZeroSigmaDomainFormula_open :
  Formula.subst (Formula.instTerm tZero)
    dynamicTruthLocalSigmaInputDomainTemplate =
  dynamicTruthZeroSigmaDomainFormula.
Proof. vm_compute. reflexivity. Qed.

Lemma dynamicTruthZeroPiDomainFormula_open :
  Formula.subst (Formula.instTerm tZero)
    dynamicTruthLocalPiInputDomainTemplate =
  dynamicTruthZeroPiDomainFormula.
Proof. vm_compute. reflexivity. Qed.

Lemma dynamicTruthZeroSigmaPredicateFormula_application :
  standardTernaryApplication dynamicTruthZeroSigmaPredicateFormula
    (tVar 2) (tVar 1) (tVar 0) =
  dynamicTruthZeroSigmaEvidenceFormula.
Proof. vm_compute. reflexivity. Qed.

Lemma dynamicTruthZeroPiPredicateFormula_application :
  standardTernaryApplication dynamicTruthZeroPiPredicateFormula
    (tVar 2) (tVar 1) (tVar 0) =
  dynamicTruthZeroPiEvidenceFormula.
Proof. vm_compute. reflexivity. Qed.

(** The fixed evidence formulas use only their displayed three arguments;
    reversing those arguments therefore preserves ternary scope. *)
Lemma dynamicTruthZeroSigmaPredicateFormula_scoped :
  StandardFormulaScoped 3 dynamicTruthZeroSigmaPredicateFormula.
Proof.
  apply (proj1 (standardFormulaScopedb_spec 3 _)).
  vm_compute. reflexivity.
Qed.

Lemma dynamicTruthZeroPiPredicateFormula_scoped :
  StandardFormulaScoped 3 dynamicTruthZeroPiPredicateFormula.
Proof.
  apply (proj1 (standardFormulaScopedb_spec 3 _)).
  vm_compute. reflexivity.
Qed.

(** Standard substitution realizes the two concrete domain leaves. *)
Lemma raw_dynamicTruthZeroSigmaDomain_substitution : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaSingleSubstitution M
    (rawQuotedTermCode M tZero)
    (rawQuotedFormulaCode M dynamicTruthLocalSigmaInputDomainTemplate)
    (rawQuotedFormulaCode M dynamicTruthZeroSigmaDomainFormula).
Proof.
  intros M hPA.
  rewrite <- dynamicTruthZeroSigmaDomainFormula_open.
  exact (raw_codedFormulaSingleSubstitution_standard M hPA tZero
    dynamicTruthLocalSigmaInputDomainTemplate).
Qed.

Lemma raw_dynamicTruthZeroPiDomain_substitution : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaSingleSubstitution M
    (rawQuotedTermCode M tZero)
    (rawQuotedFormulaCode M dynamicTruthLocalPiInputDomainTemplate)
    (rawQuotedFormulaCode M dynamicTruthZeroPiDomainFormula).
Proof.
  intros M hPA.
  rewrite <- dynamicTruthZeroPiDomainFormula_open.
  exact (raw_codedFormulaSingleSubstitution_standard M hPA tZero
    dynamicTruthLocalPiInputDomainTemplate).
Qed.

(** Generic standard ternary realization, transported through the alignment
    theorem above, gives the two literal native application relations. *)
Lemma raw_dynamicTruthZeroSigmaEvidence_application : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthLocalTernaryApplication M
    (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
    (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula).
Proof.
  intros M hPA.
  apply (proj2
    (raw_dynamicTruthLocalTernaryApplication_ternary_iff M hPA
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula))).
  rewrite <- dynamicTruthZeroSigmaPredicateFormula_application.
  exact (raw_codedTernaryApplication_standard M hPA
    dynamicTruthZeroSigmaPredicateFormula (tVar 2) (tVar 1) (tVar 0)).
Qed.

Lemma raw_dynamicTruthZeroPiEvidence_application : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthLocalTernaryApplication M
    (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
    (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula).
Proof.
  intros M hPA.
  apply (proj2
    (raw_dynamicTruthLocalTernaryApplication_ternary_iff M hPA
      (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula))).
  rewrite <- dynamicTruthZeroPiPredicateFormula_application.
  exact (raw_codedTernaryApplication_standard M hPA
    dynamicTruthZeroPiPredicateFormula (tVar 2) (tVar 1) (tVar 0)).
Qed.

(** All syntactic coordinates of the direct bridge are now fixed.  Only the
    three predecessor-state logical roots remain proof-producing. *)
Theorem raw_dynamicTruthZeroLocalExclusiveTemplateIdentification_exists :
    forall (M : RawPAModel), RawPASatisfies M ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaDomainFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiDomainFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula).
Proof.
  intros M hPA.
  apply (raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_deepClosed
    M hPA (raw_zero M) (rawQuotedTermCode M tZero)
    (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
    (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
    (rawQuotedFormulaCode M dynamicTruthZeroSigmaDomainFormula)
    (rawQuotedFormulaCode M dynamicTruthZeroPiDomainFormula)
    (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
    (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula)).
  - exact (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
      dynamicTruthZeroSigmaPredicateFormula
      dynamicTruthZeroSigmaPredicateFormula_scoped).
  - exact (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
      dynamicTruthZeroPiPredicateFormula
      dynamicTruthZeroPiPredicateFormula_scoped).
  - exact (raw_numeralTermCodeAt_standard M hPA 0).
  - repeat rewrite <- rawQuotedFormulaCode_standard by exact hPA.
    exact (raw_dynamicTruthZeroSigmaDomain_substitution M hPA).
  - repeat rewrite <- rawQuotedFormulaCode_standard by exact hPA.
    exact (raw_dynamicTruthZeroPiDomain_substitution M hPA).
  - exact (raw_dynamicTruthZeroSigmaEvidence_application M hPA).
  - exact (raw_dynamicTruthZeroPiEvidence_application M hPA).
Qed.

End PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
