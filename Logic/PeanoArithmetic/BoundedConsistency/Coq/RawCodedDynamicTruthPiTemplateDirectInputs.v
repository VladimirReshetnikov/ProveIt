(**
  Direct structural inputs and exact identification for the Pi successor row.

  The Pi source template deliberately uses the same numeric parameter names,
  opaque-predicate name, and three de Bruijn substitutions as the Sigma
  source.  We therefore reuse [rawCoqDynamicTruthTemplateDirectStructuralInputs]
  unchanged: only the intended polarity of its selected input formula differs.

  This file proves the Pi-specific domain trace, transports the already proved
  lower-application trace through the definitional polarity equivalence, and
  packages the two resulting code equalities in
  [RawCoqDynamicTruthPiDirectTemplateIdentification].  The only operation law
  required from a selector is the existing honest-syntax-guarded commuting
  record; no off-domain commutation premise is introduced.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedFormulaOperations
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateProjectionSchemas
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.

(** Explicit audits of the namespace sharing on which reuse depends. *)
Lemma coqDynamicTruthPiLowerLevelParameterName_eq_shared :
  coqDynamicTruthPiLowerLevelParameterName =
  coqDynamicTruthLowerLevelParameterName.
Proof. reflexivity. Qed.

Lemma coqDynamicTruthPiUpperLevelParameterName_eq_shared :
  coqDynamicTruthPiUpperLevelParameterName =
  coqDynamicTruthUpperLevelParameterName.
Proof. reflexivity. Qed.

Lemma coqDynamicTruthLowerSigmaPredicateName_eq_shared :
  coqDynamicTruthLowerSigmaPredicateName =
  coqDynamicTruthLowerPiPredicateName.
Proof. reflexivity. Qed.

Lemma coqDynamicTruthPiLowerLevelTerm_eq_shared :
  coqDynamicTruthPiLowerLevelTerm = coqDynamicTruthLowerLevelTerm.
Proof. reflexivity. Qed.

Lemma coqDynamicTruthPiUpperLevelTerm_eq_shared :
  coqDynamicTruthPiUpperLevelTerm = coqDynamicTruthUpperLevelTerm.
Proof. reflexivity. Qed.

(** The Pi-facing name is only a polarity annotation.  Its implementation is
    exactly the already audited direct input record. *)
Definition rawCoqDynamicTruthPiTemplateDirectStructuralInputs
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (lowerLevel upperLevel lowerSigmaCode : M)
    (selector : RawCodedTernaryApplicationSelector M lowerSigmaCode)
    (commutingOnSyntax :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
        M lowerSigmaCode selector)
    (package : RawCodedDynamicTruthTemplateNumeralTermPackage
      M lowerLevel upperLevel
      (rawCoqDynamicTruthTemplateOpaqueCode selector))
    : RawCodedTemplateDirectStructuralInputs M :=
  rawCoqDynamicTruthTemplateDirectStructuralInputs
    M hPA lowerLevel upperLevel lowerSigmaCode selector
    commutingOnSyntax package.

Arguments rawCoqDynamicTruthPiTemplateDirectStructuralInputs
  M _ _ _ _ _ _ _ : clear implicits.

(** The Pi graph writes this fixed metacode directly as [formulaCode]. *)
Lemma raw_dynamicTruthPiRowDomainTemplate_quoted_code : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawQuotedFormulaCode M dynamicTruthPiRowDomainTemplate =
  rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate).
Proof.
  intros M hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

(** Direct counterpart of the source module's opaque-atom polynomial. *)
Definition rawCoqDynamicTruthLowerSigmaDirectAtomTemplateCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawStructuralTemplateOpaqueCode
    (rawDirectTemplateSymbols inputs)
    coqDynamicTruthLowerSigmaPredicateName
    [rawTermVarCode M (rawNumeralValue M 9);
     rawTermVarCode M (rawNumeralValue M 1);
     rawTermVarCode M (rawNumeralValue M 0)].

Theorem rawDirect_coqDynamicTruthLowerSigmaAtomTemplate : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs coqDynamicTruthLowerSigmaAtomTemplate =
  rawCoqDynamicTruthLowerSigmaDirectAtomTemplateCode M inputs.
Proof.
  intros M inputs. reflexivity.
Qed.

(** These two equalities are exactly what a direct proof compiler needs to
    retarget a structurally translated proof to graph-selected witnesses. *)
Record RawCoqDynamicTruthPiDirectTemplateIdentification
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (concreteDomain concreteLowerApplication : M) : Prop := {
  rawCoqDynamicTruthPiDirect_domain_identified :
    rawDirectTemplateFormula inputs
      coqDynamicTruthPiDomainLeafTemplate = concreteDomain;
  rawCoqDynamicTruthPiDirect_lowerApplication_identified :
    rawCoqDynamicTruthLowerSigmaDirectAtomTemplateCode M inputs =
      concreteLowerApplication
}.

Arguments rawCoqDynamicTruthPiDirect_domain_identified
  {M inputs concreteDomain concreteLowerApplication} _.
Arguments rawCoqDynamicTruthPiDirect_lowerApplication_identified
  {M inputs concreteDomain concreteLowerApplication} _.

(** ------------------------------------------------------------------
    Direct structural equations used by later proof compilation. *)

Theorem rawDirect_coqDynamicTruthPiExistentialLeafTemplate : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
    coqDynamicTruthPiExistentialLeafTemplate =
  rawCoqDynamicTruthPiExistentialLeafTemplateCode M
    (rawCoqDynamicTruthLowerSigmaDirectAtomTemplateCode M inputs).
Proof.
  intros M inputs.
  unfold coqDynamicTruthPiExistentialLeafTemplate,
    coqDynamicTruthPiExistentialPrefixTemplate,
    coqDynamicTruthPiNoBinderCounterexampleTemplate,
    coqDynamicTruthPiBinderPrependTemplate,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode.
  cbn [templateRepeatedExists rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  reflexivity.
Qed.

Theorem rawDirect_coqDynamicTruthPiBranchesTemplate : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs coqDynamicTruthPiBranchesTemplate =
  rawCoqDynamicTruthPiBranchesTemplateCode M
    (rawCoqDynamicTruthLowerSigmaDirectAtomTemplateCode M inputs).
Proof.
  intros M inputs.
  unfold coqDynamicTruthPiBranchesTemplate,
    coqDynamicTruthPiQfLeafTemplate,
    coqDynamicTruthPiImpLeafTemplate,
    coqDynamicTruthPiAndLeafTemplate,
    coqDynamicTruthPiOrLeafTemplate,
    coqDynamicTruthPiAllLeafTemplate,
    coqDynamicTruthPiExistentialLeafTemplate,
    coqDynamicTruthPiExistentialPrefixTemplate,
    coqDynamicTruthPiNoBinderCounterexampleTemplate,
    coqDynamicTruthPiBinderPrependTemplate,
    rawCoqDynamicTruthPiBranchesTemplateCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode.
  cbn [templateRepeatedExists rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  reflexivity.
Qed.

Theorem rawDirect_coqDynamicTruthPiSuccessorRowTemplate : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs coqDynamicTruthPiSuccessorRowTemplate =
  rawCoqDynamicTruthPiSuccessorRowTemplateCode M
    (rawDirectTemplateFormula inputs coqDynamicTruthPiDomainLeafTemplate)
    (rawCoqDynamicTruthLowerSigmaDirectAtomTemplateCode M inputs).
Proof.
  intros M inputs.
  unfold rawCoqDynamicTruthPiSuccessorRowTemplateCode.
  change (rawDynamicTruthPiFormulaEx8Code M
    (rawFormulaAndCode M
      (rawDirectTemplateFormula inputs coqDynamicTruthPiDomainLeafTemplate)
      (rawDirectTemplateFormula inputs coqDynamicTruthPiBranchesTemplate)) =
    rawDynamicTruthPiFormulaEx8Code M
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthPiDomainLeafTemplate)
        (rawCoqDynamicTruthPiBranchesTemplateCode M
          (rawCoqDynamicTruthLowerSigmaDirectAtomTemplateCode M inputs)))).
  rewrite rawDirect_coqDynamicTruthPiBranchesTemplate.
  reflexivity.
Qed.

Theorem rawDirect_coqDynamicTruthPiSuccessorRowTemplate_identified :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs coqDynamicTruthPiSuccessorRowTemplate =
  rawCoqDynamicTruthPiSuccessorRowTemplateCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication identification.
  rewrite rawDirect_coqDynamicTruthPiSuccessorRowTemplate.
  rewrite (rawCoqDynamicTruthPiDirect_domain_identified identification).
  rewrite
    (rawCoqDynamicTruthPiDirect_lowerApplication_identified identification).
  reflexivity.
Qed.

Corollary rawDirect_coqDynamicTruthPiSuccessorRowTemplate_identifies_native :
  forall (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M)
      concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs coqDynamicTruthPiSuccessorRowTemplate =
  rawDynamicTruthPiSuccessorRowCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  rewrite (rawDirect_coqDynamicTruthPiSuccessorRowTemplate_identified
    M inputs concreteDomain concreteLowerApplication identification).
  exact (rawCoqDynamicTruthPiSuccessorRowTemplateCode_eq_native
    M hPA concreteDomain concreteLowerApplication).
Qed.

(** Identification of the restricted proof core is the immediate entry point
    for a Pi analogue of the closed-template proof compiler. *)
Theorem rawDirect_coqDynamicTruthPiRestrictedProjection_identified :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthPiRestrictedExistentialProjectionFormula =
  rawCoqDynamicTruthPiRestrictedExistentialProjectionCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication identification.
  unfold rawCoqDynamicTruthPiRestrictedExistentialProjectionCode.
  change (rawFormulaImpCode M
    (rawDynamicTruthPiFormulaEx8Code M
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthPiDomainLeafTemplate)
        (rawDirectTemplateFormula inputs
          coqDynamicTruthPiExistentialLeafTemplate)))
    (rawDynamicTruthPiFormulaEx8Code M
      (rawDirectTemplateFormula inputs
        coqDynamicTruthPiExistentialLeafTemplate)) =
    rawFormulaImpCode M
      (rawDynamicTruthPiFormulaEx8Code M
        (rawFormulaAndCode M concreteDomain
          (rawCoqDynamicTruthPiExistentialLeafTemplateCode M
            concreteLowerApplication)))
      (rawDynamicTruthPiFormulaEx8Code M
        (rawCoqDynamicTruthPiExistentialLeafTemplateCode M
          concreteLowerApplication))).
  rewrite !rawDirect_coqDynamicTruthPiExistentialLeafTemplate.
  rewrite (rawCoqDynamicTruthPiDirect_domain_identified identification).
  rewrite
    (rawCoqDynamicTruthPiDirect_lowerApplication_identified identification).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Concrete selector/domain/application identification. *)

Lemma raw_dynamicTruthPiCoqLowerApplication_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall input output output',
  RawDynamicTruthPiCoqLowerApplication M input output ->
  RawDynamicTruthPiCoqLowerApplication M input output' ->
  output = output'.
Proof.
  intros M hPA input output output' houtput houtput'.
  apply (raw_dynamicTruthCoqLowerApplication_functional
    M hPA input output output').
  - exact (proj1
      (raw_dynamicTruthPiCoqLowerApplication_iff_sigma
        M input output) houtput).
  - exact (proj1
      (raw_dynamicTruthPiCoqLowerApplication_iff_sigma
        M input output') houtput').
Qed.

Section DirectFields.

Context (M : RawPAModel) (hPA : RawPASatisfies M).
Context (lowerLevel upperLevel lowerSigmaCode : M).
Context (selector : RawCodedTernaryApplicationSelector M lowerSigmaCode).
Context (commutingOnSyntax :
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M lowerSigmaCode selector).
Context (package : RawCodedDynamicTruthTemplateNumeralTermPackage
  M lowerLevel upperLevel
  (rawCoqDynamicTruthTemplateOpaqueCode selector)).

Let inputs : RawCodedTemplateDirectStructuralInputs M :=
  rawCoqDynamicTruthPiTemplateDirectStructuralInputs
    M hPA lowerLevel upperLevel lowerSigmaCode selector
    commutingOnSyntax package.

(** Direct opening of the Pi domain with the shared upper numeral code. *)
Lemma rawCoqDynamicTruthPiDomainLeaf_opening_trace :
  RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate))
    (rawDirectTemplateFormula inputs
      coqDynamicTruthPiDomainLeafTemplate).
Proof.
  pose proof (rawDirectTemplateFormula_openingAt M hPA inputs
    0 coqDynamicTruthPiUpperLevelTerm
    (embedPAFormula dynamicTruthPiRowDomainTemplate)) as hopening.
  change (RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawDirectTemplateFormula inputs
      (embedPAFormula dynamicTruthPiRowDomainTemplate))
    (rawDirectTemplateFormula inputs
      coqDynamicTruthPiDomainLeafTemplate)) in hopening.
  unfold rawDirectTemplateFormula in hopening.
  rewrite rawStructuralTemplateFormulaWith_embedPA in hopening.
  rewrite raw_dynamicTruthPiRowDomainTemplate_quoted_code in hopening
    by exact hPA.
  exact hopening.
Qed.

Lemma rawCoqDynamicTruthPiDomainLeaf_identifies_native_domain : forall
    domain,
  RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate))
    domain ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthPiDomainLeafTemplate = domain.
Proof.
  intros domain hdomain.
  exact (raw_codedFormulaSingleSubstitution_functional M hPA
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate))
    (rawDirectTemplateFormula inputs
      coqDynamicTruthPiDomainLeafTemplate)
    domain rawCoqDynamicTruthPiDomainLeaf_opening_trace hdomain).
Qed.

(** The direct lower-Sigma atom is definitionally the same designated
    ternary leaf already handled by the shared translator. *)
Lemma rawCoqDynamicTruthLowerSigmaAtomDirect_code :
  rawDirectTemplateFormula inputs
    coqDynamicTruthLowerSigmaAtomTemplate =
  rawTernaryApplicationOutput selector
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0)).
Proof. reflexivity. Qed.

Lemma rawCoqDynamicTruthLowerSigmaAtom_selector_trace :
  RawCodedTernaryApplication M lowerSigmaCode
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0))
    (rawDirectTemplateFormula inputs
      coqDynamicTruthLowerSigmaAtomTemplate).
Proof.
  change (RawCodedTernaryApplication M lowerSigmaCode
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0))
    (rawDirectTemplateFormula
      (rawCoqDynamicTruthTemplateDirectStructuralInputs
        M hPA lowerLevel upperLevel lowerSigmaCode selector
        commutingOnSyntax package)
      coqDynamicTruthLowerPiAtomTemplate)).
  exact (rawCoqDynamicTruthLowerPiAtom_selector_trace
    M hPA lowerLevel upperLevel lowerSigmaCode selector
    commutingOnSyntax package).
Qed.

Definition RawCoqDynamicTruthPiLowerApplicationCompatibility : Prop :=
  RawDynamicTruthPiCoqLowerApplication M lowerSigmaCode
    (rawTernaryApplicationOutput selector
      (rawTermVarCode M (rawNumeralValue M 9))
      (rawTermVarCode M (rawNumeralValue M 1))
      (rawTermVarCode M (rawNumeralValue M 0))).

(** Reuse the shared three substitutions through the exact polarity
    equivalence; no second trace derivation is needed. *)
Lemma rawCoqDynamicTruthPiLowerApplicationCompatibility_holds :
  RawCoqDynamicTruthPiLowerApplicationCompatibility.
Proof.
  unfold RawCoqDynamicTruthPiLowerApplicationCompatibility.
  apply (proj2 (raw_dynamicTruthPiCoqLowerApplication_iff_sigma M
    lowerSigmaCode
    (rawTernaryApplicationOutput selector
      (rawTermVarCode M (rawNumeralValue M 9))
      (rawTermVarCode M (rawNumeralValue M 1))
      (rawTermVarCode M (rawNumeralValue M 0))))).
  exact (rawCoqDynamicTruthLowerApplicationCompatibility_holds
    M hPA lowerLevel upperLevel lowerSigmaCode selector
    package).
Qed.

Lemma rawCoqDynamicTruthPiLowerApplication_selector_unique : forall
    lowerApplication,
  RawDynamicTruthPiCoqLowerApplication M lowerSigmaCode lowerApplication ->
  rawTernaryApplicationOutput selector
    (rawTermVarCode M (rawNumeralValue M 9))
    (rawTermVarCode M (rawNumeralValue M 1))
    (rawTermVarCode M (rawNumeralValue M 0)) = lowerApplication.
Proof.
  intros lowerApplication hlowerApplication.
  exact (raw_dynamicTruthPiCoqLowerApplication_functional M hPA
    lowerSigmaCode
    (rawTernaryApplicationOutput selector
      (rawTermVarCode M (rawNumeralValue M 9))
      (rawTermVarCode M (rawNumeralValue M 1))
      (rawTermVarCode M (rawNumeralValue M 0)))
    lowerApplication
    rawCoqDynamicTruthPiLowerApplicationCompatibility_holds
    hlowerApplication).
Qed.

Lemma rawCoqDynamicTruthLowerSigmaAtom_identifies_native_application :
    forall lowerApplication,
  RawDynamicTruthPiCoqLowerApplication M lowerSigmaCode lowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthLowerSigmaAtomTemplate = lowerApplication.
Proof.
  intros lowerApplication hlowerApplication.
  rewrite rawCoqDynamicTruthLowerSigmaAtomDirect_code.
  exact (rawCoqDynamicTruthPiLowerApplication_selector_unique
    lowerApplication hlowerApplication).
Qed.

Lemma rawCoqDynamicTruthLowerSigmaAtom_native_application :
  RawDynamicTruthPiCoqLowerApplication M lowerSigmaCode
    (rawDirectTemplateFormula inputs
      coqDynamicTruthLowerSigmaAtomTemplate).
Proof.
  rewrite rawCoqDynamicTruthLowerSigmaAtomDirect_code.
  exact rawCoqDynamicTruthPiLowerApplicationCompatibility_holds.
Qed.

Theorem rawCoqDynamicTruthPiDirectTemplateIdentification_of_native :
    forall domain lowerApplication,
  RawCodedFormulaSingleSubstitution M
    (rawCoqDynamicTruthUpperNumeralCode package)
    (rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate))
    domain ->
  RawDynamicTruthPiCoqLowerApplication M
    lowerSigmaCode lowerApplication ->
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    domain lowerApplication.
Proof.
  intros domain lowerApplication hdomain hlowerApplication.
  constructor.
  - exact (rawCoqDynamicTruthPiDomainLeaf_identifies_native_domain
      domain hdomain).
  - rewrite <- (rawDirect_coqDynamicTruthLowerSigmaAtomTemplate M inputs).
    exact (rawCoqDynamicTruthLowerSigmaAtom_identifies_native_application
      lowerApplication hlowerApplication).
Qed.

End DirectFields.

(** Build the complete direct-input/identification package around an upper
    numeral chosen by a graph.  Besides the graph's own domain/application
    traces, the only selector law is honest-syntax-guarded commutation. *)
Theorem raw_coqDynamicTruthPiDirectTemplateIdentification_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (lowerLevel upperLevel lowerSigmaCode upperNumeral
      domain lowerApplication : M)
    (selector : RawCodedTernaryApplicationSelector M lowerSigmaCode),
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M lowerSigmaCode selector ->
  RawNumeralTermCodeAt M upperLevel upperNumeral ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate))
    domain ->
  RawDynamicTruthPiCoqLowerApplication M
    lowerSigmaCode lowerApplication ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
      domain lowerApplication.
Proof.
  intros M hPA lowerLevel upperLevel lowerSigmaCode upperNumeral
    domain lowerApplication selector commutingOnSyntax hupperNumeral
    hdomain hlowerApplication.
  destruct (raw_numeralTermCodeExists_all M hPA lowerLevel)
    as [lowerNumeral hlowerNumeral].
  pose (parameters :=
    rawCoqDynamicTruthTemplateNumeralParameters M
      lowerLevel upperLevel lowerNumeral upperNumeral
      hlowerNumeral hupperNumeral).
  pose (package :=
    rawCoqDynamicTruthTemplateNumeralTermPackage M hPA
      lowerLevel upperLevel
      (rawCoqDynamicTruthTemplateOpaqueCode selector)
      parameters eq_refl eq_refl).
  pose (inputs :=
    rawCoqDynamicTruthPiTemplateDirectStructuralInputs M hPA
      lowerLevel upperLevel lowerSigmaCode selector
      commutingOnSyntax package).
  exists inputs.
  apply (rawCoqDynamicTruthPiDirectTemplateIdentification_of_native
    M hPA lowerLevel upperLevel lowerSigmaCode selector
    commutingOnSyntax package domain lowerApplication).
  - change (RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate))
      domain).
    exact hdomain.
  - exact hlowerApplication.
Qed.

End PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
