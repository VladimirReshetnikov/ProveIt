(**
  The honest domain boundary for carrier-level formula-bound totality.

  A well-formed formula traversal alone permits arbitrary payloads at an
  equality atom, so it is not sufficient for [Formula.bound]: the two term
  payloads must themselves carry represented syntax.  The established
  [RawCodedFormulaAtomicallyAdequate] predicate is exactly the strengthened
  domain required by such a fold.

  Formula-shift traces already contain this information on their source
  side.  We prove that fact below, then isolate the one genuinely missing
  reusable theorem as [RawCodedFormulaBoundAtomicallyAdequateTotal].  If that
  model-global fold is supplied, the direct strong-prefix closure remainder
  follows with no per-formula bound hypothesis, no closure-existence
  hypothesis, and no separately supplied self-instantiation orbit.

  No fold theorem with this conclusion currently exists in the repository.
  Constructing it requires a PA-definable strong induction over formula
  codes which simultaneously builds the normalized source column and the
  numeric bound column used by [RawCodedFormulaBoundTrace].  Its atomic case
  additionally needs the analogous term-bound fold from
  [RawTermSyntaxRealizable].  An occurrence-indexed syntax traversal by
  itself cannot be reused as the required table: [RawCodedFormulaBound]
  indexes its root at the carrier formula code and is defined through its
  successor, including default rows for intervening malformed codes.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation
  RawCodedTermEvaluationStepFunctionality
  RawCodedFormulaOperations
  RawCodedFormulaRankTotality
  RawCodedPAAxiomWitness
  RawCodedUniversalClosureDiagonalSubstitution
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaSubstitutionAtomSourceSyntax
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedUniversalClosureAllCarrierTotality.

Module PABoundedRawCodedFormulaBoundAllCarrierBoundary.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedTermEvaluationStepFunctionality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedUniversalClosureDiagonalSubstitution.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaSubstitutionAtomSourceSyntax.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedUniversalClosureAllCarrierTotality.

(** If an operation source is an equality, constructor separation rules out
    every non-equality source row.  This is the source-column counterpart of
    [raw_formulaShift_eq_row_of_target]. *)
Lemma raw_formulaShift_eq_row_of_source : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth left right,
  RawCodedFormulaOperationTraversalRow M (RawCodedFormulaShiftAtom M)
    parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth ->
  input = rawFormulaEqCode M left right ->
  RawCodedFormulaEqOperationRow M (RawCodedFormulaShiftAtom M)
    parameter depth input output.
Proof.
  intros M hPA parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth left right hrow hinputEq.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]];
    [exact heq | ..].
  - destruct hbot as [hinput _]. exfalso.
    unfold rawFormulaBotCode, rawFormulaEqCode in hinput, hinputEq.
    apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym hinput) hinputEq).
  - destruct himp as
      (_ & inputLeft & _ & _ & _ & inputRight & _ & _ &
       _ & _ & _ & _ & _ & _ & hinput & _).
    exfalso. apply (raw_formulaShift_nonzero_binary_neq_eq
      M hPA 2 inputLeft inputRight left right); [discriminate |].
    unfold rawFormulaImpCode in hinput.
    exact (eq_trans (eq_sym hinput) hinputEq).
  - destruct hand as
      (_ & inputLeft & _ & _ & _ & inputRight & _ & _ &
       _ & _ & _ & _ & _ & _ & hinput & _).
    exfalso. apply (raw_formulaShift_nonzero_binary_neq_eq
      M hPA 3 inputLeft inputRight left right); [discriminate |].
    unfold rawFormulaAndCode in hinput.
    exact (eq_trans (eq_sym hinput) hinputEq).
  - destruct hor as
      (_ & inputLeft & _ & _ & _ & inputRight & _ & _ &
       _ & _ & _ & _ & _ & _ & hinput & _).
    exfalso. apply (raw_formulaShift_nonzero_binary_neq_eq
      M hPA 4 inputLeft inputRight left right); [discriminate |].
    unfold rawFormulaOrCode in hinput.
    exact (eq_trans (eq_sym hinput) hinputEq).
  - destruct hall as
      (_ & inputChild & _ & _ & _ & _ & _ & hinput & _).
    exfalso. unfold rawFormulaAllCode, rawFormulaEqCode in hinput, hinputEq.
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 5) inputChild
      (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym hinput) hinputEq).
  - destruct hex as
      (_ & inputChild & _ & _ & _ & _ & _ & hinput & _).
    exfalso. unfold rawFormulaExCode, rawFormulaEqCode in hinput, hinputEq.
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 6) inputChild
      (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym hinput) hinputEq).
Qed.

(** Formula shift makes its source atomically adequate as well as its
    target.  The nonstandard term-syntax work is delegated to the already
    proved source-column realization theorem for term shifts. *)
Theorem raw_codedFormulaShift_source_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount input output,
  RawCodedFormulaShift M cutoff amount input output ->
  RawCodedFormulaAtomicallyAdequate M input.
Proof.
  intros M hPA cutoff amount input output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof htrace as htraceForSyntax.
  assert (hsourceSyntax : RawCodedFormulaSyntaxTraversal M
      sourceCode sourceStep bound rootIndex input).
  {
    destruct htraceForSyntax as
      (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
       hrootLookup & hrows).
    repeat split; try assumption.
    - exact (proj1 hrootLookup).
    - intros index code hindex hsourceLookup.
      destruct (htargetDefined index hindex) as [target htargetLookup].
      destruct (hdepthDefined index hindex) as [depth hdepthLookup].
      apply (raw_codedFormulaOperationTraversalRow_source_syntax M
        (RawCodedFormulaShiftAtom M) amount
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        index code target depth).
      apply hrows; [exact hindex |].
      repeat split; assumption.
  }
  exists sourceCode, sourceStep, bound, rootIndex.
  split; [exact hsourceSyntax |].
  intros index code left right assignmentCode assignmentStep
    hindex hsourceLookup hcodeEq hassignment.
  destruct htrace as
    (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
     hrootLookup & hrows).
  destruct (htargetDefined index hindex) as [target htargetLookup].
  destruct (hdepthDefined index hindex) as [depth hdepthLookup].
  pose proof (hrows index code target depth hindex
    (conj hsourceLookup (conj htargetLookup hdepthLookup))) as hrow.
  pose proof (raw_formulaShift_eq_row_of_source M hPA
    amount sourceCode sourceStep targetCode targetStep depthCode depthStep
    index code target depth left right hrow hcodeEq) as heqRow.
  destruct heqRow as
    (sourceLeft & targetLeft & sourceRight & targetRight &
     hsourceEq & htargetEq & hleftShift & hrightShift).
  assert (hsourceFields : sourceLeft = left /\ sourceRight = right).
  {
    unfold rawFormulaEqCode in hsourceEq, hcodeEq.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ (eq_trans (eq_sym hsourceEq) hcodeEq))
      as [_ [hleft hright]]. exact (conj hleft hright).
  }
  destruct hsourceFields as [-> ->]. split.
  - apply (raw_codedTermShift_source_syntax_realizable M hPA
      depth amount left targetLeft assignmentCode assignmentStep code).
    + exact hleftShift.
    + rewrite hcodeEq. exact (raw_formulaShift_eq_left_lt M hPA left right).
    + exact hassignment.
  - apply (raw_codedTermShift_source_syntax_realizable M hPA
      depth amount right targetRight assignmentCode assignmentStep code).
    + exact hrightShift.
    + rewrite hcodeEq. exact (raw_formulaShift_eq_right_lt M hPA left right).
    + exact hassignment.
Qed.

Corollary rawDirectTemplateFormula_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) template,
  RawCodedFormulaAtomicallyAdequate M
    (rawDirectTemplateFormula inputs template).
Proof.
  intros M hPA inputs template.
  pose proof (rawDirectTemplateFormula_shiftAt M hPA inputs 0 template)
    as hshift.
  exact (raw_codedFormulaShift_source_atomically_adequate M hPA
    (rawNumeralValue M 0) (rawNumeralValue M 1)
    (rawDirectTemplateFormula inputs template)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename
        (templateShiftRenamingAt 0) template))
    hshift).
Qed.

(** The exact reusable fold still missing from the library.  It is stated on
    the smallest honest public domain: mere well-formedness is insufficient
    because equality payloads need term-syntax certificates. *)
Definition RawCodedFormulaBoundAtomicallyAdequateTotal
    (M : RawPAModel) : Prop :=
  forall input : M,
    RawCodedFormulaAtomicallyAdequate M input ->
    exists bound : M, RawCodedFormulaBound M input bound.

Arguments RawCodedFormulaBoundAtomicallyAdequateTotal M : clear implicits.

(** The literal template whose direct code is the body passed to the generic
    PA induction compiler. *)
Definition coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate
    : TemplateFormula :=
  tfImp
    (tfAnd
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
      (tfAll
        (tfImp
          coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
          coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate)))
    (tfAll coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate).

Lemma
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode_view
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
    M inputs =
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate.
Proof. reflexivity. Qed.

Corollary
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode_atomically_adequate
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaAtomicallyAdequate M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs).
Proof.
  intros M hPA inputs.
  rewrite
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode_view.
  exact (rawDirectTemplateFormula_atomically_adequate M hPA inputs
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate).
Qed.

(** Assuming precisely the missing global bound fold, the direct remainder
    now chooses both the carrier bound and its sealed closure output. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_exists_of_bound_totality
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaBoundAtomicallyAdequateTotal M ->
  forall (inputs : RawCodedTemplateDirectStructuralInputs M) replacement,
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs) ->
  exists closureCount axiom : M,
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs replacement axiom closureCount.
Proof.
  intros M hPA hboundTotal inputs replacement hdiagonal.
  destruct (hboundTotal
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs)
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode_atomically_adequate
      M hPA inputs)) as [closureCount hbound].
  destruct
    (raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_exists
      M hPA inputs replacement closureCount hbound hdiagonal)
    as [axiom hremainder].
  exists closureCount, axiom. exact hremainder.
Qed.

End PABoundedRawCodedFormulaBoundAllCarrierBoundary.
