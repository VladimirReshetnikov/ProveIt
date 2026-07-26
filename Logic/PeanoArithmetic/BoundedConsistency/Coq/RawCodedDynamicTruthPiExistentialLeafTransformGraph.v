(**
  Output-first graph for the restricted Pi/existential proof field.

  The graph is evaluated under

      fieldCode :: globalSigmaCode :: globalPiCode :: level :: tail.

  Three witnesses select a numeral term for [level + 1], the corresponding
  instance of the native Pi-domain template, and the three-substitution
  application of [globalSigmaCode].  The final transparent equality builds
  the thirteen-times universally closed code compiled in
  [RawCodedDynamicTruthPiExistentialLeafProofCompilation].

  Relational graph totality and proof-producing totality remain separate.
  The former needs only the native Pi domain/application operations.  The
  latter additionally requires direct structural inputs whose opaque traces
  identify exactly those witnesses; equality of output codes is never used
  to invent a shift or opening trace.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedFixedLevelTruth
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthPiExistentialLeafProofCompilation
  RawCodedDynamicTruthUniversalLeafProofCompilation
  RawCodedDynamicTruthUniversalLeafTransformGraph
  RawCodedOutputFirstPairedFormulaGraphComposition.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthPiExistentialLeafTransformGraph.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPiExistentialLeafProofCompilation.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.
Import PABoundedRawCodedDynamicTruthUniversalLeafTransformGraph.
Import PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.

(** ------------------------------------------------------------------
    Transparent code polynomial for the closed restricted projection. *)

Definition dynamicTruthPiRestrictedExistentialProjectionCodeTerm
    (domain lowerApplication : term) : term :=
  let existentialLeaf :=
    dynamicTruthPiExistentialCodeTerm lowerApplication in
  dynamicTruthPiFormulaImpCodeTerm
    (dynamicTruthPiFormulaEx8CodeTerm
      (dynamicTruthPiFormulaAndCodeTerm domain existentialLeaf))
    (dynamicTruthPiFormulaEx8CodeTerm existentialLeaf).

Definition dynamicTruthPiRestrictedExistentialFieldCodeTerm
    (domain lowerApplication : term) : term :=
  restrictedUniversalRepeatedAllCodeTerm
    coqDynamicTruthPiRowEnvironmentArity
    (dynamicTruthPiRestrictedExistentialProjectionCodeTerm
      domain lowerApplication).

Definition rawDynamicTruthPiRestrictedExistentialProjectionGraphCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  let existentialLeaf :=
    rawDynamicTruthPiExistentialCode M lowerApplication in
  rawFormulaImpCode M
    (rawDynamicTruthPiFormulaEx8Code M
      (rawFormulaAndCode M domain existentialLeaf))
    (rawDynamicTruthPiFormulaEx8Code M existentialLeaf).

Definition rawDynamicTruthPiRestrictedExistentialFieldGraphCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawTemplateRepeatedAllCode M
    coqDynamicTruthPiRowEnvironmentArity
    (rawDynamicTruthPiRestrictedExistentialProjectionGraphCode M
      domain lowerApplication).

Lemma raw_eval_dynamicTruthPiRestrictedExistentialProjectionCodeTerm :
  forall (M : RawPAModel) e domain lowerApplication,
  raw_term_eval M e
    (dynamicTruthPiRestrictedExistentialProjectionCodeTerm
      domain lowerApplication) =
  rawDynamicTruthPiRestrictedExistentialProjectionGraphCode M
    (raw_term_eval M e domain)
    (raw_term_eval M e lowerApplication).
Proof.
  intros M e domain lowerApplication.
  unfold dynamicTruthPiRestrictedExistentialProjectionCodeTerm,
    rawDynamicTruthPiRestrictedExistentialProjectionGraphCode.
  rewrite raw_eval_dynamicTruthPiFormulaImpCodeTerm,
    !raw_eval_dynamicTruthPiFormulaEx8CodeTerm,
    raw_eval_dynamicTruthPiFormulaAndCodeTerm,
    !raw_eval_dynamicTruthPiExistentialCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiRestrictedExistentialFieldCodeTerm : forall
    (M : RawPAModel) e domain lowerApplication,
  raw_term_eval M e
    (dynamicTruthPiRestrictedExistentialFieldCodeTerm
      domain lowerApplication) =
  rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
    (raw_term_eval M e domain)
    (raw_term_eval M e lowerApplication).
Proof.
  intros M e domain lowerApplication.
  unfold dynamicTruthPiRestrictedExistentialFieldCodeTerm,
    rawDynamicTruthPiRestrictedExistentialFieldGraphCode.
  rewrite raw_eval_restrictedUniversalRepeatedAllCodeTerm,
    raw_eval_dynamicTruthPiRestrictedExistentialProjectionCodeTerm.
  reflexivity.
Qed.

Definition dynamicTruthPiRestrictedExistentialFieldCodeTermAt
    (output domain lowerApplication : term) : formula :=
  pEq output
    (dynamicTruthPiRestrictedExistentialFieldCodeTerm
      domain lowerApplication).

Lemma raw_sat_dynamicTruthPiRestrictedExistentialFieldCodeTermAt_iff :
  forall (M : RawPAModel) e output domain lowerApplication,
  raw_formula_sat M e
    (dynamicTruthPiRestrictedExistentialFieldCodeTermAt
      output domain lowerApplication) <->
  raw_term_eval M e output =
    rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
      (raw_term_eval M e domain)
      (raw_term_eval M e lowerApplication).
Proof.
  intros M e output domain lowerApplication.
  unfold dynamicTruthPiRestrictedExistentialFieldCodeTermAt.
  change (raw_term_eval M e output =
      raw_term_eval M e
        (dynamicTruthPiRestrictedExistentialFieldCodeTerm
          domain lowerApplication) <->
    raw_term_eval M e output =
      rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
        (raw_term_eval M e domain)
        (raw_term_eval M e lowerApplication)).
  rewrite raw_eval_dynamicTruthPiRestrictedExistentialFieldCodeTerm.
  reflexivity.
Qed.

(** The graph uses fixed numeral leaves, whereas the source compiler uses
    structural quotations.  PA identifies the two presentations. *)
Lemma rawDynamicTruthPiExistentialCode_eq_directTemplateCode : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  rawDynamicTruthPiExistentialCode M lowerApplication =
  rawCoqDynamicTruthPiExistentialLeafTemplateCode M lowerApplication.
Proof.
  intros M hPA lowerApplication.
  unfold rawDynamicTruthPiExistentialCode,
    rawDynamicTruthPiNoBinderCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode.
  rewrite !rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Theorem rawDynamicTruthPiRestrictedExistentialFieldGraphCode_eq_compiled :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    domain lowerApplication,
  rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
    domain lowerApplication =
  rawCoqDynamicTruthPiRestrictedExistentialFieldCode M
    domain lowerApplication.
Proof.
  intros M hPA domain lowerApplication.
  unfold rawDynamicTruthPiRestrictedExistentialFieldGraphCode,
    rawDynamicTruthPiRestrictedExistentialProjectionGraphCode,
    rawCoqDynamicTruthPiRestrictedExistentialFieldCode,
    rawCoqDynamicTruthPiRestrictedExistentialProjectionCode.
  rewrite (rawDynamicTruthPiExistentialCode_eq_directTemplateCode
    M hPA lowerApplication).
  reflexivity.
Qed.

Opaque dynamicTruthPiRestrictedExistentialFieldCodeTerm.

(** ------------------------------------------------------------------
    Output-first graph and exact arbitrary-model semantics.

    Beneath the three witnesses the environment is

      lowerApplication :: domain :: upperNumeral ::
      fieldCode :: globalSigmaCode :: globalPiCode :: level :: tail.
*)

Definition dynamicTruthPiRestrictedExistentialFieldTransformGraph
    : formula :=
  pEx (pEx (pEx
    (fixedLevelAnd4
      (numeralTermCodeAtTermAt (tSucc (tVar 6)) (tVar 2))
      (codedFormulaSingleSubstitutionTermAt
        (tVar 2)
        (Term.numeral (formulaCode dynamicTruthPiRowDomainTemplate))
        (tVar 1))
      (dynamicTruthPiCoqLowerApplicationTermAt (tVar 4) (tVar 0))
      (dynamicTruthPiRestrictedExistentialFieldCodeTermAt
        (tVar 3) (tVar 1) (tVar 0))))).

Definition RawDynamicTruthPiRestrictedExistentialFieldTransformAt
    (M : RawPAModel)
    (globalSigmaCode globalPiCode level fieldCode : M) : Prop :=
  exists upperNumeral domain lowerApplication : M,
    RawNumeralTermCodeAt M (raw_succ M level) upperNumeral /\
    RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthPiRowDomainTemplate)) domain /\
    RawDynamicTruthPiCoqLowerApplication M
      globalSigmaCode lowerApplication /\
    fieldCode =
      rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
        domain lowerApplication.

Arguments RawDynamicTruthPiRestrictedExistentialFieldTransformAt
  M globalSigmaCode globalPiCode level fieldCode : clear implicits.

Local Opaque dynamicTruthPiCoqLowerApplicationTermAt.

Theorem raw_sat_dynamicTruthPiRestrictedExistentialFieldTransformGraph_iff :
  forall (M : RawPAModel) tail
    globalSigmaCode globalPiCode level fieldCode,
  raw_formula_sat M
    (scons M fieldCode
      (scons M globalSigmaCode
        (scons M globalPiCode (scons M level tail))))
    dynamicTruthPiRestrictedExistentialFieldTransformGraph <->
  RawDynamicTruthPiRestrictedExistentialFieldTransformAt M
    globalSigmaCode globalPiCode level fieldCode.
Proof.
  intros M tail globalSigmaCode globalPiCode level fieldCode.
  unfold dynamicTruthPiRestrictedExistentialFieldTransformGraph,
    RawDynamicTruthPiRestrictedExistentialFieldTransformAt,
    fixedLevelAnd4.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_numeralTermCodeAtTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  setoid_rewrite raw_sat_dynamicTruthPiCoqLowerApplicationTermAt_iff.
  setoid_rewrite
    raw_sat_dynamicTruthPiRestrictedExistentialFieldCodeTermAt_iff.
  split.
  - intros (upperNumeral & domain & lowerApplication &
      hupper & hdomain & hlower & hfield).
    exists upperNumeral, domain, lowerApplication.
    assert (hupper' : RawNumeralTermCodeAt M
        (raw_succ M level) upperNumeral).
    {
      change (RawNumeralTermCodeAt M
        (raw_succ M level) upperNumeral) in hupper.
      exact hupper.
    }
    assert (hdomain' : RawCodedFormulaSingleSubstitution M
        upperNumeral
        (rawNumeralValue M
          (formulaCode dynamicTruthPiRowDomainTemplate)) domain).
    {
      change (RawCodedFormulaSingleSubstitution M upperNumeral
        (raw_term_eval M
          (scons M lowerApplication
            (scons M domain
              (scons M upperNumeral
                (scons M fieldCode
                  (scons M globalSigmaCode
                    (scons M globalPiCode (scons M level tail)))))))
          (Term.numeral
            (formulaCode dynamicTruthPiRowDomainTemplate)))
        domain) in hdomain.
      rewrite raw_term_eval_numeral in hdomain.
      exact hdomain.
    }
    assert (hlower' : RawDynamicTruthPiCoqLowerApplication M
        globalSigmaCode lowerApplication).
    {
      change (RawDynamicTruthPiCoqLowerApplication M
        globalSigmaCode lowerApplication) in hlower.
      exact hlower.
    }
    assert (hfield' : fieldCode =
        rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
          domain lowerApplication).
    {
      change (fieldCode =
        rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
          domain lowerApplication) in hfield.
      exact hfield.
    }
    repeat split; assumption.
  - intros (upperNumeral & domain & lowerApplication &
      hupper & hdomain & hlower & hfield).
    exists upperNumeral, domain, lowerApplication.
    repeat split.
    + change (RawNumeralTermCodeAt M
        (raw_succ M level) upperNumeral).
      exact hupper.
    + change (RawCodedFormulaSingleSubstitution M upperNumeral
        (raw_term_eval M
          (scons M lowerApplication
            (scons M domain
              (scons M upperNumeral
                (scons M fieldCode
                  (scons M globalSigmaCode
                    (scons M globalPiCode (scons M level tail)))))))
          (Term.numeral
            (formulaCode dynamicTruthPiRowDomainTemplate)))
        domain).
      rewrite raw_term_eval_numeral. exact hdomain.
    + change (RawDynamicTruthPiCoqLowerApplication M
        globalSigmaCode lowerApplication).
      exact hlower.
    + change (fieldCode =
        rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
          domain lowerApplication).
      exact hfield.
Qed.

(** ------------------------------------------------------------------
    Relational and proof-producing totality. *)

Definition RawDynamicTruthPiRestrictedExistentialFieldTransformTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) globalSigmaCode globalPiCode level,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode
          (scons M globalSigmaCode
            (scons M globalPiCode (scons M level tail))))
        dynamicTruthPiRestrictedExistentialFieldTransformGraph.

Arguments RawDynamicTruthPiRestrictedExistentialFieldTransformTotal M
  : clear implicits.

Theorem dynamicTruthPiRestrictedExistentialFieldTransformGraph_raw_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiDomainStepTotal M ->
  RawDynamicTruthPiCoqLowerApplicationTotal M ->
  RawDynamicTruthPiRestrictedExistentialFieldTransformTotal M.
Proof.
  intros M hPA hdomain hlower tail
    globalSigmaCode globalPiCode level.
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (hdomain level upperNumeral hupperNumeral)
    as [domain hdomainWitness].
  destruct (hlower globalSigmaCode)
    as [lowerApplication hlowerApplication].
  exists (rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
    domain lowerApplication).
  apply (proj2
    (raw_sat_dynamicTruthPiRestrictedExistentialFieldTransformGraph_iff
      M tail globalSigmaCode globalPiCode level _)).
  exists upperNumeral, domain, lowerApplication.
  repeat split; assumption.
Qed.

(** Direct compiler availability for the exact three graph witnesses. *)
Definition RawDynamicTruthPiRestrictedExistentialDirectCompilerTotal
    (M : RawPAModel) : Prop :=
  forall globalSigmaCode level upperNumeral domain lowerApplication,
    RawNumeralTermCodeAt M (raw_succ M level) upperNumeral ->
    RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthPiRowDomainTemplate)) domain ->
    RawDynamicTruthPiCoqLowerApplication M
      globalSigmaCode lowerApplication ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
      RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
        domain lowerApplication.

Arguments RawDynamicTruthPiRestrictedExistentialDirectCompilerTotal M
  : clear implicits.

Theorem
    dynamicTruthPiRestrictedExistentialFieldTransformGraph_raw_proof_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceGraph,
  RawDynamicTruthPiDomainStepTotal M ->
  RawDynamicTruthPiCoqLowerApplicationTotal M ->
  RawDynamicTruthPiRestrictedExistentialDirectCompilerTotal M ->
  RawOutputFirstPairedFormulaTransformProofTotal M sourceGraph
    dynamicTruthPiRestrictedExistentialFieldTransformGraph.
Proof.
  intros M hPA sourceGraph hdomain hlower hcompiler
    tail level globalSigmaCode globalPiCode _hsource.
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (hdomain level upperNumeral hupperNumeral)
    as [domain hdomainWitness].
  destruct (hlower globalSigmaCode)
    as [lowerApplication hlowerApplication].
  destruct (hcompiler globalSigmaCode level upperNumeral
    domain lowerApplication hupperNumeral hdomainWitness
    hlowerApplication) as [inputs identification].
  exists (rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
      domain lowerApplication),
    (rawCoqDynamicTruthPiRestrictedExistentialFieldCertificate
      M hPA inputs).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthPiRestrictedExistentialFieldTransformGraph_iff
        M tail globalSigmaCode globalPiCode level _)).
    exists upperNumeral, domain, lowerApplication.
    repeat split; assumption.
  - rewrite
      (rawDynamicTruthPiRestrictedExistentialFieldGraphCode_eq_compiled
        M hPA domain lowerApplication).
    exact
      (raw_codedPAProofOf_coqDynamicTruthPiRestrictedExistentialField_identified
        M hPA inputs domain lowerApplication identification).
Qed.

End PABoundedRawCodedDynamicTruthPiExistentialLeafTransformGraph.
