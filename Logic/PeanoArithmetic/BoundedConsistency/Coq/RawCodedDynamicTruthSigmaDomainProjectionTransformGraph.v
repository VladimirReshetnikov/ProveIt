(**
  Output-first graph for the full Sigma-row domain projection.

  The graph is read under

      fieldCode :: globalSigmaCode :: globalPiCode :: level :: tail.

  Three witnesses select the represented numeral for [level + 1], the
  corresponding instance of the native Sigma domain, and the native
  three-substitution application of [globalPiCode].  The output is the code
  of the thirteen-times universally closed implication

      full Sigma successor row -> Ex^8 domain.

  Thus this module compiles a genuine eliminator for the complete seven-way
  Sigma row.  It is one positive proof field; it is not the complete local
  decision/exclusivity bundle.

  Exact graph semantics are law free.  Relational totality names only the
  represented domain and lower-application operation interfaces.  Proof
  totality additionally requests direct structural inputs identifying the
  very witnesses selected by the graph, and targets the certificate theorem
  from [RawCodedDynamicTruthSigmaDomainProjectionProofCompilation].
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedFixedLevelTruth
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthUniversalLeafProofCompilation
  RawCodedDynamicTruthSigmaDomainProjectionProofCompilation
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedOutputFirstPairedFormulaGraphComposition
  RawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthSigmaDomainProjectionTransformGraph.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.
Import
  PABoundedRawCodedDynamicTruthSigmaDomainProjectionProofCompilation.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.
Import
  PABoundedRawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph.

(** ------------------------------------------------------------------
    Transparent formula-code polynomial. *)

Definition dynamicTruthSigmaDomainProjectionFormulaAllCodeTerm
    (child : term) : term :=
  codeList2Term (Term.numeral 5) child.

Fixpoint dynamicTruthSigmaDomainProjectionRepeatedAllCodeTerm
    (binderCount : nat) (body : term) : term :=
  match binderCount with
  | 0 => body
  | S smaller =>
      dynamicTruthSigmaDomainProjectionFormulaAllCodeTerm
        (dynamicTruthSigmaDomainProjectionRepeatedAllCodeTerm
          smaller body)
  end.

Definition dynamicTruthSigmaDomainProjectionCodeTerm
    (domain lowerApplication : term) : term :=
  formulaImpCodeTerm
    (dynamicTruthSigmaSuccessorRowCodeTerm domain lowerApplication)
    (formulaEx8CodeTerm domain).

Definition dynamicTruthSigmaDomainProjectionFieldCodeTerm
    (domain lowerApplication : term) : term :=
  dynamicTruthSigmaDomainProjectionRepeatedAllCodeTerm
    coqDynamicTruthSigmaRowEnvironmentArity
    (dynamicTruthSigmaDomainProjectionCodeTerm
      domain lowerApplication).

Lemma raw_eval_dynamicTruthSigmaDomainProjectionFormulaAllCodeTerm :
    forall (M : RawPAModel) e child,
  raw_term_eval M e
    (dynamicTruthSigmaDomainProjectionFormulaAllCodeTerm child) =
  rawFormulaAllCode M (raw_term_eval M e child).
Proof.
  intros M e child.
  unfold dynamicTruthSigmaDomainProjectionFormulaAllCodeTerm,
    rawFormulaAllCode.
  rewrite raw_eval_codeList2Term, raw_term_eval_numeral.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthSigmaDomainProjectionRepeatedAllCodeTerm :
    forall (M : RawPAModel) e binderCount body,
  raw_term_eval M e
    (dynamicTruthSigmaDomainProjectionRepeatedAllCodeTerm
      binderCount body) =
  rawTemplateRepeatedAllCode M binderCount
    (raw_term_eval M e body).
Proof.
  intros M e binderCount.
  induction binderCount as [|smaller ih]; intro body;
    cbn [dynamicTruthSigmaDomainProjectionRepeatedAllCodeTerm
      rawTemplateRepeatedAllCode].
  - reflexivity.
  - change (rawFormulaAllCode M
      (raw_term_eval M e
        (dynamicTruthSigmaDomainProjectionRepeatedAllCodeTerm
          smaller body)) =
      rawFormulaAllCode M
        (rawTemplateRepeatedAllCode M smaller
          (raw_term_eval M e body))).
    now rewrite ih.
Qed.

Lemma raw_eval_dynamicTruthSigmaDomainProjectionCodeTerm : forall
    (M : RawPAModel) e domain lowerApplication,
  raw_term_eval M e
    (dynamicTruthSigmaDomainProjectionCodeTerm
      domain lowerApplication) =
  rawDynamicTruthSigmaDomainProjectionCode M
    (raw_term_eval M e domain)
    (raw_term_eval M e lowerApplication).
Proof.
  intros M e domain lowerApplication.
  unfold dynamicTruthSigmaDomainProjectionCodeTerm,
    rawDynamicTruthSigmaDomainProjectionCode.
  rewrite raw_eval_formulaImpCodeTerm,
    raw_eval_dynamicTruthSigmaSuccessorRowCodeTerm,
    raw_eval_formulaEx8CodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthSigmaDomainProjectionFieldCodeTerm : forall
    (M : RawPAModel) e domain lowerApplication,
  raw_term_eval M e
    (dynamicTruthSigmaDomainProjectionFieldCodeTerm
      domain lowerApplication) =
  rawDynamicTruthSigmaDomainProjectionFieldCode M
    (raw_term_eval M e domain)
    (raw_term_eval M e lowerApplication).
Proof.
  intros M e domain lowerApplication.
  unfold dynamicTruthSigmaDomainProjectionFieldCodeTerm,
    rawDynamicTruthSigmaDomainProjectionFieldCode.
  rewrite
    raw_eval_dynamicTruthSigmaDomainProjectionRepeatedAllCodeTerm,
    raw_eval_dynamicTruthSigmaDomainProjectionCodeTerm.
  reflexivity.
Qed.

Definition dynamicTruthSigmaDomainProjectionFieldCodeTermAt
    (output domain lowerApplication : term) : formula :=
  pEq output
    (dynamicTruthSigmaDomainProjectionFieldCodeTerm
      domain lowerApplication).

Lemma raw_sat_dynamicTruthSigmaDomainProjectionFieldCodeTermAt_iff :
    forall (M : RawPAModel) e output domain lowerApplication,
  raw_formula_sat M e
    (dynamicTruthSigmaDomainProjectionFieldCodeTermAt
      output domain lowerApplication) <->
  raw_term_eval M e output =
    rawDynamicTruthSigmaDomainProjectionFieldCode M
      (raw_term_eval M e domain)
      (raw_term_eval M e lowerApplication).
Proof.
  intros M e output domain lowerApplication.
  unfold dynamicTruthSigmaDomainProjectionFieldCodeTermAt.
  change (raw_term_eval M e output =
      raw_term_eval M e
        (dynamicTruthSigmaDomainProjectionFieldCodeTerm
          domain lowerApplication) <->
    raw_term_eval M e output =
      rawDynamicTruthSigmaDomainProjectionFieldCode M
        (raw_term_eval M e domain)
        (raw_term_eval M e lowerApplication)).
  rewrite raw_eval_dynamicTruthSigmaDomainProjectionFieldCodeTerm.
  reflexivity.
Qed.

(** Keep the already verified thirteen-quantifier code polynomial folded
    while the surrounding existential graph is simplified. *)
Opaque dynamicTruthSigmaDomainProjectionFieldCodeTerm.

(** ------------------------------------------------------------------
    Output-first transform graph and law-free semantics.

    Beneath the three witnesses the environment is

      lowerApplication :: domain :: upperNumeral ::
      fieldCode :: globalSigmaCode :: globalPiCode :: level :: tail.
*)

Definition dynamicTruthSigmaDomainProjectionFieldTransformGraph : formula :=
  pEx (pEx (pEx
    (fixedLevelAnd4
      (numeralTermCodeAtTermAt (tSucc (tVar 6)) (tVar 2))
      (codedFormulaSingleSubstitutionTermAt
        (tVar 2)
        (Term.numeral dynamicTruthSigmaRowDomainTemplateCode)
        (tVar 1))
      (dynamicTruthCoqLowerApplicationTermAt (tVar 5) (tVar 0))
      (dynamicTruthSigmaDomainProjectionFieldCodeTermAt
        (tVar 3) (tVar 1) (tVar 0))))).

Definition RawDynamicTruthSigmaDomainProjectionFieldTransformAt
    (M : RawPAModel)
    (globalSigmaCode globalPiCode level fieldCode : M) : Prop :=
  exists upperNumeral domain lowerApplication : M,
    RawNumeralTermCodeAt M (raw_succ M level) upperNumeral /\
    RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode) domain /\
    RawDynamicTruthCoqLowerApplication M
      globalPiCode lowerApplication /\
    fieldCode =
      rawDynamicTruthSigmaDomainProjectionFieldCode M
        domain lowerApplication.

Arguments RawDynamicTruthSigmaDomainProjectionFieldTransformAt
  M globalSigmaCode globalPiCode level fieldCode : clear implicits.

Local Opaque dynamicTruthCoqLowerApplicationTermAt.

Theorem raw_sat_dynamicTruthSigmaDomainProjectionFieldTransformGraph_iff :
    forall (M : RawPAModel) tail
      globalSigmaCode globalPiCode level fieldCode,
  raw_formula_sat M
    (scons M fieldCode
      (scons M globalSigmaCode
        (scons M globalPiCode (scons M level tail))))
    dynamicTruthSigmaDomainProjectionFieldTransformGraph <->
  RawDynamicTruthSigmaDomainProjectionFieldTransformAt M
    globalSigmaCode globalPiCode level fieldCode.
Proof.
  intros M tail globalSigmaCode globalPiCode level fieldCode.
  unfold dynamicTruthSigmaDomainProjectionFieldTransformGraph,
    RawDynamicTruthSigmaDomainProjectionFieldTransformAt,
    fixedLevelAnd4.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_numeralTermCodeAtTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  setoid_rewrite raw_sat_dynamicTruthCoqLowerApplicationTermAt_iff.
  setoid_rewrite
    raw_sat_dynamicTruthSigmaDomainProjectionFieldCodeTermAt_iff.
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
        (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
        domain).
    {
      change (RawCodedFormulaSingleSubstitution M upperNumeral
        (raw_term_eval M
          (scons M lowerApplication
            (scons M domain
              (scons M upperNumeral
                (scons M fieldCode
                  (scons M globalSigmaCode
                    (scons M globalPiCode (scons M level tail)))))))
          (Term.numeral dynamicTruthSigmaRowDomainTemplateCode))
        domain) in hdomain.
      rewrite raw_term_eval_numeral in hdomain.
      exact hdomain.
    }
    assert (hlower' : RawDynamicTruthCoqLowerApplication M
        globalPiCode lowerApplication).
    {
      change (RawDynamicTruthCoqLowerApplication M
        globalPiCode lowerApplication) in hlower.
      exact hlower.
    }
    assert (hfield' : fieldCode =
        rawDynamicTruthSigmaDomainProjectionFieldCode M
          domain lowerApplication).
    {
      change (fieldCode =
        rawDynamicTruthSigmaDomainProjectionFieldCode M
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
          (Term.numeral dynamicTruthSigmaRowDomainTemplateCode))
        domain).
      rewrite raw_term_eval_numeral. exact hdomain.
    + change (RawDynamicTruthCoqLowerApplication M
        globalPiCode lowerApplication).
      exact hlower.
    + change (fieldCode =
        rawDynamicTruthSigmaDomainProjectionFieldCode M
          domain lowerApplication).
      exact hfield.
Qed.

(** ------------------------------------------------------------------
    Relational totality from the native operation premises. *)

Definition RawDynamicTruthSigmaDomainProjectionFieldTransformTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) globalSigmaCode globalPiCode level,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode
          (scons M globalSigmaCode
            (scons M globalPiCode (scons M level tail))))
        dynamicTruthSigmaDomainProjectionFieldTransformGraph.

Arguments RawDynamicTruthSigmaDomainProjectionFieldTransformTotal M
  : clear implicits.

Theorem dynamicTruthSigmaDomainProjectionFieldTransformGraph_raw_total :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaDomainStepTotal M ->
  RawDynamicTruthCoqLowerApplicationTotal M ->
  RawDynamicTruthSigmaDomainProjectionFieldTransformTotal M.
Proof.
  intros M hPA hdomain hlower tail
    globalSigmaCode globalPiCode level.
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (hdomain level upperNumeral hupperNumeral)
    as [domain hdomainWitness].
  destruct (hlower globalPiCode)
    as [lowerApplication hlowerApplication].
  exists (rawDynamicTruthSigmaDomainProjectionFieldCode M
    domain lowerApplication).
  apply (proj2
    (raw_sat_dynamicTruthSigmaDomainProjectionFieldTransformGraph_iff
      M tail globalSigmaCode globalPiCode level _)).
  exists upperNumeral, domain, lowerApplication.
  repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Direct compiler availability and proof-producing totality.

    The premise retains structural operation traces, not merely their output
    equalities.  Those traces are the data consumed by the direct template
    translator and are shared with the restricted universal compiler. *)

Definition RawDynamicTruthSigmaDomainProjectionDirectCompilerTotal
    (M : RawPAModel) : Prop :=
  forall globalPiCode level upperNumeral domain lowerApplication,
    RawNumeralTermCodeAt M (raw_succ M level) upperNumeral ->
    RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode) domain ->
    RawDynamicTruthCoqLowerApplication M
      globalPiCode lowerApplication ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
      RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
        domain lowerApplication.

Arguments RawDynamicTruthSigmaDomainProjectionDirectCompilerTotal M
  : clear implicits.

Theorem
    dynamicTruthSigmaDomainProjectionFieldTransformGraph_raw_proof_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceGraph,
  RawDynamicTruthSigmaDomainStepTotal M ->
  RawDynamicTruthCoqLowerApplicationTotal M ->
  RawDynamicTruthSigmaDomainProjectionDirectCompilerTotal M ->
  RawOutputFirstPairedFormulaTransformProofTotal M sourceGraph
    dynamicTruthSigmaDomainProjectionFieldTransformGraph.
Proof.
  intros M hPA sourceGraph hdomain hlower hcompiler
    tail level globalSigmaCode globalPiCode _hsource.
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (hdomain level upperNumeral hupperNumeral)
    as [domain hdomainWitness].
  destruct (hlower globalPiCode)
    as [lowerApplication hlowerApplication].
  destruct (hcompiler globalPiCode level upperNumeral
    domain lowerApplication hupperNumeral hdomainWitness
    hlowerApplication) as [inputs identification].
  exists (rawDynamicTruthSigmaDomainProjectionFieldCode M
      domain lowerApplication),
    (rawCoqDynamicTruthSigmaDomainProjectionFieldCertificate
      M hPA inputs).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthSigmaDomainProjectionFieldTransformGraph_iff
        M tail globalSigmaCode globalPiCode level _)).
    exists upperNumeral, domain, lowerApplication.
    repeat split; assumption.
  - exact
      (raw_codedPAProofOf_dynamicTruthSigmaDomainProjectionField_identified
        M hPA inputs domain lowerApplication identification).
Qed.

(** ------------------------------------------------------------------
    Composition with the paired global orbit.

    The exposed level is the predecessor level: the transform selects its
    successor numeral and compiles the corresponding positive Sigma-row
    projection.  Both hidden global polarity codes come from one paired
    orbit witness. *)

Definition dynamicTruthSigmaDomainProjectionPositiveFieldGraph : formula :=
  outputFirstPairedFormulaGraphComposition
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph
    dynamicTruthSigmaDomainProjectionFieldTransformGraph.

Definition RawDynamicTruthSigmaDomainProjectionPositiveFieldAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel fieldCode : M) : Prop :=
  exists globalSigmaCode globalPiCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail predecessorLevel globalSigmaCode globalPiCode /\
    RawDynamicTruthSigmaDomainProjectionFieldTransformAt M
      globalSigmaCode globalPiCode predecessorLevel fieldCode.

Arguments RawDynamicTruthSigmaDomainProjectionPositiveFieldAt
  M tail predecessorLevel fieldCode : clear implicits.

Theorem raw_sat_dynamicTruthSigmaDomainProjectionPositiveFieldGraph_iff :
    forall (M : RawPAModel) tail predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M predecessorLevel tail))
    dynamicTruthSigmaDomainProjectionPositiveFieldGraph <->
  RawDynamicTruthSigmaDomainProjectionPositiveFieldAt M
    tail predecessorLevel fieldCode.
Proof.
  intros M tail predecessorLevel fieldCode.
  unfold dynamicTruthSigmaDomainProjectionPositiveFieldGraph,
    RawDynamicTruthSigmaDomainProjectionPositiveFieldAt.
  rewrite raw_sat_outputFirstPairedFormulaGraphComposition_iff.
  unfold RawOutputFirstPairedFormulaGraphCompositionAt.
  split.
  - intros (globalSigmaCode & globalPiCode & horbit & htransform).
    exists globalSigmaCode, globalPiCode. split.
    + apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail predecessorLevel globalSigmaCode globalPiCode)).
      exact horbit.
    + apply (proj1
        (raw_sat_dynamicTruthSigmaDomainProjectionFieldTransformGraph_iff
          M tail globalSigmaCode globalPiCode predecessorLevel fieldCode)).
      exact htransform.
  - intros (globalSigmaCode & globalPiCode & horbit & htransform).
    exists globalSigmaCode, globalPiCode. split.
    + apply (proj2
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail predecessorLevel globalSigmaCode globalPiCode)).
      exact horbit.
    + apply (proj2
        (raw_sat_dynamicTruthSigmaDomainProjectionFieldTransformGraph_iff
          M tail globalSigmaCode globalPiCode predecessorLevel fieldCode)).
      exact htransform.
Qed.

Definition RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode certificate : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthSigmaDomainProjectionPositiveFieldGraph /\
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal M
  : clear implicits.

Theorem dynamicTruthSigmaDomainProjectionPositiveFieldGraph_raw_proof_total :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaDomainStepTotal M ->
  RawDynamicTruthCoqLowerApplicationTotal M ->
  RawDynamicTruthSigmaDomainProjectionDirectCompilerTotal M ->
  RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA hdomain hlower hcompiler.
  unfold RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal,
    dynamicTruthSigmaDomainProjectionPositiveFieldGraph.
  apply (outputFirstPairedFormulaGraphComposition_raw_proof_total M
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph
    dynamicTruthSigmaDomainProjectionFieldTransformGraph).
  - intros tail predecessorLevel.
    destruct
      (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
        M hPA tail predecessorLevel) as
      (globalSigmaCode & globalPiCode & horbit & _ & _).
    exists globalSigmaCode, globalPiCode. exact horbit.
  - exact
      (dynamicTruthSigmaDomainProjectionFieldTransformGraph_raw_proof_total
        M hPA dynamicTruthPairedGlobalFormulaCodeOrbitGraph
        hdomain hlower hcompiler).
Qed.

(** The direct structural inputs used for the restricted universal field and
    for this full-row projection are literally the same inputs: both identify
    the selected native Sigma domain and lower-Pi application.  The existing
    orbit-refined compiler interface can therefore be reused without adding
    any operation law for carrier codes outside the chosen paired orbit. *)
Definition RawDynamicTruthSigmaDomainProjectionOrbitDirectCompilerTotal
    (M : RawPAModel) : Prop :=
  RawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal M.

Arguments
  RawDynamicTruthSigmaDomainProjectionOrbitDirectCompilerTotal M
  : clear implicits.

(** Adequacy of the actual orbit witness supplies the two native operation
    outputs.  This is strictly sharper than the preceding compatibility
    theorem, which assumes total operations and a compiler for every carrier
    input. *)
Theorem
    dynamicTruthSigmaDomainProjectionPositiveFieldGraph_raw_adequate_proof_total
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaDomainProjectionOrbitDirectCompilerTotal M ->
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode certificate globalSigmaCode globalPiCode : M,
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail predecessorLevel globalSigmaCode globalPiCode /\
      RawDynamicTruthSigmaDomainProjectionFieldTransformAt M
        globalSigmaCode globalPiCode predecessorLevel fieldCode /\
      RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA hcompiler tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail predecessorLevel) as
    (globalSigmaCode & globalPiCode & horbit & hsigmaAdequate &
     hpiAdequate).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail predecessorLevel globalSigmaCode globalPiCode).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail predecessorLevel globalSigmaCode globalPiCode)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail predecessorLevel globalSigmaCode globalPiCode)).
      exact horbit.
    - split; assumption.
  }
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M predecessorLevel)) as
    [upperNumeral hupperNumeral].
  destruct (raw_dynamicTruthSigmaDomain_exists_adequate M hPA
    predecessorLevel upperNumeral hupperNumeral) as
    (domain & hdomainWitness & _hdomainAdequate).
  destruct (raw_dynamicTruthSigmaLower_exists_adequate M hPA
    globalPiCode hpiAdequate) as
    (lowerApplication & hlowerApplication & _hlowerAdequate).
  destruct (hcompiler tail predecessorLevel globalSigmaCode globalPiCode
    hadequateOrbit upperNumeral domain lowerApplication
    hupperNumeral hdomainWitness hlowerApplication) as
    [inputs identification].
  exists
    (rawDynamicTruthSigmaDomainProjectionFieldCode M
      domain lowerApplication),
    (rawCoqDynamicTruthSigmaDomainProjectionFieldCertificate
      M hPA inputs),
    globalSigmaCode, globalPiCode.
  split.
  - exact hadequateOrbit.
  - split.
    + exists upperNumeral, domain, lowerApplication.
      repeat split; try assumption; reflexivity.
    + exact
        (raw_codedPAProofOf_dynamicTruthSigmaDomainProjectionField_identified
          M hPA inputs domain lowerApplication identification).
Qed.

Theorem
    dynamicTruthSigmaDomainProjectionPositiveFieldGraph_raw_proof_total_of_orbit_direct_compiler
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaDomainProjectionOrbitDirectCompilerTotal M ->
  RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA hcompiler tail predecessorLevel.
  destruct
    (dynamicTruthSigmaDomainProjectionPositiveFieldGraph_raw_adequate_proof_total
      M hPA hcompiler tail predecessorLevel) as
    (fieldCode & certificate & globalSigmaCode & globalPiCode &
     hadequateOrbit & htransform & hcertificate).
  exists fieldCode, certificate. split; [|exact hcertificate].
  apply (proj2
    (raw_sat_dynamicTruthSigmaDomainProjectionPositiveFieldGraph_iff
      M tail predecessorLevel fieldCode)).
  exists globalSigmaCode, globalPiCode. split; [|exact htransform].
  apply (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail predecessorLevel globalSigmaCode globalPiCode)).
  exact hadequateOrbit.
Qed.

(** Strongest concrete interface exported here.  The existing selector
    construction converts shift/opening interchange on the actual orbit Pi
    code into direct inputs; the full-row compiler then reuses those inputs
    to emit the domain-projection certificate. *)
Corollary
    dynamicTruthSigmaDomainProjectionPositiveFieldGraph_raw_proof_total_of_orbit_interchange
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalOrbitTernaryInterchangeTotal M ->
  RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA hinterchange.
  apply
    dynamicTruthSigmaDomainProjectionPositiveFieldGraph_raw_proof_total_of_orbit_direct_compiler;
    [exact hPA |].
  unfold RawDynamicTruthSigmaDomainProjectionOrbitDirectCompilerTotal.
  exact
    (rawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal_of_interchange
      M hPA hinterchange).
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaDomainProjectionTransformGraph.
