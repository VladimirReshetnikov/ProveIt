(**
  Output-first graph for the full Pi-row domain projection.

  The graph is read under

      fieldCode :: globalSigmaCode :: globalPiCode :: level :: tail.

  Three witnesses select the represented numeral for [level + 1], the
  corresponding instance of the native Pi domain, and the native
  three-substitution application of [globalSigmaCode].  The output is the
  code of the thirteen-times universally closed implication

      full Pi successor row -> Ex^8 domain.

  Thus this module compiles a genuine eliminator for the complete six-way
  Pi row.  It is one positive proof field; it is not the complete local
  decision/exclusivity bundle.

  Exact graph semantics are law free.  Relational totality names only the
  represented domain and lower-application operation interfaces.  Proof
  totality additionally requests direct structural inputs identifying the
  very witnesses selected by the graph, and targets the certificate theorem
  from [RawCodedDynamicTruthPiDomainProjectionProofCompilation].
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedPAProvability
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
  RawCodedDynamicTruthPiDomainProjectionProofCompilation
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedOutputFirstPairedFormulaGraphComposition
  RawCodedDynamicTruthRestrictedExistentialLocalProofFieldGraph.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthPiDomainProjectionTransformGraph.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedPAProvability.
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
Import PABoundedRawCodedDynamicTruthPiDomainProjectionProofCompilation.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.
Import
  PABoundedRawCodedDynamicTruthRestrictedExistentialLocalProofFieldGraph.

(** ------------------------------------------------------------------
    Transparent formula-code polynomial. *)

(** This private repeated-universal constructor is kept local to the Pi
    projection instead of borrowing a code term from another proof field.
    Its evaluation theorem below pins it directly to
    [rawTemplateRepeatedAllCode]. *)
Definition dynamicTruthPiDomainProjectionFormulaAllCodeTerm
    (child : term) : term :=
  dynamicTruthPiFormulaAllCodeTerm child.

Fixpoint dynamicTruthPiDomainProjectionRepeatedAllCodeTerm
    (binderCount : nat) (body : term) : term :=
  match binderCount with
  | 0 => body
  | S smaller =>
      dynamicTruthPiDomainProjectionFormulaAllCodeTerm
        (dynamicTruthPiDomainProjectionRepeatedAllCodeTerm smaller body)
  end.

Definition dynamicTruthPiDomainProjectionCodeTerm
    (domain lowerApplication : term) : term :=
  dynamicTruthPiFormulaImpCodeTerm
    (dynamicTruthPiSuccessorRowCodeTerm domain lowerApplication)
    (dynamicTruthPiFormulaEx8CodeTerm domain).

Definition dynamicTruthPiDomainProjectionFieldCodeTerm
    (domain lowerApplication : term) : term :=
  dynamicTruthPiDomainProjectionRepeatedAllCodeTerm
    coqDynamicTruthPiRowEnvironmentArity
    (dynamicTruthPiDomainProjectionCodeTerm domain lowerApplication).

Lemma raw_eval_dynamicTruthPiDomainProjectionFormulaAllCodeTerm :
    forall (M : RawPAModel) e child,
  raw_term_eval M e
    (dynamicTruthPiDomainProjectionFormulaAllCodeTerm child) =
  rawFormulaAllCode M (raw_term_eval M e child).
Proof.
  intros M e child.
  unfold dynamicTruthPiDomainProjectionFormulaAllCodeTerm.
  apply raw_eval_dynamicTruthPiFormulaAllCodeTerm.
Qed.

Lemma raw_eval_dynamicTruthPiDomainProjectionRepeatedAllCodeTerm :
    forall (M : RawPAModel) e binderCount body,
  raw_term_eval M e
    (dynamicTruthPiDomainProjectionRepeatedAllCodeTerm binderCount body) =
  rawTemplateRepeatedAllCode M binderCount (raw_term_eval M e body).
Proof.
  intros M e binderCount.
  induction binderCount as [|smaller ih]; intro body;
    cbn [dynamicTruthPiDomainProjectionRepeatedAllCodeTerm
      rawTemplateRepeatedAllCode].
  - reflexivity.
  - change (rawFormulaAllCode M
      (raw_term_eval M e
        (dynamicTruthPiDomainProjectionRepeatedAllCodeTerm
          smaller body)) =
      rawFormulaAllCode M
        (rawTemplateRepeatedAllCode M smaller
          (raw_term_eval M e body))).
    now rewrite ih.
Qed.

Lemma raw_eval_dynamicTruthPiDomainProjectionCodeTerm : forall
    (M : RawPAModel) e domain lowerApplication,
  raw_term_eval M e
    (dynamicTruthPiDomainProjectionCodeTerm domain lowerApplication) =
  rawDynamicTruthPiDomainProjectionCode M
    (raw_term_eval M e domain)
    (raw_term_eval M e lowerApplication).
Proof.
  intros M e domain lowerApplication.
  unfold dynamicTruthPiDomainProjectionCodeTerm,
    rawDynamicTruthPiDomainProjectionCode.
  rewrite raw_eval_dynamicTruthPiFormulaImpCodeTerm,
    raw_eval_dynamicTruthPiSuccessorRowCodeTerm,
    raw_eval_dynamicTruthPiFormulaEx8CodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiDomainProjectionFieldCodeTerm : forall
    (M : RawPAModel) e domain lowerApplication,
  raw_term_eval M e
    (dynamicTruthPiDomainProjectionFieldCodeTerm
      domain lowerApplication) =
  rawDynamicTruthPiDomainProjectionFieldCode M
    (raw_term_eval M e domain)
    (raw_term_eval M e lowerApplication).
Proof.
  intros M e domain lowerApplication.
  unfold dynamicTruthPiDomainProjectionFieldCodeTerm,
    rawDynamicTruthPiDomainProjectionFieldCode.
  rewrite raw_eval_dynamicTruthPiDomainProjectionRepeatedAllCodeTerm,
    raw_eval_dynamicTruthPiDomainProjectionCodeTerm.
  reflexivity.
Qed.

Definition dynamicTruthPiDomainProjectionFieldCodeTermAt
    (output domain lowerApplication : term) : formula :=
  pEq output
    (dynamicTruthPiDomainProjectionFieldCodeTerm
      domain lowerApplication).

Lemma raw_sat_dynamicTruthPiDomainProjectionFieldCodeTermAt_iff : forall
    (M : RawPAModel) e output domain lowerApplication,
  raw_formula_sat M e
    (dynamicTruthPiDomainProjectionFieldCodeTermAt
      output domain lowerApplication) <->
  raw_term_eval M e output =
    rawDynamicTruthPiDomainProjectionFieldCode M
      (raw_term_eval M e domain)
      (raw_term_eval M e lowerApplication).
Proof.
  intros M e output domain lowerApplication.
  unfold dynamicTruthPiDomainProjectionFieldCodeTermAt.
  change (raw_term_eval M e output =
      raw_term_eval M e
        (dynamicTruthPiDomainProjectionFieldCodeTerm
          domain lowerApplication) <->
    raw_term_eval M e output =
      rawDynamicTruthPiDomainProjectionFieldCode M
        (raw_term_eval M e domain)
        (raw_term_eval M e lowerApplication)).
  rewrite raw_eval_dynamicTruthPiDomainProjectionFieldCodeTerm.
  reflexivity.
Qed.

(** Keep the already verified thirteen-quantifier code polynomial folded
    while the surrounding existential graph is simplified. *)
Opaque dynamicTruthPiDomainProjectionFieldCodeTerm.

(** ------------------------------------------------------------------
    Output-first transform graph and law-free semantics.

    Beneath the three witnesses the environment is

      lowerApplication :: domain :: upperNumeral ::
      fieldCode :: globalSigmaCode :: globalPiCode :: level :: tail.
*)

Definition dynamicTruthPiDomainProjectionFieldTransformGraph : formula :=
  pEx (pEx (pEx
    (fixedLevelAnd4
      (numeralTermCodeAtTermAt (tSucc (tVar 6)) (tVar 2))
      (codedFormulaSingleSubstitutionTermAt
        (tVar 2)
        (Term.numeral (formulaCode dynamicTruthPiRowDomainTemplate))
        (tVar 1))
      (dynamicTruthPiCoqLowerApplicationTermAt (tVar 4) (tVar 0))
      (dynamicTruthPiDomainProjectionFieldCodeTermAt
        (tVar 3) (tVar 1) (tVar 0))))).

Definition RawDynamicTruthPiDomainProjectionFieldTransformAt
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
      rawDynamicTruthPiDomainProjectionFieldCode M
        domain lowerApplication.

Arguments RawDynamicTruthPiDomainProjectionFieldTransformAt
  M globalSigmaCode globalPiCode level fieldCode : clear implicits.

Local Opaque dynamicTruthPiCoqLowerApplicationTermAt.

Theorem raw_sat_dynamicTruthPiDomainProjectionFieldTransformGraph_iff :
    forall (M : RawPAModel) tail
      globalSigmaCode globalPiCode level fieldCode,
  raw_formula_sat M
    (scons M fieldCode
      (scons M globalSigmaCode
        (scons M globalPiCode (scons M level tail))))
    dynamicTruthPiDomainProjectionFieldTransformGraph <->
  RawDynamicTruthPiDomainProjectionFieldTransformAt M
    globalSigmaCode globalPiCode level fieldCode.
Proof.
  intros M tail globalSigmaCode globalPiCode level fieldCode.
  unfold dynamicTruthPiDomainProjectionFieldTransformGraph,
    RawDynamicTruthPiDomainProjectionFieldTransformAt,
    fixedLevelAnd4.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_numeralTermCodeAtTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  setoid_rewrite raw_sat_dynamicTruthPiCoqLowerApplicationTermAt_iff.
  setoid_rewrite
    raw_sat_dynamicTruthPiDomainProjectionFieldCodeTermAt_iff.
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
        rawDynamicTruthPiDomainProjectionFieldCode M
          domain lowerApplication).
    {
      change (fieldCode =
        rawDynamicTruthPiDomainProjectionFieldCode M
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
        rawDynamicTruthPiDomainProjectionFieldCode M
          domain lowerApplication).
      exact hfield.
Qed.

(** ------------------------------------------------------------------
    Relational totality from the native operation premises. *)

Definition RawDynamicTruthPiDomainProjectionFieldTransformTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) globalSigmaCode globalPiCode level,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode
          (scons M globalSigmaCode
            (scons M globalPiCode (scons M level tail))))
        dynamicTruthPiDomainProjectionFieldTransformGraph.

Arguments RawDynamicTruthPiDomainProjectionFieldTransformTotal M
  : clear implicits.

Theorem dynamicTruthPiDomainProjectionFieldTransformGraph_raw_total :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiDomainStepTotal M ->
  RawDynamicTruthPiCoqLowerApplicationTotal M ->
  RawDynamicTruthPiDomainProjectionFieldTransformTotal M.
Proof.
  intros M hPA hdomain hlower tail
    globalSigmaCode globalPiCode level.
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (hdomain level upperNumeral hupperNumeral)
    as [domain hdomainWitness].
  destruct (hlower globalSigmaCode)
    as [lowerApplication hlowerApplication].
  exists (rawDynamicTruthPiDomainProjectionFieldCode M
    domain lowerApplication).
  apply (proj2
    (raw_sat_dynamicTruthPiDomainProjectionFieldTransformGraph_iff
      M tail globalSigmaCode globalPiCode level _)).
  exists upperNumeral, domain, lowerApplication.
  repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Direct compiler availability and proof-producing totality.

    This is precisely the witness package constructed by
    [raw_coqDynamicTruthPiDirectTemplateIdentification_exists] once a
    ternary selector and its syntax-guarded shift/opening laws have been
    chosen.  Retaining it as an explicit interface prevents a graph-output
    equality from being mistaken for the structural traces used by the
    direct proof compiler. *)

Definition RawDynamicTruthPiDomainProjectionDirectCompilerTotal
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

Arguments RawDynamicTruthPiDomainProjectionDirectCompilerTotal M
  : clear implicits.

Theorem dynamicTruthPiDomainProjectionFieldTransformGraph_raw_proof_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceGraph,
  RawDynamicTruthPiDomainStepTotal M ->
  RawDynamicTruthPiCoqLowerApplicationTotal M ->
  RawDynamicTruthPiDomainProjectionDirectCompilerTotal M ->
  RawOutputFirstPairedFormulaTransformProofTotal M sourceGraph
    dynamicTruthPiDomainProjectionFieldTransformGraph.
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
  exists (rawDynamicTruthPiDomainProjectionFieldCode M
      domain lowerApplication),
    (rawCoqDynamicTruthPiDomainProjectionFieldCertificate
      M hPA inputs).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthPiDomainProjectionFieldTransformGraph_iff
        M tail globalSigmaCode globalPiCode level _)).
    exists upperNumeral, domain, lowerApplication.
    repeat split; assumption.
  - exact
      (raw_codedPAProofOf_dynamicTruthPiDomainProjectionField_identified
        M hPA inputs domain lowerApplication identification).
Qed.

(** ------------------------------------------------------------------
    Composition with the paired global orbit.

    The exposed level is the predecessor level: the transform selects its
    successor numeral and compiles the corresponding positive Pi-row
    projection.  Both hidden global polarity codes come from one paired
    orbit witness. *)

Definition dynamicTruthPiDomainProjectionPositiveFieldGraph : formula :=
  outputFirstPairedFormulaGraphComposition
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph
    dynamicTruthPiDomainProjectionFieldTransformGraph.

Definition RawDynamicTruthPiDomainProjectionPositiveFieldAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel fieldCode : M) : Prop :=
  exists globalSigmaCode globalPiCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail predecessorLevel globalSigmaCode globalPiCode /\
    RawDynamicTruthPiDomainProjectionFieldTransformAt M
      globalSigmaCode globalPiCode predecessorLevel fieldCode.

Arguments RawDynamicTruthPiDomainProjectionPositiveFieldAt
  M tail predecessorLevel fieldCode : clear implicits.

Theorem raw_sat_dynamicTruthPiDomainProjectionPositiveFieldGraph_iff :
    forall (M : RawPAModel) tail predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M predecessorLevel tail))
    dynamicTruthPiDomainProjectionPositiveFieldGraph <->
  RawDynamicTruthPiDomainProjectionPositiveFieldAt M
    tail predecessorLevel fieldCode.
Proof.
  intros M tail predecessorLevel fieldCode.
  unfold dynamicTruthPiDomainProjectionPositiveFieldGraph,
    RawDynamicTruthPiDomainProjectionPositiveFieldAt.
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
        (raw_sat_dynamicTruthPiDomainProjectionFieldTransformGraph_iff
          M tail globalSigmaCode globalPiCode predecessorLevel fieldCode)).
      exact htransform.
  - intros (globalSigmaCode & globalPiCode & horbit & htransform).
    exists globalSigmaCode, globalPiCode. split.
    + apply (proj2
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail predecessorLevel globalSigmaCode globalPiCode)).
      exact horbit.
    + apply (proj2
        (raw_sat_dynamicTruthPiDomainProjectionFieldTransformGraph_iff
          M tail globalSigmaCode globalPiCode predecessorLevel fieldCode)).
      exact htransform.
Qed.

Definition RawDynamicTruthPiDomainProjectionPositiveFieldTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode certificate : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthPiDomainProjectionPositiveFieldGraph /\
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthPiDomainProjectionPositiveFieldTotal M
  : clear implicits.

Theorem dynamicTruthPiDomainProjectionPositiveFieldGraph_raw_proof_total :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiDomainStepTotal M ->
  RawDynamicTruthPiCoqLowerApplicationTotal M ->
  RawDynamicTruthPiDomainProjectionDirectCompilerTotal M ->
  RawDynamicTruthPiDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA hdomain hlower hcompiler.
  unfold RawDynamicTruthPiDomainProjectionPositiveFieldTotal,
    dynamicTruthPiDomainProjectionPositiveFieldGraph.
  apply (outputFirstPairedFormulaGraphComposition_raw_proof_total M
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph
    dynamicTruthPiDomainProjectionFieldTransformGraph).
  - intros tail predecessorLevel.
    destruct
      (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
        M hPA tail predecessorLevel) as
      (globalSigmaCode & globalPiCode & horbit & _ & _).
    exists globalSigmaCode, globalPiCode. exact horbit.
  - exact
      (dynamicTruthPiDomainProjectionFieldTransformGraph_raw_proof_total
        M hPA dynamicTruthPairedGlobalFormulaCodeOrbitGraph
        hdomain hlower hcompiler).
Qed.

(** The restricted existential field and this full-row projection consume
    exactly the same direct structural inputs: both identify the selected
    native Pi domain and the lower-Sigma application.  Reusing that
    orbit-refined compiler avoids imposing operation laws on unrelated
    carrier codes. *)
Definition RawDynamicTruthPiDomainProjectionOrbitDirectCompilerTotal
    (M : RawPAModel) : Prop :=
  RawDynamicTruthPiRestrictedExistentialOrbitDirectCompilerTotal M.

Arguments RawDynamicTruthPiDomainProjectionOrbitDirectCompilerTotal M
  : clear implicits.

(** Adequacy of the concrete paired-orbit witness supplies the native Pi
    domain and lower-Sigma application.  The resulting certificate is still
    only the full-row domain eliminator; no other branch projection or local
    decision/exclusivity component is asserted here. *)
Theorem
    dynamicTruthPiDomainProjectionPositiveFieldGraph_raw_adequate_proof_total
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiDomainProjectionOrbitDirectCompilerTotal M ->
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode certificate globalSigmaCode globalPiCode : M,
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail predecessorLevel globalSigmaCode globalPiCode /\
      RawDynamicTruthPiDomainProjectionFieldTransformAt M
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
  destruct (raw_dynamicTruthPiDomain_exists_adequate M hPA
    predecessorLevel upperNumeral hupperNumeral) as
    (domain & hdomainWitness & _hdomainAdequate).
  destruct (raw_dynamicTruthPiLower_exists_adequate M hPA
    globalSigmaCode hsigmaAdequate) as
    (lowerApplication & hlowerApplication & _hlowerAdequate).
  destruct (hcompiler tail predecessorLevel globalSigmaCode globalPiCode
    hadequateOrbit upperNumeral domain lowerApplication
    hupperNumeral hdomainWitness hlowerApplication) as
    [inputs identification].
  exists
    (rawDynamicTruthPiDomainProjectionFieldCode M
      domain lowerApplication),
    (rawCoqDynamicTruthPiDomainProjectionFieldCertificate
      M hPA inputs),
    globalSigmaCode, globalPiCode.
  split.
  - exact hadequateOrbit.
  - split.
    + exists upperNumeral, domain, lowerApplication.
      repeat split; try assumption; reflexivity.
    + exact
        (raw_codedPAProofOf_dynamicTruthPiDomainProjectionField_identified
          M hPA inputs domain lowerApplication identification).
Qed.

Theorem
    dynamicTruthPiDomainProjectionPositiveFieldGraph_raw_proof_total_of_orbit_direct_compiler
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiDomainProjectionOrbitDirectCompilerTotal M ->
  RawDynamicTruthPiDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA hcompiler tail predecessorLevel.
  destruct
    (dynamicTruthPiDomainProjectionPositiveFieldGraph_raw_adequate_proof_total
      M hPA hcompiler tail predecessorLevel) as
    (fieldCode & certificate & globalSigmaCode & globalPiCode &
     hadequateOrbit & htransform & hcertificate).
  exists fieldCode, certificate. split; [|exact hcertificate].
  apply (proj2
    (raw_sat_dynamicTruthPiDomainProjectionPositiveFieldGraph_iff
      M tail predecessorLevel fieldCode)).
  exists globalSigmaCode, globalPiCode. split; [|exact htransform].
  apply (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail predecessorLevel globalSigmaCode globalPiCode)).
  exact hadequateOrbit.
Qed.

(** Strongest concrete interface exported here.  The existing Pi selector
    construction converts shift/opening interchange on the actual orbit
    Sigma code into direct inputs.  Those same inputs are then retargeted to
    the full-row domain-projection certificate. *)
Corollary
    dynamicTruthPiDomainProjectionPositiveFieldGraph_raw_proof_total_of_orbit_interchange
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiRestrictedExistentialOrbitTernaryInterchangeTotal M ->
  RawDynamicTruthPiDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA hinterchange.
  apply
    dynamicTruthPiDomainProjectionPositiveFieldGraph_raw_proof_total_of_orbit_direct_compiler;
    [exact hPA |].
  unfold RawDynamicTruthPiDomainProjectionOrbitDirectCompilerTotal.
  exact
    (rawDynamicTruthPiRestrictedExistentialOrbitDirectCompilerTotal_of_interchange
      M hPA hinterchange).
Qed.

End PABoundedRawCodedDynamicTruthPiDomainProjectionTransformGraph.
