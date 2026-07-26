(**
  Output-first graph for the restricted universal-row proof field.

  The graph is read under

      fieldCode :: globalSigmaCode :: globalPiCode :: level :: tail.

  Three existential witnesses select, in order, a numeral term for
  [level + 1], the corresponding instance of Rocq's native Sigma-domain
  template, and the three-substitution application of [globalPiCode].  A
  transparent polynomial then constrains [fieldCode] to the thirteen-times
  universally closed restricted-row projection compiled in
  [RawCodedDynamicTruthUniversalLeafProofCompilation].

  The graph itself is relational and meaningful in every raw arithmetic
  structure.  Totality names the two existing nonstandard operation
  interfaces explicitly.  Proof totality additionally requires direct
  structural compiler inputs whose selected domain and opaque output are the
  very witnesses chosen by the graph.  No opaque shift/open commutation fact
  is inferred from application adequacy or from equality of output codes.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedFixedLevelTruth
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthUniversalLeafProofCompilation
  RawCodedOutputFirstPairedFormulaGraphComposition.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthUniversalLeafTransformGraph.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.
Import PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.

(** ------------------------------------------------------------------
    Transparent formula-code polynomial. *)

Definition restrictedUniversalFormulaAllCodeTerm (child : term) : term :=
  codeList2Term (Term.numeral 5) child.

Fixpoint restrictedUniversalRepeatedAllCodeTerm
    (binderCount : nat) (body : term) : term :=
  match binderCount with
  | 0 => body
  | S smaller =>
      restrictedUniversalFormulaAllCodeTerm
        (restrictedUniversalRepeatedAllCodeTerm smaller body)
  end.

Definition dynamicTruthSigmaRestrictedUniversalProjectionCodeTerm
    (domain lowerApplication : term) : term :=
  let universalLeaf :=
    dynamicTruthSigmaUniversalCodeTerm lowerApplication in
  formulaImpCodeTerm
    (formulaEx8CodeTerm
      (formulaAndCodeTerm domain universalLeaf))
    (formulaEx8CodeTerm universalLeaf).

Definition dynamicTruthSigmaRestrictedUniversalFieldCodeTerm
    (domain lowerApplication : term) : term :=
  restrictedUniversalRepeatedAllCodeTerm
    coqDynamicTruthSigmaRowEnvironmentArity
    (dynamicTruthSigmaRestrictedUniversalProjectionCodeTerm
      domain lowerApplication).

Definition rawDynamicTruthSigmaRestrictedUniversalProjectionGraphCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  let universalLeaf :=
    rawDynamicTruthSigmaUniversalCode M lowerApplication in
  rawFormulaImpCode M
    (rawFormulaEx8Code M
      (rawFormulaAndCode M domain universalLeaf))
    (rawFormulaEx8Code M universalLeaf).

Definition rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawTemplateRepeatedAllCode M
    coqDynamicTruthSigmaRowEnvironmentArity
    (rawDynamicTruthSigmaRestrictedUniversalProjectionGraphCode M
      domain lowerApplication).

Lemma raw_eval_restrictedUniversalFormulaAllCodeTerm : forall
    (M : RawPAModel) e child,
  raw_term_eval M e (restrictedUniversalFormulaAllCodeTerm child) =
  rawFormulaAllCode M (raw_term_eval M e child).
Proof.
  intros M e child.
  unfold restrictedUniversalFormulaAllCodeTerm, rawFormulaAllCode.
  rewrite raw_eval_codeList2Term, raw_term_eval_numeral.
  reflexivity.
Qed.

Lemma raw_eval_restrictedUniversalRepeatedAllCodeTerm : forall
    (M : RawPAModel) e binderCount body,
  raw_term_eval M e
    (restrictedUniversalRepeatedAllCodeTerm binderCount body) =
  rawTemplateRepeatedAllCode M binderCount
    (raw_term_eval M e body).
Proof.
  intros M e binderCount.
  induction binderCount as [|smaller ih]; intro body;
    cbn [restrictedUniversalRepeatedAllCodeTerm
      rawTemplateRepeatedAllCode].
  - reflexivity.
  - change (rawFormulaAllCode M
      (raw_term_eval M e
        (restrictedUniversalRepeatedAllCodeTerm smaller body)) =
      rawFormulaAllCode M
        (rawTemplateRepeatedAllCode M smaller
          (raw_term_eval M e body))).
    now rewrite ih.
Qed.

Lemma raw_eval_dynamicTruthSigmaRestrictedUniversalProjectionCodeTerm :
  forall (M : RawPAModel) e domain lowerApplication,
  raw_term_eval M e
    (dynamicTruthSigmaRestrictedUniversalProjectionCodeTerm
      domain lowerApplication) =
  rawDynamicTruthSigmaRestrictedUniversalProjectionGraphCode M
    (raw_term_eval M e domain)
    (raw_term_eval M e lowerApplication).
Proof.
  intros M e domain lowerApplication.
  unfold dynamicTruthSigmaRestrictedUniversalProjectionCodeTerm,
    rawDynamicTruthSigmaRestrictedUniversalProjectionGraphCode.
  rewrite raw_eval_formulaImpCodeTerm,
    !raw_eval_formulaEx8CodeTerm,
    raw_eval_formulaAndCodeTerm,
    !raw_eval_dynamicTruthSigmaUniversalCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthSigmaRestrictedUniversalFieldCodeTerm : forall
    (M : RawPAModel) e domain lowerApplication,
  raw_term_eval M e
    (dynamicTruthSigmaRestrictedUniversalFieldCodeTerm
      domain lowerApplication) =
  rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
    (raw_term_eval M e domain)
    (raw_term_eval M e lowerApplication).
Proof.
  intros M e domain lowerApplication.
  unfold dynamicTruthSigmaRestrictedUniversalFieldCodeTerm,
    rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode.
  rewrite raw_eval_restrictedUniversalRepeatedAllCodeTerm,
    raw_eval_dynamicTruthSigmaRestrictedUniversalProjectionCodeTerm.
  reflexivity.
Qed.

Definition dynamicTruthSigmaRestrictedUniversalFieldCodeTermAt
    (output domain lowerApplication : term) : formula :=
  pEq output
    (dynamicTruthSigmaRestrictedUniversalFieldCodeTerm
      domain lowerApplication).

Lemma raw_sat_dynamicTruthSigmaRestrictedUniversalFieldCodeTermAt_iff :
  forall (M : RawPAModel) e output domain lowerApplication,
  raw_formula_sat M e
    (dynamicTruthSigmaRestrictedUniversalFieldCodeTermAt
      output domain lowerApplication) <->
  raw_term_eval M e output =
    rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
      (raw_term_eval M e domain)
      (raw_term_eval M e lowerApplication).
Proof.
  intros M e output domain lowerApplication.
  unfold dynamicTruthSigmaRestrictedUniversalFieldCodeTermAt.
  change (raw_term_eval M e output =
      raw_term_eval M e
        (dynamicTruthSigmaRestrictedUniversalFieldCodeTerm
          domain lowerApplication) <->
    raw_term_eval M e output =
      rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
        (raw_term_eval M e domain)
        (raw_term_eval M e lowerApplication)).
  rewrite raw_eval_dynamicTruthSigmaRestrictedUniversalFieldCodeTerm.
  reflexivity.
Qed.

(** The graph polynomial uses fixed numeral leaves, while the direct source
    code uses structural quotation.  PA identifies those leaves exactly. *)
Lemma rawDynamicTruthSigmaUniversalCode_eq_directTemplateCode : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  rawDynamicTruthSigmaUniversalCode M lowerApplication =
  rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M lowerApplication.
Proof.
  intros M hPA lowerApplication.
  unfold rawDynamicTruthSigmaUniversalCode,
    rawDynamicTruthSigmaNoBinderCode,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode,
    rawFormulaEx3Code.
  rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

Theorem rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode_eq_compiled :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    domain lowerApplication,
  rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
    domain lowerApplication =
  rawCoqDynamicTruthSigmaRestrictedUniversalFieldCode M
    domain lowerApplication.
Proof.
  intros M hPA domain lowerApplication.
  unfold rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode,
    rawDynamicTruthSigmaRestrictedUniversalProjectionGraphCode,
    rawCoqDynamicTruthSigmaRestrictedUniversalFieldCode,
    rawCoqDynamicTruthSigmaRestrictedUniversalProjectionCode.
  rewrite (rawDynamicTruthSigmaUniversalCode_eq_directTemplateCode
    M hPA lowerApplication).
  reflexivity.
Qed.

(** Keep the thirteen-quantifier code polynomial folded while simplifying
    the surrounding existential graph.  Its evaluation theorem above is the
    intended reduction interface. *)
Opaque dynamicTruthSigmaRestrictedUniversalFieldCodeTerm.

(** ------------------------------------------------------------------
    Output-first transform graph and arbitrary-model semantics.

    Beneath the three witnesses the environment is

      lowerApplication :: domain :: upperNumeral ::
      fieldCode :: globalSigmaCode :: globalPiCode :: level :: tail.
*)

Definition dynamicTruthSigmaRestrictedUniversalFieldTransformGraph
    : formula :=
  pEx (pEx (pEx
    (fixedLevelAnd4
      (numeralTermCodeAtTermAt (tSucc (tVar 6)) (tVar 2))
      (codedFormulaSingleSubstitutionTermAt
        (tVar 2)
        (Term.numeral dynamicTruthSigmaRowDomainTemplateCode)
        (tVar 1))
      (dynamicTruthCoqLowerApplicationTermAt (tVar 5) (tVar 0))
      (dynamicTruthSigmaRestrictedUniversalFieldCodeTermAt
        (tVar 3) (tVar 1) (tVar 0))))).

Definition RawDynamicTruthSigmaRestrictedUniversalFieldTransformAt
    (M : RawPAModel)
    (globalSigmaCode globalPiCode level fieldCode : M) : Prop :=
  exists upperNumeral domain lowerApplication : M,
    RawNumeralTermCodeAt M (raw_succ M level) upperNumeral /\
    RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode) domain /\
    RawDynamicTruthCoqLowerApplication M
      globalPiCode lowerApplication /\
    fieldCode =
      rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
        domain lowerApplication.

Arguments RawDynamicTruthSigmaRestrictedUniversalFieldTransformAt
  M globalSigmaCode globalPiCode level fieldCode : clear implicits.

Local Opaque dynamicTruthCoqLowerApplicationTermAt.

Theorem raw_sat_dynamicTruthSigmaRestrictedUniversalFieldTransformGraph_iff :
  forall (M : RawPAModel) tail
    globalSigmaCode globalPiCode level fieldCode,
  raw_formula_sat M
    (scons M fieldCode
      (scons M globalSigmaCode
        (scons M globalPiCode (scons M level tail))))
    dynamicTruthSigmaRestrictedUniversalFieldTransformGraph <->
  RawDynamicTruthSigmaRestrictedUniversalFieldTransformAt M
    globalSigmaCode globalPiCode level fieldCode.
Proof.
  intros M tail globalSigmaCode globalPiCode level fieldCode.
  unfold dynamicTruthSigmaRestrictedUniversalFieldTransformGraph,
    RawDynamicTruthSigmaRestrictedUniversalFieldTransformAt,
    fixedLevelAnd4.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_numeralTermCodeAtTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  setoid_rewrite raw_sat_dynamicTruthCoqLowerApplicationTermAt_iff.
  setoid_rewrite
    raw_sat_dynamicTruthSigmaRestrictedUniversalFieldCodeTermAt_iff.
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
        rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
          domain lowerApplication).
    {
      change (fieldCode =
        rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
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
        rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
          domain lowerApplication).
      exact hfield.
Qed.

(** ------------------------------------------------------------------
    Relational totality from the existing operation premises. *)

Definition RawDynamicTruthSigmaRestrictedUniversalFieldTransformTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) globalSigmaCode globalPiCode level,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode
          (scons M globalSigmaCode
            (scons M globalPiCode (scons M level tail))))
        dynamicTruthSigmaRestrictedUniversalFieldTransformGraph.

Arguments RawDynamicTruthSigmaRestrictedUniversalFieldTransformTotal M
  : clear implicits.

Theorem dynamicTruthSigmaRestrictedUniversalFieldTransformGraph_raw_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaDomainStepTotal M ->
  RawDynamicTruthCoqLowerApplicationTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalFieldTransformTotal M.
Proof.
  intros M hPA hdomain hlower tail
    globalSigmaCode globalPiCode level.
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (hdomain level upperNumeral hupperNumeral)
    as [domain hdomainWitness].
  destruct (hlower globalPiCode)
    as [lowerApplication hlowerApplication].
  exists (rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
    domain lowerApplication).
  apply (proj2
    (raw_sat_dynamicTruthSigmaRestrictedUniversalFieldTransformGraph_iff
      M tail globalSigmaCode globalPiCode level _)).
  exists upperNumeral, domain, lowerApplication.
  repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Direct compiler availability and proof-producing totality.

    This premise is deliberately stronger than relational graph totality:
    after the graph's three witnesses have been selected, it supplies direct
    represented operation traces for the exact template atoms and identifies
    their domain/application outputs with those witnesses.  Nothing in the
    graph semantics is used to manufacture opaque shift/open relations. *)

Definition RawDynamicTruthSigmaRestrictedUniversalDirectCompilerTotal
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

Arguments RawDynamicTruthSigmaRestrictedUniversalDirectCompilerTotal M
  : clear implicits.

Theorem dynamicTruthSigmaRestrictedUniversalFieldTransformGraph_raw_proof_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceGraph,
  RawDynamicTruthSigmaDomainStepTotal M ->
  RawDynamicTruthCoqLowerApplicationTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalDirectCompilerTotal M ->
  RawOutputFirstPairedFormulaTransformProofTotal M sourceGraph
    dynamicTruthSigmaRestrictedUniversalFieldTransformGraph.
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
  exists (rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
      domain lowerApplication),
    (rawCoqDynamicTruthSigmaRestrictedUniversalFieldCertificate
      M hPA inputs).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthSigmaRestrictedUniversalFieldTransformGraph_iff
        M tail globalSigmaCode globalPiCode level _)).
    exists upperNumeral, domain, lowerApplication.
    repeat split; assumption.
  - rewrite (rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode_eq_compiled
      M hPA domain lowerApplication).
    exact
      (raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedUniversalField_identified
        M hPA inputs domain lowerApplication identification).
Qed.

End PABoundedRawCodedDynamicTruthUniversalLeafTransformGraph.
