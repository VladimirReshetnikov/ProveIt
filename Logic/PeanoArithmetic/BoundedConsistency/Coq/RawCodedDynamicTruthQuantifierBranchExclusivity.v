(**
  The two quantifier-diagonal cells of the native dynamic-truth matrix.

  Sigma truth of an existential and Pi falsity of an existential collide
  only after one knows that the Sigma witness supplies an application of
  the preceding Sigma predicate.  Dually, Pi falsity of a universal and
  Sigma truth of a universal collide only after the Pi witness supplies an
  application of the preceding Pi predicate.  Those cross-level facts are
  not consequences of propositional syntax, so this module records them as
  two explicit premise formulae.

  The fixed PA cells proved below have the shape

      cross-level premise -> Sigma branch -> Pi branch -> bottom.

  Their formula-level proofs are uniform in a standard lower-application
  formula.  The public carrier layer is different: it is polynomial in an
  arbitrary model element [lowerApplication], exactly as the native Sigma
  and Pi successor-row assemblers are.  Its common-context collision
  endpoints therefore do not decode that carrier element into a
  metatheoretic [formula], and they do not claim to construct either
  cross-level premise root.

  The dynamic universal and existential leaf codes reuse the opaque-template
  carrier polynomials already used by the restricted branch projection
  compilers.  The final helpers also expose the exact implication-elimination
  step from a restricted row to its selected quantifier leaf.  Deep closure
  of the paired orbit guarantees syntax adequacy elsewhere, but it does not
  imply either cross-level truth bridge and is intentionally not used as a
  substitute for one here.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedPAProvability
  RawCodedRestrictedPAProof
  RawCodedProofBinaryConstructors
  RawCodedPAProofImpICertificates
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.

(** ------------------------------------------------------------------
    Literal native quantifier branches.

    [lowerApplication] already has the native row's three binder variables
    [#2,#1,#0] installed.  On standard predecessor syntax it is the renamed
    ternary application produced by [dynamicTruthCoqLowerApplicationRenaming]
    or its Pi dual.  Keeping this post-selection application as the parameter
    makes the carrier polynomial below line up exactly with the successor-row
    graph output. *)

Definition dynamicTruthSigmaEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthSigmaRowExFormula.

Definition dynamicTruthPiExistentialLeafFormula
    (lowerApplication : formula) : formula :=
  pAnd dynamicTruthPiRowExistentialPrefixFormula
    (fixedLevelNoBinderCounterexampleTermAt lowerApplication
      (tVar 9) (tVar 8) (tVar 10)).

Definition dynamicTruthPiExistentialEx8BranchFormula
    (lowerApplication : formula) : formula :=
  fixedLevelEx8
    (dynamicTruthPiExistentialLeafFormula lowerApplication).

Definition dynamicTruthSigmaUniversalLeafFormula
    (lowerApplication : formula) : formula :=
  pAnd dynamicTruthSigmaRowUniversalPrefixFormula
    (fixedLevelNoBinderCounterexampleTermAt lowerApplication
      (tVar 9) (tVar 8) (tVar 10)).

Definition dynamicTruthSigmaUniversalEx8BranchFormula
    (lowerApplication : formula) : formula :=
  fixedLevelEx8
    (dynamicTruthSigmaUniversalLeafFormula lowerApplication).

Definition dynamicTruthPiAllEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthPiRowAllFormula.

(** ------------------------------------------------------------------
    Exact cross-level premises.

    The counterexample formulae are literally the antecedents negated by
    the opposite row's [fixedLevelNoBinderCounterexampleTermAt].  Thus the
    first premise says that a selected Sigma-existential branch supplies the
    lower-Sigma binder counterexample.  The second says that a selected
    Pi-universal branch supplies the lower-Pi binder counterexample. *)

Definition dynamicTruthPiExistentialCounterexampleFormula
    (lowerApplication : formula) : formula :=
  fixedLevelEx3
    (pAnd dynamicTruthPiRowBinderPrependFormula lowerApplication).

Definition dynamicTruthSigmaUniversalCounterexampleFormula
    (lowerApplication : formula) : formula :=
  fixedLevelEx3
    (pAnd dynamicTruthSigmaRowBinderPrependFormula lowerApplication).

(** Eight universal binders range over the witness tuple of the opposite
    selected branch.  The lower application is evaluated beneath that tuple,
    exactly where the opposite no-counterexample clause evaluates it. *)
Definition dynamicTruthQuantifierAll8 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll body))))))).

Definition dynamicTruthSigmaExPiExCrossLevelPremiseFormula
    (lowerSigmaApplication : formula) : formula :=
  pImp dynamicTruthSigmaEx8BranchFormula
    (dynamicTruthQuantifierAll8
      (pImp dynamicTruthPiRowExistentialPrefixFormula
        (dynamicTruthPiExistentialCounterexampleFormula
          lowerSigmaApplication))).

Definition dynamicTruthSigmaAllPiAllCrossLevelPremiseFormula
    (lowerPiApplication : formula) : formula :=
  pImp dynamicTruthPiAllEx8BranchFormula
    (dynamicTruthQuantifierAll8
      (pImp dynamicTruthSigmaRowUniversalPrefixFormula
        (dynamicTruthSigmaUniversalCounterexampleFormula
          lowerPiApplication))).

Definition dynamicTruthSigmaExPiExConditionalCellFormula
    (lowerSigmaApplication : formula) : formula :=
  pImp
    (dynamicTruthSigmaExPiExCrossLevelPremiseFormula
      lowerSigmaApplication)
    (pImp dynamicTruthSigmaEx8BranchFormula
      (pImp
        (dynamicTruthPiExistentialEx8BranchFormula
          lowerSigmaApplication)
        pBot)).

Definition dynamicTruthSigmaAllPiAllConditionalCellFormula
    (lowerPiApplication : formula) : formula :=
  pImp
    (dynamicTruthSigmaAllPiAllCrossLevelPremiseFormula
      lowerPiApplication)
    (pImp
      (dynamicTruthSigmaUniversalEx8BranchFormula lowerPiApplication)
      (pImp dynamicTruthPiAllEx8BranchFormula pBot)).

(** The two formulae are valid for purely structural reasons once their
    cross-level antecedent is present.  In particular these proofs do not
    silently appeal to semantic correctness of a preceding truth level. *)
Theorem dynamicTruthSigmaExPiExConditionalCellFormula_raw_valid : forall
    lowerSigmaApplication (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (dynamicTruthSigmaExPiExConditionalCellFormula
      lowerSigmaApplication).
Proof.
  intros lowerSigmaApplication M _hPA e.
  unfold dynamicTruthSigmaExPiExConditionalCellFormula,
    dynamicTruthSigmaExPiExCrossLevelPremiseFormula,
    dynamicTruthSigmaEx8BranchFormula,
    dynamicTruthPiExistentialEx8BranchFormula,
    dynamicTruthPiExistentialLeafFormula,
    dynamicTruthPiExistentialCounterexampleFormula,
    dynamicTruthQuantifierAll8,
    fixedLevelEx8, fixedLevelEx3,
    fixedLevelNoBinderCounterexampleTermAt.
  cbn [raw_formula_sat].
  intros hcross hsigma hpi.
  destruct hpi as
    (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & _hprefix & hnone).
  exact (hnone (hcross hsigma p0 p1 p2 p3 p4 p5 p6 p7 _hprefix)).
Qed.

Theorem dynamicTruthSigmaAllPiAllConditionalCellFormula_raw_valid : forall
    lowerPiApplication (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (dynamicTruthSigmaAllPiAllConditionalCellFormula
      lowerPiApplication).
Proof.
  intros lowerPiApplication M _hPA e.
  unfold dynamicTruthSigmaAllPiAllConditionalCellFormula,
    dynamicTruthSigmaAllPiAllCrossLevelPremiseFormula,
    dynamicTruthSigmaUniversalEx8BranchFormula,
    dynamicTruthSigmaUniversalLeafFormula,
    dynamicTruthPiAllEx8BranchFormula,
    dynamicTruthSigmaUniversalCounterexampleFormula,
    dynamicTruthQuantifierAll8,
    fixedLevelEx8, fixedLevelEx3,
    fixedLevelNoBinderCounterexampleTermAt.
  cbn [raw_formula_sat].
  intros hcross hsigma hpi.
  destruct hsigma as
    (s0 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & _hprefix & hnone).
  exact (hnone (hcross hpi s0 s1 s2 s3 s4 s5 s6 s7 _hprefix)).
Qed.

(** Completeness is applied to the seal of an open formula and the seal is
    then eliminated.  This helper is intentionally local to avoid coupling
    the quantifier cells to either of the already-built diagonal modules. *)
Lemma PA_proves_quantifier_open_formula_of_raw_valid : forall target : formula,
  (forall (M : RawPAModel), RawPASatisfies M -> forall e,
    raw_formula_sat M e target) ->
  Formula.BProv Formula.Ax_s [] target.
Proof.
  intros target hvalid.
  assert (hclosed : Formula.BProv Formula.Ax_s [] (Formula.sealPA target)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA e.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner. exact (hvalid M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] target (fun n => n) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

Theorem PA_proves_dynamicTruthSigmaExPiExConditionalCellFormula : forall
    lowerSigmaApplication,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthSigmaExPiExConditionalCellFormula
      lowerSigmaApplication).
Proof.
  intro lowerSigmaApplication.
  apply PA_proves_quantifier_open_formula_of_raw_valid.
  exact (dynamicTruthSigmaExPiExConditionalCellFormula_raw_valid
    lowerSigmaApplication).
Qed.

Theorem PA_proves_dynamicTruthSigmaAllPiAllConditionalCellFormula : forall
    lowerPiApplication,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthSigmaAllPiAllConditionalCellFormula
      lowerPiApplication).
Proof.
  intro lowerPiApplication.
  apply PA_proves_quantifier_open_formula_of_raw_valid.
  exact (dynamicTruthSigmaAllPiAllConditionalCellFormula_raw_valid
    lowerPiApplication).
Qed.

(** ------------------------------------------------------------------
    Native carrier-code polynomials.

    The two lower-dependent leaf codes are exactly the opaque-template
    polynomials consumed by the existing restricted projection compilers.
    No carrier code is decoded into a Rocq [formula]. *)

Definition rawDynamicTruthSigmaEx8BranchCode
    (M : RawPAModel) : M :=
  rawFormulaEx8Code M
    (rawFixedFormulaNumeralCode M dynamicTruthSigmaRowExFormula).

Definition rawDynamicTruthPiExistentialEx8BranchCode
    (M : RawPAModel) (lowerApplication : M) : M :=
  rawDynamicTruthPiFormulaEx8Code M
    (rawCoqDynamicTruthPiExistentialLeafTemplateCode M
      lowerApplication).

Definition rawDynamicTruthSigmaUniversalEx8BranchCode
    (M : RawPAModel) (lowerApplication : M) : M :=
  rawFormulaEx8Code M
    (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
      lowerApplication).

Definition rawDynamicTruthPiAllEx8BranchCode
    (M : RawPAModel) : M :=
  rawDynamicTruthPiFormulaEx8Code M
    (rawDynamicTruthPiFixedFormulaNumeralCode M
      dynamicTruthPiRowAllFormula).

Definition rawDynamicTruthPiExistentialCounterexampleCode
    (M : RawPAModel) (lowerApplication : M) : M :=
  rawDynamicTruthPiFormulaEx3Code M
    (rawFormulaAndCode M
      (rawQuotedFormulaCode M dynamicTruthPiRowBinderPrependFormula)
      lowerApplication).

Definition rawDynamicTruthSigmaUniversalCounterexampleCode
    (M : RawPAModel) (lowerApplication : M) : M :=
  rawFormulaEx3Code M
    (rawFormulaAndCode M
      (rawQuotedFormulaCode M dynamicTruthSigmaRowBinderPrependFormula)
      lowerApplication).

Definition rawDynamicTruthQuantifierAll8Code
    (M : RawPAModel) (body : M) : M :=
  rawFormulaAllCode M (rawFormulaAllCode M
    (rawFormulaAllCode M (rawFormulaAllCode M
      (rawFormulaAllCode M (rawFormulaAllCode M
        (rawFormulaAllCode M (rawFormulaAllCode M body))))))).

Definition rawDynamicTruthSigmaExPiExCrossLevelPremiseCode
    (M : RawPAModel) (lowerSigmaApplication : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthSigmaEx8BranchCode M)
    (rawDynamicTruthQuantifierAll8Code M
      (rawFormulaImpCode M
        (rawDynamicTruthPiFixedFormulaNumeralCode M
          dynamicTruthPiRowExistentialPrefixFormula)
        (rawDynamicTruthPiExistentialCounterexampleCode M
          lowerSigmaApplication))).

Definition rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode
    (M : RawPAModel) (lowerPiApplication : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthPiAllEx8BranchCode M)
    (rawDynamicTruthQuantifierAll8Code M
      (rawFormulaImpCode M
        (rawFixedFormulaNumeralCode M
          dynamicTruthSigmaRowUniversalPrefixFormula)
        (rawDynamicTruthSigmaUniversalCounterexampleCode M
          lowerPiApplication))).

Definition rawDynamicTruthSigmaExPiExConditionalCellCode
    (M : RawPAModel) (lowerSigmaApplication : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M
      lowerSigmaApplication)
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaEx8BranchCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPiExistentialEx8BranchCode M
          lowerSigmaApplication)
        (rawFormulaBotCode M))).

Definition rawDynamicTruthSigmaAllPiAllConditionalCellCode
    (M : RawPAModel) (lowerPiApplication : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M
      lowerPiApplication)
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPiApplication)
      (rawFormulaImpCode M
        (rawDynamicTruthPiAllEx8BranchCode M)
        (rawFormulaBotCode M))).

(** The opaque-template leaf polynomials are extensionally the native row
    polynomials for every carrier-selected lower application.  Only the
    fixed standard prefix and prepend leaves need identification. *)
Lemma rawDynamicTruthPiExistentialEx8BranchCode_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  rawDynamicTruthPiExistentialEx8BranchCode M lowerApplication =
  rawDynamicTruthPiFormulaEx8Code M
    (rawDynamicTruthPiExistentialCode M lowerApplication).
Proof.
  intros M hPA lowerApplication.
  unfold rawDynamicTruthPiExistentialEx8BranchCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode,
    rawDynamicTruthPiExistentialCode,
    rawDynamicTruthPiNoBinderCode.
  rewrite !rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaUniversalEx8BranchCode_eq_native : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  rawDynamicTruthSigmaUniversalEx8BranchCode M lowerApplication =
  rawFormulaEx8Code M
    (rawDynamicTruthSigmaUniversalCode M lowerApplication).
Proof.
  intros M hPA lowerApplication.
  unfold rawDynamicTruthSigmaUniversalEx8BranchCode,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode,
    rawDynamicTruthSigmaUniversalCode,
    rawDynamicTruthSigmaNoBinderCode.
  rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

(** Quotation equations certify that the carrier polynomials specialize to
    the literal native branches on standard lower-application syntax. *)
Lemma rawDynamicTruthSigmaEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthSigmaEx8BranchCode M =
  rawQuotedFormulaCode M dynamicTruthSigmaEx8BranchFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthSigmaEx8BranchCode,
    dynamicTruthSigmaEx8BranchFormula, fixedLevelEx8.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA).
  reflexivity.
Qed.

Lemma rawDynamicTruthPiExistentialEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  rawDynamicTruthPiExistentialEx8BranchCode M
    (rawQuotedFormulaCode M lowerApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthPiExistentialEx8BranchFormula lowerApplication).
Proof.
  intros M hPA lowerApplication.
  unfold rawDynamicTruthPiExistentialEx8BranchCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode,
    dynamicTruthPiExistentialEx8BranchFormula,
    dynamicTruthPiExistentialLeafFormula,
    fixedLevelEx8, fixedLevelNoBinderCounterexampleTermAt,
    fixedLevelEx3, dynamicTruthPiRowBinderPrependFormula.
  cbn [rawQuotedFormulaCode].
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaUniversalEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  rawDynamicTruthSigmaUniversalEx8BranchCode M
    (rawQuotedFormulaCode M lowerApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthSigmaUniversalEx8BranchFormula lowerApplication).
Proof.
  intros M hPA lowerApplication.
  unfold rawDynamicTruthSigmaUniversalEx8BranchCode,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode,
    dynamicTruthSigmaUniversalEx8BranchFormula,
    dynamicTruthSigmaUniversalLeafFormula,
    fixedLevelEx8, fixedLevelNoBinderCounterexampleTermAt,
    fixedLevelEx3, dynamicTruthSigmaRowBinderPrependFormula.
  cbn [rawQuotedFormulaCode].
  reflexivity.
Qed.

Lemma rawDynamicTruthPiAllEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthPiAllEx8BranchCode M =
  rawQuotedFormulaCode M dynamicTruthPiAllEx8BranchFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthPiAllEx8BranchCode,
    dynamicTruthPiAllEx8BranchFormula, fixedLevelEx8.
  rewrite (rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted M hPA).
  reflexivity.
Qed.

Lemma rawDynamicTruthPiExistentialCounterexampleCode_eq_quoted : forall
    (M : RawPAModel) lowerApplication,
  rawDynamicTruthPiExistentialCounterexampleCode M
    (rawQuotedFormulaCode M lowerApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthPiExistentialCounterexampleFormula lowerApplication).
Proof.
  intros M lowerApplication.
  unfold rawDynamicTruthPiExistentialCounterexampleCode,
    dynamicTruthPiExistentialCounterexampleFormula,
    fixedLevelEx3.
  cbn [rawQuotedFormulaCode].
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaUniversalCounterexampleCode_eq_quoted : forall
    (M : RawPAModel) lowerApplication,
  rawDynamicTruthSigmaUniversalCounterexampleCode M
    (rawQuotedFormulaCode M lowerApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthSigmaUniversalCounterexampleFormula lowerApplication).
Proof.
  intros M lowerApplication.
  unfold rawDynamicTruthSigmaUniversalCounterexampleCode,
    dynamicTruthSigmaUniversalCounterexampleFormula,
    fixedLevelEx3.
  cbn [rawQuotedFormulaCode].
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaExPiExCrossLevelPremiseCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M
    (rawQuotedFormulaCode M lowerApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthSigmaExPiExCrossLevelPremiseFormula lowerApplication).
Proof.
  intros M hPA lowerApplication.
  unfold rawDynamicTruthSigmaExPiExCrossLevelPremiseCode,
    dynamicTruthSigmaExPiExCrossLevelPremiseFormula,
    rawDynamicTruthQuantifierAll8Code,
    dynamicTruthQuantifierAll8.
  rewrite rawDynamicTruthSigmaEx8BranchCode_eq_quoted by exact hPA.
  rewrite (rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted M hPA).
  rewrite rawDynamicTruthPiExistentialCounterexampleCode_eq_quoted.
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M
    (rawQuotedFormulaCode M lowerApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthSigmaAllPiAllCrossLevelPremiseFormula lowerApplication).
Proof.
  intros M hPA lowerApplication.
  unfold rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode,
    dynamicTruthSigmaAllPiAllCrossLevelPremiseFormula,
    rawDynamicTruthQuantifierAll8Code,
    dynamicTruthQuantifierAll8.
  rewrite rawDynamicTruthPiAllEx8BranchCode_eq_quoted by exact hPA.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA).
  rewrite rawDynamicTruthSigmaUniversalCounterexampleCode_eq_quoted.
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaExPiExConditionalCellCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  rawDynamicTruthSigmaExPiExConditionalCellCode M
    (rawQuotedFormulaCode M lowerApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthSigmaExPiExConditionalCellFormula lowerApplication).
Proof.
  intros M hPA lowerApplication.
  unfold rawDynamicTruthSigmaExPiExConditionalCellCode,
    dynamicTruthSigmaExPiExConditionalCellFormula.
  rewrite rawDynamicTruthSigmaExPiExCrossLevelPremiseCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthSigmaEx8BranchCode_eq_quoted by exact hPA.
  rewrite rawDynamicTruthPiExistentialEx8BranchCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaAllPiAllConditionalCellCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  rawDynamicTruthSigmaAllPiAllConditionalCellCode M
    (rawQuotedFormulaCode M lowerApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthSigmaAllPiAllConditionalCellFormula lowerApplication).
Proof.
  intros M hPA lowerApplication.
  unfold rawDynamicTruthSigmaAllPiAllConditionalCellCode,
    dynamicTruthSigmaAllPiAllConditionalCellFormula.
  rewrite rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthSigmaUniversalEx8BranchCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthPiAllEx8BranchCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

(** Fixed standard instances have ordinary represented PA proofs.  The
    theorem is deliberately not quantified over an arbitrary carrier code;
    that nonstandard compilation problem is exposed below as an interface. *)
Theorem raw_codedPAProofOf_dynamicTruthSigmaExPiExConditionalCell_standard :
    forall (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthSigmaExPiExConditionalCellCode M
        (rawQuotedFormulaCode M lowerApplication))
      certificate.
Proof.
  intros M hPA lowerApplication.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (dynamicTruthSigmaExPiExConditionalCellFormula lowerApplication)
    (PA_proves_dynamicTruthSigmaExPiExConditionalCellFormula
      lowerApplication)) as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthSigmaExPiExConditionalCellCode_eq_quoted
    by exact hPA.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthSigmaAllPiAllConditionalCell_standard :
    forall (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthSigmaAllPiAllConditionalCellCode M
        (rawQuotedFormulaCode M lowerApplication))
      certificate.
Proof.
  intros M hPA lowerApplication.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (dynamicTruthSigmaAllPiAllConditionalCellFormula lowerApplication)
    (PA_proves_dynamicTruthSigmaAllPiAllConditionalCellFormula
      lowerApplication)) as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthSigmaAllPiAllConditionalCellCode_eq_quoted
    by exact hPA.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

(** This is the honest remaining carrier-parametric proof-compilation seam.
    A future template compiler may discharge it without changing either
    public cell code or either local collision theorem. *)
Definition RawDynamicTruthQuantifierConditionalCellCompilerTotal
    (M : RawPAModel) : Prop :=
  forall lowerSigmaApplication lowerPiApplication : M,
    RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication ->
    RawCodedFormulaAtomicallyAdequate M lowerPiApplication ->
    (exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthSigmaExPiExConditionalCellCode M
          lowerSigmaApplication)
        certificate) /\
    (exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthSigmaAllPiAllConditionalCellCode M
          lowerPiApplication)
        certificate).

Arguments RawDynamicTruthQuantifierConditionalCellCompilerTotal M
  : clear implicits.

(** ------------------------------------------------------------------
    Exact common-context collision compiler.

    All four inputs are checked local roots in one and the same context.
    The first is the fixed conditional PA cell; the second is the genuinely
    cross-level premise.  Three implication eliminations then produce
    bottom, with no weakening and no manufactured truth bridge. *)

Definition rawDynamicTruthQuantifierConditionalCellCollisionRoot
    (M : RawPAModel)
    (context premise sigmaBranch piBranch
      cellRoot premiseRoot sigmaRoot piRoot : M) : M :=
  rawProofImpERoot M context piBranch (rawFormulaBotCode M)
    (rawProofImpERoot M context sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M))
      (rawProofImpERoot M context premise
        (rawFormulaImpCode M sigmaBranch
          (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
        cellRoot premiseRoot)
      sigmaRoot)
    piRoot.

Arguments rawDynamicTruthQuantifierConditionalCellCollisionRoot
  M context premise sigmaBranch piBranch
    cellRoot premiseRoot sigmaRoot piRoot : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthQuantifierConditionalCellCollision :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context premise sigmaBranch piBranch
      cellRoot premiseRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M premise
      (rawFormulaImpCode M sigmaBranch
        (rawFormulaImpCode M piBranch (rawFormulaBotCode M))))
    cellRoot ->
  RawCodedPALocalProofOf M context premise premiseRoot ->
  RawCodedPALocalProofOf M context sigmaBranch sigmaRoot ->
  RawCodedPALocalProofOf M context piBranch piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthQuantifierConditionalCellCollisionRoot M context
      premise sigmaBranch piBranch
      cellRoot premiseRoot sigmaRoot piRoot).
Proof.
  intros M hPA context premise sigmaBranch piBranch
    cellRoot premiseRoot sigmaRoot piRoot
    hcell hpremise hsigma hpi.
  unfold rawDynamicTruthQuantifierConditionalCellCollisionRoot.
  apply (raw_codedPALocalProofOf_impE M hPA context
    piBranch (rawFormulaBotCode M)); [|exact hpi].
  apply (raw_codedPALocalProofOf_impE M hPA context
    sigmaBranch
    (rawFormulaImpCode M piBranch (rawFormulaBotCode M)));
    [|exact hsigma].
  exact (raw_codedPALocalProofOf_impE M hPA context
    premise
    (rawFormulaImpCode M sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
    cellRoot premiseRoot hcell hpremise).
Qed.

Definition rawDynamicTruthSigmaExPiExConditionalCellCollisionRoot
    (M : RawPAModel)
    (context lowerApplication cellRoot premiseRoot sigmaRoot piRoot : M)
    : M :=
  rawDynamicTruthQuantifierConditionalCellCollisionRoot M context
    (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M lowerApplication)
    (rawDynamicTruthSigmaEx8BranchCode M)
    (rawDynamicTruthPiExistentialEx8BranchCode M lowerApplication)
    cellRoot premiseRoot sigmaRoot piRoot.

Definition rawDynamicTruthSigmaAllPiAllConditionalCellCollisionRoot
    (M : RawPAModel)
    (context lowerApplication cellRoot premiseRoot sigmaRoot piRoot : M)
    : M :=
  rawDynamicTruthQuantifierConditionalCellCollisionRoot M context
    (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M lowerApplication)
    (rawDynamicTruthSigmaUniversalEx8BranchCode M lowerApplication)
    (rawDynamicTruthPiAllEx8BranchCode M)
    cellRoot premiseRoot sigmaRoot piRoot.

Arguments rawDynamicTruthSigmaExPiExConditionalCellCollisionRoot
  M context lowerApplication cellRoot premiseRoot sigmaRoot piRoot
  : clear implicits.
Arguments rawDynamicTruthSigmaAllPiAllConditionalCellCollisionRoot
  M context lowerApplication cellRoot premiseRoot sigmaRoot piRoot
  : clear implicits.

Corollary raw_codedPALocalProofOf_dynamicTruthSigmaExPiExCollision : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context lowerApplication cellRoot premiseRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaExPiExConditionalCellCode M lowerApplication)
    cellRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M lowerApplication)
    premiseRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaEx8BranchCode M) sigmaRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiExistentialEx8BranchCode M lowerApplication)
    piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthSigmaExPiExConditionalCellCollisionRoot M context
      lowerApplication cellRoot premiseRoot sigmaRoot piRoot).
Proof.
  intros M hPA context lowerApplication cellRoot premiseRoot
    sigmaRoot piRoot hcell hpremise hsigma hpi.
  unfold rawDynamicTruthSigmaExPiExConditionalCellCollisionRoot,
    rawDynamicTruthSigmaExPiExConditionalCellCode.
  exact
    (raw_codedPALocalProofOf_dynamicTruthQuantifierConditionalCellCollision
      M hPA context
      (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M lowerApplication)
      (rawDynamicTruthSigmaEx8BranchCode M)
      (rawDynamicTruthPiExistentialEx8BranchCode M lowerApplication)
      cellRoot premiseRoot sigmaRoot piRoot
      hcell hpremise hsigma hpi).
Qed.

Corollary raw_codedPALocalProofOf_dynamicTruthSigmaAllPiAllCollision : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context lowerApplication cellRoot premiseRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaAllPiAllConditionalCellCode M lowerApplication)
    cellRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M lowerApplication)
    premiseRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaUniversalEx8BranchCode M lowerApplication)
    sigmaRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiAllEx8BranchCode M) piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthSigmaAllPiAllConditionalCellCollisionRoot M context
      lowerApplication cellRoot premiseRoot sigmaRoot piRoot).
Proof.
  intros M hPA context lowerApplication cellRoot premiseRoot
    sigmaRoot piRoot hcell hpremise hsigma hpi.
  unfold rawDynamicTruthSigmaAllPiAllConditionalCellCollisionRoot,
    rawDynamicTruthSigmaAllPiAllConditionalCellCode.
  exact
    (raw_codedPALocalProofOf_dynamicTruthQuantifierConditionalCellCollision
      M hPA context
      (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M lowerApplication)
      (rawDynamicTruthSigmaUniversalEx8BranchCode M lowerApplication)
      (rawDynamicTruthPiAllEx8BranchCode M)
      cellRoot premiseRoot sigmaRoot piRoot
      hcell hpremise hsigma hpi).
Qed.

(** ------------------------------------------------------------------
    Reuse of the restricted quantifier projection interfaces.

    These are deliberately implication-elimination helpers, not claims that
    an arbitrary full disjunctive row has already selected the indicated
    branch.  The antecedents are the exact restricted rows compiled by the
    existing universal/existential projection modules. *)

Definition rawDynamicTruthSigmaRestrictedUniversalBranchRoot
    (M : RawPAModel)
    (context domain lowerApplication projectionRoot rowRoot : M) : M :=
  rawProofImpERoot M context
    (rawFormulaEx8Code M
      (rawFormulaAndCode M domain
        (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
          lowerApplication)))
    (rawDynamicTruthSigmaUniversalEx8BranchCode M lowerApplication)
    projectionRoot rowRoot.

Definition rawDynamicTruthPiRestrictedExistentialBranchRoot
    (M : RawPAModel)
    (context domain lowerApplication projectionRoot rowRoot : M) : M :=
  rawProofImpERoot M context
    (rawDynamicTruthPiFormulaEx8Code M
      (rawFormulaAndCode M domain
        (rawCoqDynamicTruthPiExistentialLeafTemplateCode M
          lowerApplication)))
    (rawDynamicTruthPiExistentialEx8BranchCode M lowerApplication)
    projectionRoot rowRoot.

Theorem raw_codedPALocalProofOf_dynamicTruthSigmaRestrictedUniversalBranch :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context domain lowerApplication projectionRoot rowRoot,
  RawCodedPALocalProofOf M context
    (rawCoqDynamicTruthSigmaRestrictedUniversalProjectionCode M
      domain lowerApplication)
    projectionRoot ->
  RawCodedPALocalProofOf M context
    (rawFormulaEx8Code M
      (rawFormulaAndCode M domain
        (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
          lowerApplication)))
    rowRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaUniversalEx8BranchCode M lowerApplication)
    (rawDynamicTruthSigmaRestrictedUniversalBranchRoot M context
      domain lowerApplication projectionRoot rowRoot).
Proof.
  intros M hPA context domain lowerApplication projectionRoot rowRoot
    hprojection hrow.
  unfold rawDynamicTruthSigmaRestrictedUniversalBranchRoot,
    rawCoqDynamicTruthSigmaRestrictedUniversalProjectionCode,
    rawDynamicTruthSigmaUniversalEx8BranchCode.
  exact (raw_codedPALocalProofOf_impE M hPA context
    (rawFormulaEx8Code M
      (rawFormulaAndCode M domain
        (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
          lowerApplication)))
    (rawFormulaEx8Code M
      (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
        lowerApplication))
    projectionRoot rowRoot hprojection hrow).
Qed.

Theorem raw_codedPALocalProofOf_dynamicTruthPiRestrictedExistentialBranch :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context domain lowerApplication projectionRoot rowRoot,
  RawCodedPALocalProofOf M context
    (rawCoqDynamicTruthPiRestrictedExistentialProjectionCode M
      domain lowerApplication)
    projectionRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiFormulaEx8Code M
      (rawFormulaAndCode M domain
        (rawCoqDynamicTruthPiExistentialLeafTemplateCode M
          lowerApplication)))
    rowRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiExistentialEx8BranchCode M lowerApplication)
    (rawDynamicTruthPiRestrictedExistentialBranchRoot M context
      domain lowerApplication projectionRoot rowRoot).
Proof.
  intros M hPA context domain lowerApplication projectionRoot rowRoot
    hprojection hrow.
  unfold rawDynamicTruthPiRestrictedExistentialBranchRoot,
    rawCoqDynamicTruthPiRestrictedExistentialProjectionCode,
    rawDynamicTruthPiExistentialEx8BranchCode.
  exact (raw_codedPALocalProofOf_impE M hPA context
    (rawDynamicTruthPiFormulaEx8Code M
      (rawFormulaAndCode M domain
        (rawCoqDynamicTruthPiExistentialLeafTemplateCode M
          lowerApplication)))
    (rawDynamicTruthPiFormulaEx8Code M
      (rawCoqDynamicTruthPiExistentialLeafTemplateCode M
        lowerApplication))
    projectionRoot rowRoot hprojection hrow).
Qed.

End PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
