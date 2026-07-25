(**
  Accumulator primitives for concatenating fixed-level truth traversals.

  Boolean Tarski clauses often need two independently constructed child
  certificates in one common state table.  This module starts the honest
  concatenation construction.  Its append theorem strengthens the earlier
  root-oriented append operation by returning the full prefix embedding from
  the old tables into the new ones.  That extra data is what preserves every
  previously chosen child root while subsequent traversals are copied after
  it.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedAssignment RawCodedProofDescent
  RawCodedFormulaRankStep RawCodedFormulaRankTotality
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthReindexing.

Module PABoundedRawCodedFixedLevelTruthConcatenation.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthReindexing.

(** A positive-level table bundle omits a distinguished root: it consists of
    four defined state columns and closure of every live row. *)
Definition RawFixedLevelPositiveTraversalBundle (M : RawPAModel)
    (lower : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound : M) : Prop :=
  RawCodedAssignmentDefinedThrough M modeCode modeStep bound /\
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound /\
  RawCodedAssignmentDefinedThrough M
    assignmentCodeCode assignmentCodeStep bound /\
  RawCodedAssignmentDefinedThrough M
    assignmentStepCode assignmentStepStep bound /\
  RawFixedLevelSuccessorTruthTraversalRows M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound.

Arguments RawFixedLevelPositiveTraversalBundle M lower
  modeCode modeStep formulaCode formulaStep
  assignmentCodeCode assignmentCodeStep
  assignmentStepCode assignmentStepStep bound : clear implicits.

Definition fixedTruthConcatAnd5 (a b c d f : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d f))).

Definition fixedTruthConcatAnd3 (a b c : formula) : formula :=
  pAnd a (pAnd b c).

Definition fixedTruthConcatEx8 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx body))))))).

Definition fixedLevelPositiveTraversalBundleTermAt (lower : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound : term) : formula :=
  fixedTruthConcatAnd5
    (codedAssignmentDefinedThroughTermAt modeCode modeStep bound)
    (codedAssignmentDefinedThroughTermAt formulaCode formulaStep bound)
    (codedAssignmentDefinedThroughTermAt
      assignmentCodeCode assignmentCodeStep bound)
    (codedAssignmentDefinedThroughTermAt
      assignmentStepCode assignmentStepStep bound)
    (fixedLevelSuccessorTruthTraversalRowsTermAt lower
      (fun child childAssignmentCode childAssignmentStep =>
        fixedLevelSigmaTruthCertificateTermAt lower
          child childAssignmentCode childAssignmentStep)
      (fun child childAssignmentCode childAssignmentStep =>
        fixedLevelPiFalsityCertificateTermAt lower
          child childAssignmentCode childAssignmentStep)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound).

Lemma raw_sat_fixedLevelPositiveTraversalBundleTermAt_iff : forall
    (M : RawPAModel) e lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound,
  raw_formula_sat M e
    (fixedLevelPositiveTraversalBundleTermAt lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound) <->
  RawFixedLevelPositiveTraversalBundle M lower
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold fixedLevelPositiveTraversalBundleTermAt,
    fixedTruthConcatAnd5, RawFixedLevelPositiveTraversalBundle.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite (raw_sat_fixedLevelSuccessorTruthTraversalRowsTermAt_iff
    M
    (fun child childAssignmentCode childAssignmentStep =>
      fixedLevelSigmaTruthCertificateTermAt lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      fixedLevelPiFalsityCertificateTermAt lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun e' code assignmentCode assignmentStep =>
      raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff
        lower M e' code assignmentCode assignmentStep)
    (fun e' code assignmentCode assignmentStep =>
      raw_sat_fixedLevelPiFalsityCertificateTermAt_iff
        lower M e' code assignmentCode assignmentStep)).
  reflexivity.
Qed.

(** The guarded induction state used to copy a source traversal.  At prefix
    [current] it returns target tables of length [offset + current], retains
    one distinguished state from the initial target prefix, and embeds every
    source state below [current] at its shifted index. *)
Definition RawFixedLevelTraversalCopyState (M : RawPAModel)
    (lower : nat)
    (sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      sourceBound offset
      initialRootIndex initialRootMode initialRoot initialAssignmentCode
      initialAssignmentStep current : M) : Prop :=
  rawLe M current sourceBound ->
  exists targetModeCode targetModeStep targetFormulaCode targetFormulaStep
      targetAssignmentCodeCode targetAssignmentCodeStep
      targetAssignmentStepCode targetAssignmentStepStep : M,
    RawFixedLevelPositiveTraversalBundle M lower
      targetModeCode targetModeStep targetFormulaCode targetFormulaStep
      targetAssignmentCodeCode targetAssignmentCodeStep
      targetAssignmentStepCode targetAssignmentStepStep
      (raw_add M offset current) /\
    RawFixedLevelStateLookup M
      targetModeCode targetModeStep targetFormulaCode targetFormulaStep
      targetAssignmentCodeCode targetAssignmentCodeStep
      targetAssignmentStepCode targetAssignmentStepStep
      initialRootIndex initialRootMode initialRoot
      initialAssignmentCode initialAssignmentStep /\
    RawFixedLevelStateOffsetEmbedding M offset current
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      targetModeCode targetModeStep targetFormulaCode targetFormulaStep
      targetAssignmentCodeCode targetAssignmentCodeStep
      targetAssignmentStepCode targetAssignmentStepStep.

Arguments RawFixedLevelTraversalCopyState M lower
  sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
  sourceAssignmentCodeCode sourceAssignmentCodeStep
  sourceAssignmentStepCode sourceAssignmentStepStep
  sourceBound offset initialRootIndex initialRootMode initialRoot
  initialAssignmentCode initialAssignmentStep current : clear implicits.

Definition fixedLevelTraversalCopyStateTermAt (lower : nat)
    (sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      sourceBound offset
      initialRootIndex initialRootMode initialRoot initialAssignmentCode
      initialAssignmentStep current : term) : formula :=
  pImp
    (Formula.leTermAt current sourceBound)
    (fixedTruthConcatEx8
      (fixedTruthConcatAnd3
        (fixedLevelPositiveTraversalBundleTermAt lower
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (tAdd (liftTerm 8 offset) (liftTerm 8 current)))
        (fixedLevelStateLookupTermAt
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (liftTerm 8 initialRootIndex)
          (liftTerm 8 initialRootMode) (liftTerm 8 initialRoot)
          (liftTerm 8 initialAssignmentCode)
          (liftTerm 8 initialAssignmentStep))
        (fixedLevelStateOffsetEmbeddingTermAt
          (liftTerm 8 offset) (liftTerm 8 current)
          (liftTerm 8 sourceModeCode) (liftTerm 8 sourceModeStep)
          (liftTerm 8 sourceFormulaCode) (liftTerm 8 sourceFormulaStep)
          (liftTerm 8 sourceAssignmentCodeCode)
          (liftTerm 8 sourceAssignmentCodeStep)
          (liftTerm 8 sourceAssignmentStepCode)
          (liftTerm 8 sourceAssignmentStepStep)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)))).

Lemma raw_fixedTruthConcat_eval_liftTerm_eight : forall
    (M : RawPAModel) a b c d f g h i (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i e))))))))
    (liftTerm 8 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro k.
  replace (k + 8) with (S (S (S (S (S (S (S (S k)))))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_fixedLevelTraversalCopyStateTermAt_iff : forall
    (M : RawPAModel) e lower
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      sourceBound offset initialRootIndex initialRootMode initialRoot
      initialAssignmentCode initialAssignmentStep current,
  raw_formula_sat M e
    (fixedLevelTraversalCopyStateTermAt lower
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      sourceBound offset initialRootIndex initialRootMode initialRoot
      initialAssignmentCode initialAssignmentStep current) <->
  RawFixedLevelTraversalCopyState M lower
    (raw_term_eval M e sourceModeCode)
    (raw_term_eval M e sourceModeStep)
    (raw_term_eval M e sourceFormulaCode)
    (raw_term_eval M e sourceFormulaStep)
    (raw_term_eval M e sourceAssignmentCodeCode)
    (raw_term_eval M e sourceAssignmentCodeStep)
    (raw_term_eval M e sourceAssignmentStepCode)
    (raw_term_eval M e sourceAssignmentStepStep)
    (raw_term_eval M e sourceBound) (raw_term_eval M e offset)
    (raw_term_eval M e initialRootIndex)
    (raw_term_eval M e initialRootMode) (raw_term_eval M e initialRoot)
    (raw_term_eval M e initialAssignmentCode)
    (raw_term_eval M e initialAssignmentStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold fixedLevelTraversalCopyStateTermAt,
    fixedTruthConcatEx8, fixedTruthConcatAnd3,
    RawFixedLevelTraversalCopyState.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank.
  setoid_rewrite raw_sat_fixedLevelPositiveTraversalBundleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelStateLookupTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelStateOffsetEmbeddingTermAt_iff.
  repeat setoid_rewrite raw_fixedTruthConcat_eval_liftTerm_eight.
  cbn [raw_term_eval scons].
  split; intros h hle;
    destruct (h hle) as
      (targetModeCode & targetModeStep & targetFormulaCode &
       targetFormulaStep & targetAssignmentCodeCode &
       targetAssignmentCodeStep & targetAssignmentStepCode &
       targetAssignmentStepStep & hresult);
    exists targetModeCode, targetModeStep, targetFormulaCode,
      targetFormulaStep, targetAssignmentCodeCode,
      targetAssignmentCodeStep, targetAssignmentStepCode,
      targetAssignmentStepStep.
  - repeat rewrite raw_fixedTruthConcat_eval_liftTerm_eight in hresult.
    exact hresult.
  - repeat rewrite raw_fixedTruthConcat_eval_liftTerm_eight.
    exact hresult.
Qed.

Lemma raw_add_zero_right_fixedTruthConcat : forall
    (M : RawPAModel), RawPASatisfies M -> forall value,
  raw_add M value (raw_zero M) = value.
Proof.
  intros M hPA value.
  set (e := scons M value (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_addZero_term nil (tVar 0)) e) as hadd.
  unfold e in hadd. cbn [raw_formula_sat raw_term_eval scons] in hadd.
  exact hadd.
Qed.

Lemma raw_fixedLevelStateOffsetEmbedding_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      offset
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      targetModeCode targetModeStep targetFormulaCode targetFormulaStep
      targetAssignmentCodeCode targetAssignmentCodeStep
      targetAssignmentStepCode targetAssignmentStepStep,
  RawFixedLevelStateOffsetEmbedding M offset (raw_zero M)
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    targetModeCode targetModeStep targetFormulaCode targetFormulaStep
    targetAssignmentCodeCode targetAssignmentCodeStep
    targetAssignmentStepCode targetAssignmentStepStep.
Proof.
  intros M hPA offset
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    targetModeCode targetModeStep targetFormulaCode targetFormulaStep
    targetAssignmentCodeCode targetAssignmentCodeStep
    targetAssignmentStepCode targetAssignmentStepStep
    index mode code assignmentCode assignmentStep hindex _.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Theorem raw_fixedLevelTraversalCopyState_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lower
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep sourceBound
      offset
      initialModeCode initialModeStep initialFormulaCode initialFormulaStep
      initialAssignmentCodeCode initialAssignmentCodeStep
      initialAssignmentStepCode initialAssignmentStepStep
      initialRootIndex initialRootMode initialRoot
      initialAssignmentCode initialAssignmentStep,
  RawFixedLevelPositiveTraversalBundle M lower
    initialModeCode initialModeStep initialFormulaCode initialFormulaStep
    initialAssignmentCodeCode initialAssignmentCodeStep
    initialAssignmentStepCode initialAssignmentStepStep offset ->
  RawFixedLevelStateLookup M
    initialModeCode initialModeStep initialFormulaCode initialFormulaStep
    initialAssignmentCodeCode initialAssignmentCodeStep
    initialAssignmentStepCode initialAssignmentStepStep
    initialRootIndex initialRootMode initialRoot
    initialAssignmentCode initialAssignmentStep ->
  RawFixedLevelTraversalCopyState M lower
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    sourceBound offset initialRootIndex initialRootMode initialRoot
    initialAssignmentCode initialAssignmentStep (raw_zero M).
Proof.
  intros M hPA lower
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep sourceBound
    offset
    initialModeCode initialModeStep initialFormulaCode initialFormulaStep
    initialAssignmentCodeCode initialAssignmentCodeStep
    initialAssignmentStepCode initialAssignmentStepStep
    initialRootIndex initialRootMode initialRoot
    initialAssignmentCode initialAssignmentStep hinitialBundle
    hinitialLookup _.
  exists initialModeCode, initialModeStep, initialFormulaCode,
    initialFormulaStep, initialAssignmentCodeCode,
    initialAssignmentCodeStep, initialAssignmentStepCode,
    initialAssignmentStepStep.
  rewrite raw_add_zero_right_fixedTruthConcat by exact hPA.
  split; [exact hinitialBundle |]. split; [exact hinitialLookup |].
  exact (raw_fixedLevelStateOffsetEmbedding_zero M hPA offset
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    initialModeCode initialModeStep initialFormulaCode initialFormulaStep
    initialAssignmentCodeCode initialAssignmentCodeStep
    initialAssignmentStepCode initialAssignmentStepStep).
Qed.

(** Internal placement of the prefix-retaining append primitive.  The public
    theorem with the same statement appears below with the other bundle APIs;
    this local name is placed before the copy-successor lemma so Rocq's
    declaration order mirrors the accumulator dependency. *)
Lemma raw_fixedLevelPositiveTraversalBundle_append_internal : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode code assignmentCode assignmentStep,
  RawFixedLevelPositiveTraversalBundle M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound ->
  RawFixedLevelClosedSuccessorRow M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode code assignmentCode assignmentStep ->
  exists newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep : M,
    RawFixedLevelPositiveTraversalBundle M lower
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep (raw_succ M bound) /\
    RawFixedLevelStateTablePrefixExtension M bound
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep /\
    RawFixedLevelStateLookup M
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      bound mode code assignmentCode assignmentStep.
Proof.
  intros M hPA lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode code assignmentCode assignmentStep
    [hmodeDefined [hformulaDefined
      [hassignmentCodeDefined [hassignmentStepDefined hrows]]]] hclosed.
  destruct (raw_fixedLevelStateTablesAppend M hPA
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode code assignmentCode assignmentStep
    hmodeDefined hformulaDefined
    hassignmentCodeDefined hassignmentStepDefined)
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep &
        hnewModeDefined & hnewFormulaDefined &
        hnewAssignmentCodeDefined & hnewAssignmentStepDefined &
        hmodePrefix & hformulaPrefix &
        hassignmentCodePrefix & hassignmentStepPrefix & hnewLookup).
  assert (hext : RawFixedLevelStateTablePrefixExtension M bound
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep).
  { repeat split; assumption. }
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep.
  split.
  - repeat split; try assumption.
    intros index rowMode rowCode rowAssignmentCode rowAssignmentStep
      hindex hrowLookup.
    destruct (raw_lt_succ_cases M hPA index bound hindex)
      as [hindexBound | ->].
    + pose proof (raw_fixedLevelStateLookup_prefix_reflect M hPA bound
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        index rowMode rowCode rowAssignmentCode rowAssignmentStep
        hmodeDefined hformulaDefined
        hassignmentCodeDefined hassignmentStepDefined
        hext hindexBound hrowLookup) as holdLookup.
      exact (raw_fixedLevelClosedSuccessorRow_prefix_extend M hPA
        lower
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M lower
            child childAssignmentCode childAssignmentStep)
        bound index
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        rowMode rowCode rowAssignmentCode rowAssignmentStep
        hext (raw_lt_to_le M index bound hindexBound)
        (hrows index rowMode rowCode rowAssignmentCode rowAssignmentStep
          hindexBound holdLookup)).
    + destruct (raw_fixedLevelStateLookup_functional M hPA
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        bound mode code assignmentCode assignmentStep
        rowMode rowCode rowAssignmentCode rowAssignmentStep
        hnewLookup hrowLookup)
        as [hmode [hcode [hassignmentCode hassignmentStep]]].
      subst rowMode. subst rowCode.
      subst rowAssignmentCode. subst rowAssignmentStep.
      exact (raw_fixedLevelClosedSuccessorRow_prefix_extend M hPA
        lower
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M lower
            child childAssignmentCode childAssignmentStep)
        bound bound
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        mode code assignmentCode assignmentStep
        hext (raw_rank_le_refl M hPA bound) hclosed).
  - split; assumption.
Qed.

Theorem raw_fixedLevelTraversalCopyState_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lower
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      sourceBound sourceRootIndex sourceRootMode sourceRoot
      sourceRootAssignmentCode sourceRootAssignmentStep
      offset initialRootIndex initialRootMode initialRoot
      initialAssignmentCode initialAssignmentStep current,
  RawFixedLevelSuccessorTruthTraversal M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    sourceBound sourceRootIndex sourceRootMode sourceRoot
    sourceRootAssignmentCode sourceRootAssignmentStep ->
  rawLt M initialRootIndex offset ->
  RawFixedLevelTraversalCopyState M lower
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    sourceBound offset initialRootIndex initialRootMode initialRoot
    initialAssignmentCode initialAssignmentStep current ->
  RawFixedLevelTraversalCopyState M lower
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    sourceBound offset initialRootIndex initialRootMode initialRoot
    initialAssignmentCode initialAssignmentStep (raw_succ M current).
Proof.
  intros M hPA lower
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    sourceBound sourceRootIndex sourceRootMode sourceRoot
    sourceRootAssignmentCode sourceRootAssignmentStep
    offset initialRootIndex initialRootMode initialRoot
    initialAssignmentCode initialAssignmentStep current
    hsource hinitialBelow hcurrent hsuccLe.
  assert (hcurrentBelow : rawLt M current sourceBound).
  { exact (raw_rank_lt_of_succ_le M hPA current sourceBound hsuccLe). }
  assert (hcurrentLe : rawLe M current sourceBound).
  { exact (raw_lt_to_le M current sourceBound hcurrentBelow). }
  destruct (hcurrent hcurrentLe) as
    (targetModeCode & targetModeStep & targetFormulaCode &
     targetFormulaStep & targetAssignmentCodeCode &
     targetAssignmentCodeStep & targetAssignmentStepCode &
     targetAssignmentStepStep & htargetBundle & hinitialLookup & hembed).
  destruct (raw_fixedLevelSuccessorTruthTraversal_row_exists_unique
    M hPA lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    sourceBound sourceRootIndex sourceRootMode sourceRoot
    sourceRootAssignmentCode sourceRootAssignmentStep
    hsource current hcurrentBelow)
    as (mode & code & rowAssignmentCode & rowAssignmentStep &
        hsourceLookup & hsourceClosed & hsourceFunctional).
  pose proof (raw_fixedLevelClosedSuccessorRow_offset M hPA lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    offset current
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    targetModeCode targetModeStep targetFormulaCode targetFormulaStep
    targetAssignmentCodeCode targetAssignmentCodeStep
    targetAssignmentStepCode targetAssignmentStepStep
    mode code rowAssignmentCode rowAssignmentStep
    hembed hsourceClosed) as hshiftedClosed.
  destruct (raw_fixedLevelPositiveTraversalBundle_append_internal M hPA lower
    targetModeCode targetModeStep targetFormulaCode targetFormulaStep
    targetAssignmentCodeCode targetAssignmentCodeStep
    targetAssignmentStepCode targetAssignmentStepStep
    (raw_add M offset current) mode code
    rowAssignmentCode rowAssignmentStep htargetBundle hshiftedClosed)
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep &
        hnewBundle & hprefix & hnewLookup).
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep.
  split.
  - rewrite raw_add_succ by exact hPA. exact hnewBundle.
  - split.
    + apply (raw_fixedLevelStateLookup_prefix_extend M
        (raw_add M offset current)
        targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        initialRootIndex initialRootMode initialRoot
        initialAssignmentCode initialAssignmentStep hprefix).
      * exact (raw_lt_le_trans_pair M hPA
          initialRootIndex offset (raw_add M offset current)
          hinitialBelow (raw_proof_left_le_sum M offset current)).
      * exact hinitialLookup.
    + intros index rowMode rowCode rowAssignmentCode' rowAssignmentStep'
        hindex hrowLookup.
      destruct (raw_lt_succ_cases M hPA index current hindex)
        as [hindexCurrent | ->].
      * apply (raw_fixedLevelStateLookup_prefix_extend M
          (raw_add M offset current)
          targetModeCode targetModeStep targetFormulaCode targetFormulaStep
          targetAssignmentCodeCode targetAssignmentCodeStep
          targetAssignmentStepCode targetAssignmentStepStep
          newModeCode newModeStep newFormulaCode newFormulaStep
          newAssignmentCodeCode newAssignmentCodeStep
          newAssignmentStepCode newAssignmentStepStep
          (raw_add M offset index) rowMode rowCode
          rowAssignmentCode' rowAssignmentStep' hprefix).
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             index current hindexCurrent).
        -- exact (hembed index rowMode rowCode
             rowAssignmentCode' rowAssignmentStep'
             hindexCurrent hrowLookup).
      * destruct (hsourceFunctional rowMode rowCode
          rowAssignmentCode' rowAssignmentStep' hrowLookup)
          as [hmode [hcode [hassignmentCode hassignmentStep]]].
        subst rowMode. subst rowCode.
        subst rowAssignmentCode'. subst rowAssignmentStep'.
        exact hnewLookup.
Qed.

(** PA induction copies every row through the possibly nonstandard source
    bound.  The fifteen fixed carrier parameters are stored in the tail
    environment; variable zero remains the induction index. *)
Theorem raw_fixedLevelTraversalCopyState_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lower
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      sourceBound sourceRootIndex sourceRootMode sourceRoot
      sourceRootAssignmentCode sourceRootAssignmentStep
      offset
      initialModeCode initialModeStep initialFormulaCode initialFormulaStep
      initialAssignmentCodeCode initialAssignmentCodeStep
      initialAssignmentStepCode initialAssignmentStepStep
      initialRootIndex initialRootMode initialRoot
      initialAssignmentCode initialAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    sourceBound sourceRootIndex sourceRootMode sourceRoot
    sourceRootAssignmentCode sourceRootAssignmentStep ->
  RawFixedLevelPositiveTraversalBundle M lower
    initialModeCode initialModeStep initialFormulaCode initialFormulaStep
    initialAssignmentCodeCode initialAssignmentCodeStep
    initialAssignmentStepCode initialAssignmentStepStep offset ->
  rawLt M initialRootIndex offset ->
  RawFixedLevelStateLookup M
    initialModeCode initialModeStep initialFormulaCode initialFormulaStep
    initialAssignmentCodeCode initialAssignmentCodeStep
    initialAssignmentStepCode initialAssignmentStepStep
    initialRootIndex initialRootMode initialRoot
    initialAssignmentCode initialAssignmentStep ->
  forall current,
  RawFixedLevelTraversalCopyState M lower
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    sourceBound offset initialRootIndex initialRootMode initialRoot
    initialAssignmentCode initialAssignmentStep current.
Proof.
  intros M hPA lower
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    sourceBound sourceRootIndex sourceRootMode sourceRoot
    sourceRootAssignmentCode sourceRootAssignmentStep
    offset
    initialModeCode initialModeStep initialFormulaCode initialFormulaStep
    initialAssignmentCodeCode initialAssignmentCodeStep
    initialAssignmentStepCode initialAssignmentStepStep
    initialRootIndex initialRootMode initialRoot
    initialAssignmentCode initialAssignmentStep
    hsource hinitialBundle hinitialBelow hinitialLookup.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => sourceModeCode
    | 1 => sourceModeStep
    | 2 => sourceFormulaCode
    | 3 => sourceFormulaStep
    | 4 => sourceAssignmentCodeCode
    | 5 => sourceAssignmentCodeStep
    | 6 => sourceAssignmentStepCode
    | 7 => sourceAssignmentStepStep
    | 8 => sourceBound
    | 9 => offset
    | 10 => initialRootIndex
    | 11 => initialRootMode
    | 12 => initialRoot
    | 13 => initialAssignmentCode
    | _ => initialAssignmentStep
    end).
  set (phi := fixedLevelTraversalCopyStateTermAt lower
    (tVar 1) (tVar 2) (tVar 3) (tVar 4)
    (tVar 5) (tVar 6) (tVar 7) (tVar 8)
    (tVar 9) (tVar 10) (tVar 11) (tVar 12)
    (tVar 13) (tVar 14) (tVar 15) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_fixedLevelTraversalCopyStateTermAt_iff M
        (scons M (raw_zero M) parameterEnv) lower
        (tVar 1) (tVar 2) (tVar 3) (tVar 4)
        (tVar 5) (tVar 6) (tVar 7) (tVar 8)
        (tVar 9) (tVar 10) (tVar 11) (tVar 12)
        (tVar 13) (tVar 14) (tVar 15) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_fixedLevelTraversalCopyState_zero M hPA lower
        sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
        sourceAssignmentCodeCode sourceAssignmentCodeStep
        sourceAssignmentStepCode sourceAssignmentStepStep sourceBound
        offset
        initialModeCode initialModeStep initialFormulaCode initialFormulaStep
        initialAssignmentCodeCode initialAssignmentCodeStep
        initialAssignmentStepCode initialAssignmentStepStep
        initialRootIndex initialRootMode initialRoot
        initialAssignmentCode initialAssignmentStep
        hinitialBundle hinitialLookup).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_fixedLevelTraversalCopyStateTermAt_iff M
          (scons M current parameterEnv) lower
          (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 8)
          (tVar 9) (tVar 10) (tVar 11) (tVar 12)
          (tVar 13) (tVar 14) (tVar 15) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_fixedLevelTraversalCopyStateTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) lower
        (tVar 1) (tVar 2) (tVar 3) (tVar 4)
        (tVar 5) (tVar 6) (tVar 7) (tVar 8)
        (tVar 9) (tVar 10) (tVar 11) (tVar 12)
        (tVar 13) (tVar 14) (tVar 15) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_fixedLevelTraversalCopyState_succ M hPA lower
        sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
        sourceAssignmentCodeCode sourceAssignmentCodeStep
        sourceAssignmentStepCode sourceAssignmentStepStep
        sourceBound sourceRootIndex sourceRootMode sourceRoot
        sourceRootAssignmentCode sourceRootAssignmentStep
        offset initialRootIndex initialRootMode initialRoot
        initialAssignmentCode initialAssignmentStep current
        hsource hinitialBelow hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_fixedLevelTraversalCopyStateTermAt_iff M
      (scons M current parameterEnv) lower
      (tVar 1) (tVar 2) (tVar 3) (tVar 4)
      (tVar 5) (tVar 6) (tVar 7) (tVar 8)
      (tVar 9) (tVar 10) (tVar 11) (tVar 12)
      (tVar 13) (tVar 14) (tVar 15) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Concatenate two complete successor traversals.  The second traversal is
    copied after the first, its distinguished root is shifted by the first
    bound, and the first distinguished root remains available at its original
    index. *)
Theorem raw_fixedLevelSuccessorTruthTraversals_concatenate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lower
      firstModeCode firstModeStep firstFormulaCode firstFormulaStep
      firstAssignmentCodeCode firstAssignmentCodeStep
      firstAssignmentStepCode firstAssignmentStepStep
      firstBound firstRootIndex firstRootMode firstRoot
      firstRootAssignmentCode firstRootAssignmentStep
      secondModeCode secondModeStep secondFormulaCode secondFormulaStep
      secondAssignmentCodeCode secondAssignmentCodeStep
      secondAssignmentStepCode secondAssignmentStepStep
      secondBound secondRootIndex secondRootMode secondRoot
      secondRootAssignmentCode secondRootAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    firstModeCode firstModeStep firstFormulaCode firstFormulaStep
    firstAssignmentCodeCode firstAssignmentCodeStep
    firstAssignmentStepCode firstAssignmentStepStep
    firstBound firstRootIndex firstRootMode firstRoot
    firstRootAssignmentCode firstRootAssignmentStep ->
  RawFixedLevelSuccessorTruthTraversal M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    secondModeCode secondModeStep secondFormulaCode secondFormulaStep
    secondAssignmentCodeCode secondAssignmentCodeStep
    secondAssignmentStepCode secondAssignmentStepStep
    secondBound secondRootIndex secondRootMode secondRoot
    secondRootAssignmentCode secondRootAssignmentStep ->
  exists newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep : M,
    RawFixedLevelSuccessorTruthTraversal M lower
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelSigmaTruthCertificate M lower
          child childAssignmentCode childAssignmentStep)
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelPiFalsityCertificate M lower
          child childAssignmentCode childAssignmentStep)
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      (raw_add M firstBound secondBound)
      (raw_add M firstBound secondRootIndex)
      secondRootMode secondRoot
      secondRootAssignmentCode secondRootAssignmentStep /\
    RawFixedLevelStateLookup M
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      firstRootIndex firstRootMode firstRoot
      firstRootAssignmentCode firstRootAssignmentStep.
Proof.
  intros M hPA lower
    firstModeCode firstModeStep firstFormulaCode firstFormulaStep
    firstAssignmentCodeCode firstAssignmentCodeStep
    firstAssignmentStepCode firstAssignmentStepStep
    firstBound firstRootIndex firstRootMode firstRoot
    firstRootAssignmentCode firstRootAssignmentStep
    secondModeCode secondModeStep secondFormulaCode secondFormulaStep
    secondAssignmentCodeCode secondAssignmentCodeStep
    secondAssignmentStepCode secondAssignmentStepStep
    secondBound secondRootIndex secondRootMode secondRoot
    secondRootAssignmentCode secondRootAssignmentStep
    hfirst hsecond.
  destruct hfirst as
    [hfirstMode [hfirstFormula [hfirstAssignmentCode
      [hfirstAssignmentStep
        [hfirstRootBelow [hfirstRootLookup hfirstRows]]]]]].
  assert (hfirstBundle : RawFixedLevelPositiveTraversalBundle M lower
      firstModeCode firstModeStep firstFormulaCode firstFormulaStep
      firstAssignmentCodeCode firstAssignmentCodeStep
      firstAssignmentStepCode firstAssignmentStepStep firstBound).
  { repeat split; assumption. }
  destruct hsecond as
    [hsecondMode [hsecondFormula [hsecondAssignmentCode
      [hsecondAssignmentStep
        [hsecondRootBelow [hsecondRootLookup hsecondRows]]]]]].
  assert (hsecondAgain : RawFixedLevelSuccessorTruthTraversal M lower
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelSigmaTruthCertificate M lower
          child childAssignmentCode childAssignmentStep)
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelPiFalsityCertificate M lower
          child childAssignmentCode childAssignmentStep)
      secondModeCode secondModeStep secondFormulaCode secondFormulaStep
      secondAssignmentCodeCode secondAssignmentCodeStep
      secondAssignmentStepCode secondAssignmentStepStep
      secondBound secondRootIndex secondRootMode secondRoot
      secondRootAssignmentCode secondRootAssignmentStep).
  { exact (conj hsecondMode
      (conj hsecondFormula
        (conj hsecondAssignmentCode
          (conj hsecondAssignmentStep
            (conj hsecondRootBelow
              (conj hsecondRootLookup hsecondRows)))))). }
  pose proof (raw_fixedLevelTraversalCopyState_all M hPA lower
    secondModeCode secondModeStep secondFormulaCode secondFormulaStep
    secondAssignmentCodeCode secondAssignmentCodeStep
    secondAssignmentStepCode secondAssignmentStepStep
    secondBound secondRootIndex secondRootMode secondRoot
    secondRootAssignmentCode secondRootAssignmentStep
    firstBound
    firstModeCode firstModeStep firstFormulaCode firstFormulaStep
    firstAssignmentCodeCode firstAssignmentCodeStep
    firstAssignmentStepCode firstAssignmentStepStep
    firstRootIndex firstRootMode firstRoot
    firstRootAssignmentCode firstRootAssignmentStep
    hsecondAgain hfirstBundle hfirstRootBelow hfirstRootLookup
    secondBound) as hcopiedGuard.
  destruct (hcopiedGuard (raw_rank_le_refl M hPA secondBound))
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep &
        hnewBundle & hfirstLookup & hembed).
  pose proof (hembed secondRootIndex secondRootMode secondRoot
    secondRootAssignmentCode secondRootAssignmentStep
    hsecondRootBelow hsecondRootLookup) as hsecondShiftedLookup.
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep.
  split.
  - destruct hnewBundle as
      [hnewMode [hnewFormula [hnewAssignmentCode
        [hnewAssignmentStep hnewRows]]]].
    exact (conj hnewMode
      (conj hnewFormula
        (conj hnewAssignmentCode
          (conj hnewAssignmentStep
            (conj
              (raw_lt_add_left_fixedTruth M hPA firstBound
                secondRootIndex secondBound hsecondRootBelow)
              (conj hsecondShiftedLookup hnewRows)))))).
  - exact hfirstLookup.
Qed.

Lemma raw_fixedLevelPositiveTraversalBundle_of_traversal : forall
    (M : RawPAModel) lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  RawFixedLevelPositiveTraversalBundle M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound.
Proof.
  intros M lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    [hmode [hformula [hassignmentCode [hassignmentStep [_ [_ hrows]]]]]].
  repeat split; assumption.
Qed.

(** Append one already closed row and retain both the resulting bundle and
    the exact old-prefix embedding.  The proof uses arbitrary-value beta
    append for all four columns and rechecks every old row against the new
    tables; no external finite-vector construction is hidden here. *)
Theorem raw_fixedLevelPositiveTraversalBundle_append : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode code assignmentCode assignmentStep,
  RawFixedLevelPositiveTraversalBundle M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound ->
  RawFixedLevelClosedSuccessorRow M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode code assignmentCode assignmentStep ->
  exists newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep : M,
    RawFixedLevelPositiveTraversalBundle M lower
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep (raw_succ M bound) /\
    RawFixedLevelStateTablePrefixExtension M bound
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep /\
    RawFixedLevelStateLookup M
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      bound mode code assignmentCode assignmentStep.
Proof.
  intros M hPA lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode code assignmentCode assignmentStep
    [hmodeDefined [hformulaDefined
      [hassignmentCodeDefined [hassignmentStepDefined hrows]]]] hclosed.
  destruct (raw_fixedLevelStateTablesAppend M hPA
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode code assignmentCode assignmentStep
    hmodeDefined hformulaDefined
    hassignmentCodeDefined hassignmentStepDefined)
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep &
        hnewModeDefined & hnewFormulaDefined &
        hnewAssignmentCodeDefined & hnewAssignmentStepDefined &
        hmodePrefix & hformulaPrefix &
        hassignmentCodePrefix & hassignmentStepPrefix & hnewLookup).
  assert (hext : RawFixedLevelStateTablePrefixExtension M bound
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep).
  { repeat split; assumption. }
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep.
  split.
  - repeat split; try assumption.
    intros index rowMode rowCode rowAssignmentCode rowAssignmentStep
      hindex hrowLookup.
    destruct (raw_lt_succ_cases M hPA index bound hindex)
      as [hindexBound | ->].
    + pose proof (raw_fixedLevelStateLookup_prefix_reflect M hPA bound
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        index rowMode rowCode rowAssignmentCode rowAssignmentStep
        hmodeDefined hformulaDefined
        hassignmentCodeDefined hassignmentStepDefined
        hext hindexBound hrowLookup) as holdLookup.
      exact (raw_fixedLevelClosedSuccessorRow_prefix_extend M hPA
        lower
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M lower
            child childAssignmentCode childAssignmentStep)
        bound index
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        rowMode rowCode rowAssignmentCode rowAssignmentStep
        hext (raw_lt_to_le M index bound hindexBound)
        (hrows index rowMode rowCode rowAssignmentCode rowAssignmentStep
          hindexBound holdLookup)).
    + destruct (raw_fixedLevelStateLookup_functional M hPA
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        bound mode code assignmentCode assignmentStep
        rowMode rowCode rowAssignmentCode rowAssignmentStep
        hnewLookup hrowLookup)
        as [hmode [hcode [hassignmentCode hassignmentStep]]].
      subst rowMode. subst rowCode.
      subst rowAssignmentCode. subst rowAssignmentStep.
      exact (raw_fixedLevelClosedSuccessorRow_prefix_extend M hPA
        lower
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M lower
            child childAssignmentCode childAssignmentStep)
        bound bound
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        mode code assignmentCode assignmentStep
        hext (raw_rank_le_refl M hPA bound) hclosed).
  - split; assumption.
Qed.

End PABoundedRawCodedFixedLevelTruthConcatenation.
