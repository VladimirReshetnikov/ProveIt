(**
  Totality of iterated universal closure at an arbitrary carrier count.

  A metatheoretic list of [count + 1] formula codes is not available when
  [count] is nonstandard.  The carrier-indexed orbit graph already solves
  precisely this problem: its beta table is grown by PA's represented
  induction.  Here its base is the input code and its successor is the
  universal-formula constructor.  Forgetting the generic orbit wrapper then
  gives the existing [RawCodedUniversalClosure] graph.

  This file also records two consequences needed by the direct strong-prefix
  soundness construction.

  - A represented formula operation contains an honest postorder traversal
    of its source, hence its source is a well-formed carrier formula code.
  - Once the remaining formula-bound and all-depth diagonal certificates are
    supplied, universal-closure existence and the complete self-instantiation
    orbit are no longer hypotheses: they follow uniformly at the possibly
    nonstandard bound.

  Notice the deliberate domain boundary.  [RawCodedFormulaBound] cannot be
  total on every carrier element, since malformed numbers are not formula
  codes.  The well-formedness result below proves that the direct induction
  body lies in the honest syntax domain; constructing its bound table from
  that nonstandard traversal is the remaining fold-totality problem.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaRankTotality
  RawCodedFormulaOperations
  RawCodedPAAxiomWitness
  RawCodedCarrierIndexedCodeOrbitGraph
  RawCodedUniversalClosureDiagonalSubstitution
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

Module PABoundedRawCodedUniversalClosureAllCarrierTotality.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedCarrierIndexedCodeOrbitGraph.
Import PABoundedRawCodedUniversalClosureDiagonalSubstitution.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

(** ------------------------------------------------------------------
    Universal closure as a carrier-indexed orbit. *)

(** Under [base :: input :: tail], the base row says [base = input]. *)
Definition universalClosureOrbitBaseGraph : formula :=
  pEq (tVar 0) (tVar 1).

(** Under [next :: previous :: index :: input :: tail], the successor row
    says [next = all(previous)]. *)
Definition universalClosureOrbitSuccessorGraph : formula :=
  formulaAllCodeTermAt (tVar 0) (tVar 1).

Lemma raw_universalClosureOrbitBase_total : forall (M : RawPAModel),
  RawCarrierIndexedCodeOrbitBaseTotal M universalClosureOrbitBaseGraph.
Proof.
  intros M tail.
  exists (tail 0).
  unfold universalClosureOrbitBaseGraph.
  cbn [raw_formula_sat raw_term_eval scons].
  reflexivity.
Qed.

Lemma raw_universalClosureOrbitSuccessor_total : forall
    (M : RawPAModel),
  RawCarrierIndexedCodeOrbitSuccessorTotal M
    universalClosureOrbitSuccessorGraph.
Proof.
  intros M tail index previous.
  exists (rawFormulaAllCode M previous).
  unfold universalClosureOrbitSuccessorGraph.
  apply (proj2 (raw_sat_formulaAllCodeTermAt_iff M _
    (tVar 0) (tVar 1))).
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

(** The generic orbit has exactly the table fields of universal closure.
    The base and successor graphs merely expose the two equations which the
    specialized relation stores directly. *)
Lemma raw_carrierIndexedCodeOrbitAt_to_codedUniversalClosure : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail count output,
  RawCarrierIndexedCodeOrbitAt M
    universalClosureOrbitBaseGraph universalClosureOrbitSuccessorGraph
    tail count output ->
  RawCodedUniversalClosure M count (tail 0) output.
Proof.
  intros M hPA tail count output
    (code & step & base & hdefined & hzero & hbase & hrows & houtput).
  unfold universalClosureOrbitBaseGraph in hbase.
  cbn [raw_formula_sat raw_term_eval scons] in hbase.
  subst base.
  exists code, step.
  unfold RawCodedUniversalClosureTrace.
  repeat split.
  - exact hdefined.
  - exact hzero.
  - exact houtput.
  - intros index current next hindex hcurrent hnext.
    specialize (hrows index current next hindex hcurrent hnext).
    unfold universalClosureOrbitSuccessorGraph in hrows.
    apply (proj1 (raw_sat_formulaAllCodeTermAt_iff M _
      (tVar 0) (tVar 1))) in hrows.
    cbn [raw_term_eval scons] in hrows.
    exact hrows.
  - exact (raw_rank_zero_le M hPA count).
Qed.

(** Existence is genuinely uniform in [count : M].  The induction which
    grows the beta table is [raw_carrierIndexedCodeOrbitExists_all], hence no
    Rocq recursion or standardness assumption occurs here. *)
Theorem raw_codedUniversalClosure_exists_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall count input,
  exists output : M, RawCodedUniversalClosure M count input output.
Proof.
  intros M hPA count input.
  set (tail := fun index : nat =>
    match index with
    | 0 => input
    | _ => raw_zero M
    end).
  destruct (raw_carrierIndexedCodeOrbitExists_all M hPA
    universalClosureOrbitBaseGraph universalClosureOrbitSuccessorGraph
    (raw_universalClosureOrbitBase_total M)
    (raw_universalClosureOrbitSuccessor_total M)
    tail count) as [output horbit].
  exists output.
  change input with (tail 0).
  exact (raw_carrierIndexedCodeOrbitAt_to_codedUniversalClosure
    M hPA tail count output horbit).
Qed.

(** Existing graph functionality and the new totality theorem combine into
    a unique-output statement over the full carrier. *)
Corollary raw_codedUniversalClosure_exists_unique_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall count input,
  exists output : M,
    RawCodedUniversalClosure M count input output /\
    forall other,
      RawCodedUniversalClosure M count input other -> other = output.
Proof.
  intros M hPA count input.
  destruct (raw_codedUniversalClosure_exists_all M hPA count input)
    as [output houtput].
  exists output. split; [exact houtput |].
  intros other hother.
  exact (raw_codedUniversalClosure_functional M hPA
    count input other output hother houtput).
Qed.

(** ------------------------------------------------------------------
    Formula-operation sources are honest formula codes. *)

(** Forget target and depth data in one operation row.  Child source
    lookups are the first projections of the synchronized triple lookups. *)
Lemma raw_codedFormulaOperationTraversalRow_source_syntax : forall
    (M : RawPAModel) atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth,
  RawCodedFormulaOperationTraversalRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth ->
  RawCodedFormulaSyntaxTraversalRow M
    sourceCode sourceStep index input.
Proof.
  intros M atom parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - destruct heq as
      (inputLeft & outputLeft & inputRight & outputRight &
        hinput & _ & _ & _).
    left. exists inputLeft, inputRight. exact hinput.
  - right. left. exact (proj1 hbot).
  - right. right. left.
    destruct himp as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & _).
    exists leftIndex, inputLeft, rightIndex, inputRight.
    repeat split; try assumption.
    + exact (proj1 hleftLookup).
    + exact (proj1 hrightLookup).
  - right. right. right. left.
    destruct hand as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & _).
    exists leftIndex, inputLeft, rightIndex, inputRight.
    repeat split; try assumption.
    + exact (proj1 hleftLookup).
    + exact (proj1 hrightLookup).
  - right. right. right. right. left.
    destruct hor as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & _).
    exists leftIndex, inputLeft, rightIndex, inputRight.
    repeat split; try assumption.
    + exact (proj1 hleftLookup).
    + exact (proj1 hrightLookup).
  - right. right. right. right. right. left.
    destruct hall as
      (childIndex & inputChild & outputChild & childDepth &
       hchildIndex & hchildLookup & _ & hinput & _).
    exists childIndex, inputChild.
    repeat split; try assumption.
    exact (proj1 hchildLookup).
  - right. right. right. right. right. right.
    destruct hex as
      (childIndex & inputChild & outputChild & childDepth &
       hchildIndex & hchildLookup & _ & hinput & _).
    exists childIndex, inputChild.
    repeat split; try assumption.
    exact (proj1 hchildLookup).
Qed.

(** A full operation trace supplies target and depth values at every source
    row.  Feeding those values to its row predicate and applying the previous
    projection yields a syntax traversal for the source root. *)
Theorem raw_codedFormulaOperation_source_well_formed : forall
    (M : RawPAModel) atom parameter rootDepth input output,
  RawCodedFormulaOperation M atom parameter rootDepth input output ->
  RawCodedWellFormedFormula M input.
Proof.
  intros M atom parameter rootDepth input output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex &
     hsourceDefined & htargetDefined & hdepthDefined & hrootIndex &
     hroot & hrows).
  exists sourceCode, sourceStep, bound, rootIndex.
  unfold RawCodedFormulaSyntaxTraversal.
  repeat split.
  - exact hsourceDefined.
  - exact hrootIndex.
  - exact (proj1 hroot).
  - intros index code hindex hcode.
    destruct (htargetDefined index hindex) as [rowOutput hrowOutput].
    destruct (hdepthDefined index hindex) as [rowDepth hrowDepth].
    apply (raw_codedFormulaOperationTraversalRow_source_syntax M atom
      parameter sourceCode sourceStep targetCode targetStep
      depthCode depthStep index code rowOutput rowDepth).
    apply hrows; [exact hindex |].
    repeat split; assumption.
Qed.

Corollary raw_codedFormulaShift_source_well_formed : forall
    (M : RawPAModel) cutoff amount input output,
  RawCodedFormulaShift M cutoff amount input output ->
  RawCodedWellFormedFormula M input.
Proof.
  intros M cutoff amount input output hshift.
  exact (raw_codedFormulaOperation_source_well_formed M
    (RawCodedFormulaShiftAtom M) amount cutoff input output hshift).
Qed.

(** Every directly translated finite template has a shift trace, including
    templates whose opaque leaves are genuinely nonstandard codes. *)
Corollary rawDirectTemplateFormula_well_formed : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) template,
  RawCodedWellFormedFormula M (rawDirectTemplateFormula inputs template).
Proof.
  intros M hPA inputs template.
  pose proof (rawDirectTemplateFormula_shiftAt M hPA inputs 0 template)
    as hshift.
  exact (raw_codedFormulaShift_source_well_formed M
    (rawNumeralValue M 0) (rawNumeralValue M 1)
    (rawDirectTemplateFormula inputs template)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingAt 0) template))
    hshift).
Qed.

(** ------------------------------------------------------------------
    Exact reduction of the direct closure remainder. *)

(** Universal-closure totality chooses the sealed axiom code.  Diagonal
    propagation handles all (including nonstandard) strict prefixes, so the
    former three-field remainder is reduced to the two genuine syntax folds:
    formula-bound discovery and an all-depth diagonal certificate. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_exists
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement closureCount,
  RawCodedFormulaBound M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs)
    closureCount ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs) ->
  exists axiom : M,
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs replacement axiom closureCount.
Proof.
  intros M hPA inputs replacement closureCount hbound hdiagonal.
  destruct (raw_codedUniversalClosure_exists_all M hPA closureCount
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs)) as [axiom hclosure].
  exists axiom. repeat split.
  - exact hbound.
  - exact hclosure.
  - exact
      (raw_codedUniversalClosureSelfInstantiationThrough_of_diagonal
        M hPA replacement
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
          M inputs)
        closureCount hdiagonal).
Qed.

End PABoundedRawCodedUniversalClosureAllCarrierTotality.
