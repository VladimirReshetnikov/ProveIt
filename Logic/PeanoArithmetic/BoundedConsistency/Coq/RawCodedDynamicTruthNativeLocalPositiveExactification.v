(**
  Exactification of the public native-local positive graph.

  The master package deliberately stores only the public graph witness.  Its
  paired global orbit component therefore no longer mentions the atomic
  adequacy evidence used when the graph was constructed.  That loss is not
  irreversible: the paired orbit, every represented syntax operation in the
  local transform, and hence the complete positive graph are functional in
  every PA model.  We may construct a fresh adequate witness and identify it
  with the public one.

  This module records the required functionality once.  Later callback
  stages can recover the exact adequate trace attached to the current local
  field instead of adding another adequate-orbit hypothesis to their public
  interfaces.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthPairedGlobalOrbitFunctionality
  RawCodedDynamicTruthNativeLocalPositiveGraph.

Module PABoundedRawCodedDynamicTruthNativeLocalPositiveExactification.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.

(** The local ternary application is three sequential represented formula
    substitutions.  Extracting this small deterministic core avoids
    repeating the same three functionality arguments in every transform
    comparison. *)
Lemma raw_dynamicTruthLocalTernaryApplication_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall input firstOutput secondOutput,
  RawDynamicTruthLocalTernaryApplication M input firstOutput ->
  RawDynamicTruthLocalTernaryApplication M input secondOutput ->
  firstOutput = secondOutput.
Proof.
  intros M hPA input firstOutput secondOutput
    (firstMiddle1 & firstMiddle2 & hfirst1 & hfirst2 & hfirst3)
    (secondMiddle1 & secondMiddle2 & hsecond1 & hsecond2 & hsecond3).
  assert (hmiddle1 : firstMiddle1 = secondMiddle1).
  {
    exact (raw_codedFormulaSingleSubstitution_functional M hPA
      (rawNumeralValue M
        (termCode dynamicTruthLocalApplicationFirstReplacement))
      input firstMiddle1 secondMiddle1 hfirst1 hsecond1).
  }
  subst secondMiddle1.
  assert (hmiddle2 : firstMiddle2 = secondMiddle2).
  {
    exact (raw_codedFormulaSingleSubstitution_functional M hPA
      (rawNumeralValue M
        (termCode dynamicTruthLocalApplicationSecondReplacement))
      firstMiddle1 firstMiddle2 secondMiddle2 hfirst2 hsecond2).
  }
  subst secondMiddle2.
  exact (raw_codedFormulaSingleSubstitution_functional M hPA
    (rawNumeralValue M
      (termCode dynamicTruthLocalApplicationThirdReplacement))
    firstMiddle2 firstOutput secondOutput hfirst3 hsecond3).
Qed.

(** Every hidden component of the native local transform is functional.
    Notice that no adequacy premise is needed for uniqueness; adequacy is
    needed only to construct a fresh transform. *)
Theorem raw_dynamicTruthNativeLocalFieldTransformAt_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      inputGlobalSigma inputGlobalPi predecessorLevel
      firstField secondField,
  RawDynamicTruthNativeLocalFieldTransformAt M
    inputGlobalSigma inputGlobalPi predecessorLevel firstField ->
  RawDynamicTruthNativeLocalFieldTransformAt M
    inputGlobalSigma inputGlobalPi predecessorLevel secondField ->
  firstField = secondField.
Proof.
  intros M hPA inputGlobalSigma inputGlobalPi predecessorLevel
    firstField secondField
    (firstLevel & firstGlobalSigma & firstGlobalPi & firstNumeral &
      firstSigmaDomain & firstPiDomain & firstSigmaEvidence &
      firstPiEvidence & hfirstLevel & hfirstSuccessor & hfirstNumeral &
      hfirstSigmaDomain & hfirstPiDomain & hfirstSigmaEvidence &
      hfirstPiEvidence & hfirstField)
    (secondLevel & secondGlobalSigma & secondGlobalPi & secondNumeral &
      secondSigmaDomain & secondPiDomain & secondSigmaEvidence &
      secondPiEvidence & hsecondLevel & hsecondSuccessor & hsecondNumeral &
      hsecondSigmaDomain & hsecondPiDomain & hsecondSigmaEvidence &
      hsecondPiEvidence & hsecondField).
  rewrite hfirstLevel in hfirstSuccessor, hfirstNumeral.
  rewrite hsecondLevel in hsecondSuccessor, hsecondNumeral.
  destruct
    (raw_dynamicTruthPairedGlobalSuccessorAt_functional M hPA
      inputGlobalSigma inputGlobalPi (raw_succ M predecessorLevel)
      firstGlobalSigma firstGlobalPi secondGlobalSigma secondGlobalPi
      hfirstSuccessor hsecondSuccessor) as [hglobalSigma hglobalPi].
  subst secondGlobalSigma. subst secondGlobalPi.
  assert (hnumeral : firstNumeral = secondNumeral).
  {
    exact (raw_numeralTermCodeAt_functional M hPA
      (raw_succ M predecessorLevel) firstNumeral secondNumeral
      hfirstNumeral hsecondNumeral).
  }
  subst secondNumeral.
  assert (hsigmaDomain : firstSigmaDomain = secondSigmaDomain).
  {
    exact (raw_codedFormulaSingleSubstitution_functional M hPA
      firstNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      firstSigmaDomain secondSigmaDomain
      hfirstSigmaDomain hsecondSigmaDomain).
  }
  subst secondSigmaDomain.
  assert (hpiDomain : firstPiDomain = secondPiDomain).
  {
    exact (raw_codedFormulaSingleSubstitution_functional M hPA
      firstNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      firstPiDomain secondPiDomain hfirstPiDomain hsecondPiDomain).
  }
  subst secondPiDomain.
  assert (hsigmaEvidence : firstSigmaEvidence = secondSigmaEvidence).
  {
    exact (raw_dynamicTruthLocalTernaryApplication_functional M hPA
      firstGlobalSigma firstSigmaEvidence secondSigmaEvidence
      hfirstSigmaEvidence hsecondSigmaEvidence).
  }
  subst secondSigmaEvidence.
  assert (hpiEvidence : firstPiEvidence = secondPiEvidence).
  {
    exact (raw_dynamicTruthLocalTernaryApplication_functional M hPA
      firstGlobalPi firstPiEvidence secondPiEvidence
      hfirstPiEvidence hsecondPiEvidence).
  }
  subst secondPiEvidence.
  rewrite hfirstField, hsecondField.
  reflexivity.
Qed.

(** Functionality lifts through the orbit/transform composition. *)
Theorem raw_dynamicTruthNativeLocalPositiveAt_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel firstField secondField,
  RawDynamicTruthNativeLocalPositiveAt M tail predecessorLevel firstField ->
  RawDynamicTruthNativeLocalPositiveAt M tail predecessorLevel secondField ->
  firstField = secondField.
Proof.
  intros M hPA tail predecessorLevel firstField secondField
    (firstGlobalSigma & firstGlobalPi & hfirstOrbit & hfirstTransform)
    (secondGlobalSigma & secondGlobalPi & hsecondOrbit & hsecondTransform).
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_functional M hPA
      tail (raw_succ M predecessorLevel)
      firstGlobalSigma firstGlobalPi secondGlobalSigma secondGlobalPi
      hfirstOrbit hsecondOrbit) as [hglobalSigma hglobalPi].
  subst secondGlobalSigma. subst secondGlobalPi.
  exact (raw_dynamicTruthNativeLocalFieldTransformAt_functional M hPA
    firstGlobalSigma firstGlobalPi predecessorLevel firstField secondField
    hfirstTransform hsecondTransform).
Qed.

(** Recover the exact adequate orbit and transform that produced an arbitrary
    public positive-graph output.  The newly constructed output is identified
    with the supplied one by functionality, so the result remains indexed by
    the literal current field code. *)
Theorem raw_dynamicTruthNativeLocalPositiveAt_exact : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel fieldCode,
  RawDynamicTruthNativeLocalPositiveAt M tail predecessorLevel fieldCode ->
  exists inputGlobalSigma inputGlobalPi : M,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      inputGlobalSigma inputGlobalPi /\
    RawDynamicTruthNativeLocalFieldTransformAt M
      inputGlobalSigma inputGlobalPi predecessorLevel fieldCode.
Proof.
  intros M hPA tail predecessorLevel fieldCode hpublic.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (inputGlobalSigma & inputGlobalPi & horbitSat & hsigmaAdequate &
      hpiAdequate).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M predecessorLevel)
        inputGlobalSigma inputGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail (raw_succ M predecessorLevel)
        inputGlobalSigma inputGlobalPi)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail (raw_succ M predecessorLevel)
          inputGlobalSigma inputGlobalPi)).
      exact horbitSat.
    - split; assumption.
  }
  destruct
    (dynamicTruthNativeLocalFieldTransformGraph_raw_total_on_adequate
      M hPA tail inputGlobalSigma inputGlobalPi predecessorLevel
      hsigmaAdequate hpiAdequate) as [freshField hfreshSat].
  assert (hfreshTransform :
      RawDynamicTruthNativeLocalFieldTransformAt M
        inputGlobalSigma inputGlobalPi predecessorLevel freshField).
  {
    apply (proj1
      (raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff M tail
        inputGlobalSigma inputGlobalPi predecessorLevel freshField)).
    exact hfreshSat.
  }
  assert (hfreshPositive :
      RawDynamicTruthNativeLocalPositiveAt M tail predecessorLevel
        freshField).
  {
    exists inputGlobalSigma, inputGlobalPi.
    split.
    - exact (proj1 hadequateOrbit).
    - exact hfreshTransform.
  }
  assert (hfield : fieldCode = freshField).
  {
    exact (raw_dynamicTruthNativeLocalPositiveAt_functional M hPA
      tail predecessorLevel fieldCode freshField hpublic hfreshPositive).
  }
  subst freshField.
  exists inputGlobalSigma, inputGlobalPi.
  split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthNativeLocalPositiveExactification.
