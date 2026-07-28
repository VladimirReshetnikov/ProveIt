(**
  Zero-context local-proof totals for all five native positive fields.

  Ordinary [RawCodedPAProofOf] certificates hide both a witnessed axiom list
  and its synchronized context.  They therefore cannot be unpacked into an
  empty-context local proof.  This file instead consumes the proof-relevant
  leaf interfaces exposed by the five native proof-compilation modules and
  constructs each local root directly.

  The common endpoint is

    exists field root,
      positiveGraph(field, level, tail) /\
      RawCodedPALocalProofOf M [] field root.

  Every graph witness and proof root is selected in the same construction;
  no functionality principle is used to merge contexts or identify two
  independently selected transform outputs.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedContextShift
  RawCodedProofImpIConstructor
  RawCodedProofAllIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionCarrier
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeCrossLevelProofCompilation
  RawCodedDynamicTruthNativeShiftProofCompilation
  RawCodedDynamicTruthNativeSubstitutionProofCompilation
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.

Module PABoundedRawCodedDynamicTruthNativePositiveLocalProofTotals.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionCarrier.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.

(** ------------------------------------------------------------------
    Common interface and its five named specializations. *)

Definition RawDynamicTruthNativePositiveGraphLocalProofTotal
    (M : RawPAModel) (positiveGraph : formula) : Prop :=
  forall (tail : nat -> M) level,
    exists fieldCode root : M,
      raw_formula_sat M
        (scons M fieldCode (scons M level tail)) positiveGraph /\
      RawCodedPALocalProofOf M (raw_zero M) fieldCode root.

Arguments RawDynamicTruthNativePositiveGraphLocalProofTotal
  M positiveGraph : clear implicits.

Definition RawDynamicTruthNativeLocalPositiveLocalProofTotal
    (M : RawPAModel) : Prop :=
  RawDynamicTruthNativePositiveGraphLocalProofTotal M
    dynamicTruthNativeLocalPositiveGraph.

Definition RawDynamicTruthNativeCrossLevelPositiveLocalProofTotal
    (M : RawPAModel) : Prop :=
  RawDynamicTruthNativePositiveGraphLocalProofTotal M
    dynamicTruthNativeCrossLevelPositiveGraph.

Definition RawDynamicTruthNativeShiftPositiveLocalProofTotal
    (M : RawPAModel) : Prop :=
  RawDynamicTruthNativePositiveGraphLocalProofTotal M
    dynamicTruthNativeShiftPositiveGraph.

Definition RawDynamicTruthNativeSubstitutionPositiveLocalProofTotal
    (M : RawPAModel) : Prop :=
  RawDynamicTruthNativePositiveGraphLocalProofTotal M
    dynamicTruthNativeSubstitutionPositiveGraph.

Definition RawDynamicTruthNativeAxiomSoundnessPositiveLocalProofTotal
    (M : RawPAModel) : Prop :=
  RawDynamicTruthNativePositiveGraphLocalProofTotal M
    dynamicTruthNativeAxiomSoundnessPositiveGraph.

Arguments RawDynamicTruthNativeLocalPositiveLocalProofTotal M
  : clear implicits.
Arguments RawDynamicTruthNativeCrossLevelPositiveLocalProofTotal M
  : clear implicits.
Arguments RawDynamicTruthNativeShiftPositiveLocalProofTotal M
  : clear implicits.
Arguments RawDynamicTruthNativeSubstitutionPositiveLocalProofTotal M
  : clear implicits.
Arguments RawDynamicTruthNativeAxiomSoundnessPositiveLocalProofTotal M
  : clear implicits.

Definition RawDynamicTruthNativePositiveLocalProofTotals
    (M : RawPAModel) : Prop :=
  RawDynamicTruthNativeLocalPositiveLocalProofTotal M /\
  RawDynamicTruthNativeCrossLevelPositiveLocalProofTotal M /\
  RawDynamicTruthNativeShiftPositiveLocalProofTotal M /\
  RawDynamicTruthNativeSubstitutionPositiveLocalProofTotal M /\
  RawDynamicTruthNativeAxiomSoundnessPositiveLocalProofTotal M.

Arguments RawDynamicTruthNativePositiveLocalProofTotals M : clear implicits.

(** Turn the orbit graph's adequate totality fields into the exact packaged
    orbit predicate expected by every local-root trace. *)
Lemma raw_dynamicTruthNativePositive_adequateOrbit_of_graph : forall
    (M : RawPAModel) (tail : nat -> M) level globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi (scons M level tail)))
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph ->
  RawCodedFormulaAtomicallyAdequate M globalSigma ->
  RawCodedFormulaAtomicallyAdequate M globalPi ->
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail level globalSigma globalPi.
Proof.
  intros M tail level globalSigma globalPi horbit hsigma hpi.
  apply (proj2
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigma globalPi)).
  split.
  - apply (proj1
      (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
        tail level globalSigma globalPi)).
    exact horbit.
  - split; assumption.
Qed.

(** ------------------------------------------------------------------
    Local helpers closing the exact exposed bodies. *)

Theorem
    raw_codedPALocalProofOf_dynamicTruthNativeCrossLevelField_of_body_root :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  RawDynamicTruthNativeCrossLevelBodyLocalRootAt M
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi ->
  exists root : M,
    RawCodedPALocalProofOf M (raw_zero M)
      (rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi)
      root.
Proof.
  intros M hPA sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    [child hbody].
  set (body := rawDynamicTruthNativeCrossLevelCoherenceBodyCode M
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi).
  exists (rawDynamicTruthNativeLocalClose3Root M body child).
  rewrite rawDynamicTruthNativeCrossLevelCoherenceFieldCode_as_all3.
  exact (raw_codedPALocalProofOf_dynamicTruthNativeLocal_close3
    M hPA body child hbody).
Qed.

Theorem raw_codedPALocalProofOf_dynamicTruthNativeShiftField_of_body_root :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeShiftBodyLocalRootAt M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi ->
  exists root : M,
    RawCodedPALocalProofOf M (raw_zero M)
      (rawDynamicTruthNativeShiftFieldCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      root.
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    hbody.
  set (body := rawDynamicTruthNativeShiftBodyCode M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  change (exists child : M,
    RawCodedPALocalProofOf M (raw_zero M) body child) in hbody.
  destruct hbody as [child [hcoverage hendpoint]].
  exists (rawDynamicTruthNativeShiftCloseNRoot M 8 body child).
  rewrite rawDynamicTruthNativeShiftFieldCode_as_all8.
  split.
  - exact (raw_dynamicTruthNativeShiftCloseNRoot_ruleCoverage M hPA
      8 body child hcoverage hendpoint).
  - rewrite <- rawDynamicTruthNativeShiftCloseNCode_eight.
    exact (raw_dynamicTruthNativeShiftCloseNRoot_endpoint M hPA
      8 body child hcoverage hendpoint).
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthNativeSubstitutionField_of_body_root :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawDynamicTruthNativeSubstitutionBodyLocalRootAt M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi ->
  exists root : M,
    RawCodedPALocalProofOf M (raw_zero M)
      (rawDynamicTruthNativeSubstitutionFieldCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      root.
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    hbody.
  set (body := rawDynamicTruthNativeSubstitutionBodyCode M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  change (exists child : M,
    RawCodedPALocalProofOf M (raw_zero M) body child) in hbody.
  destruct hbody as [child hchild].
  exists (rawDynamicTruthNativeSubstitutionCloseRoot M 7 body child).
  rewrite rawDynamicTruthNativeSubstitutionFieldCode_as_all7_body.
  exact
    (raw_codedPALocalProofOf_dynamicTruthNativeSubstitutionClose
      M hPA 7 body child hchild).
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthNativeAxiomSoundnessField_of_local_root :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain nextSigmaEvidence,
  RawDynamicTruthNativeAxiomSoundnessLocalRootAt M
    sigmaDomain piDomain nextSigmaEvidence ->
  exists root : M,
    RawCodedPALocalProofOf M (raw_zero M)
      (rawDynamicTruthNativeAxiomSoundnessFieldCode M
        sigmaDomain piDomain nextSigmaEvidence)
      root.
Proof.
  intros M hPA sigmaDomain piDomain nextSigmaEvidence [child hchild].
  set (antecedent :=
    rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain).
  pose proof (raw_codedPALocalProofOf_impI M hPA (raw_zero M)
    antecedent nextSigmaEvidence child hchild) as himp.
  destruct himp as [hcoverage hendpoint].
  exists (rawProofAllIRoot M (raw_zero M)
    (rawFormulaImpCode M antecedent nextSigmaEvidence)
    (rawProofImpIRoot M (raw_zero M)
      antecedent nextSigmaEvidence child)).
  rewrite rawDynamicTruthNativeAxiomSoundnessFieldCode_as_all_imp.
  split.
  - exact (raw_proofAllI_ruleCoverage M hPA
      (raw_zero M) (raw_zero M)
      (rawFormulaImpCode M antecedent nextSigmaEvidence)
      (rawProofImpIRoot M (raw_zero M)
        antecedent nextSigmaEvidence child)
      (raw_contextShift_empty M hPA) hcoverage hendpoint).
  - exact (raw_proofAllI_endpoint M (raw_zero M)
      (rawFormulaImpCode M antecedent nextSigmaEvidence)
      (rawProofImpIRoot M (raw_zero M)
        antecedent nextSigmaEvidence child)).
Qed.

(** ------------------------------------------------------------------
    Five graph-local proof totals. *)

Theorem dynamicTruthNativeLocalPositiveGraph_raw_local_proof_total_of_leaves :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalLeafRootCompiler M ->
  RawDynamicTruthNativeLocalPositiveLocalProofTotal M.
Proof.
  intros M hPA hlocal tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (inputGlobalSigma & inputGlobalPi & horbit & hinputSigma & hinputPi).
  pose proof (raw_dynamicTruthNativePositive_adequateOrbit_of_graph M
    tail (raw_succ M predecessorLevel) inputGlobalSigma inputGlobalPi
    horbit hinputSigma hinputPi) as hadequateOrbit.
  destruct (dynamicTruthNativeLocalFieldTransformGraph_raw_total_on_adequate
    M hPA tail inputGlobalSigma inputGlobalPi predecessorLevel
    hinputSigma hinputPi) as [fieldCode htransformSat].
  pose proof (proj1
    (raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff M tail
      inputGlobalSigma inputGlobalPi predecessorLevel fieldCode)
    htransformSat) as htransform.
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_of_transform
    M tail predecessorLevel inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform) as
    (sigmaDomain & piDomain & sigmaEvidence & piEvidence & hfield & htrace).
  destruct (raw_dynamicTruthNativeLocalFieldLocalRootAt_of_leaf_roots
    M hPA sigmaDomain piDomain sigmaEvidence piEvidence
    (hlocal tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence htrace)) as [root hroot].
  exists fieldCode, root. split.
  - apply (proj2 (raw_sat_dynamicTruthNativeLocalPositiveGraph_iff
      M tail predecessorLevel fieldCode)).
    exists inputGlobalSigma, inputGlobalPi. split.
    + apply (proj1
        (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
          tail (raw_succ M predecessorLevel)
          inputGlobalSigma inputGlobalPi)).
      exact hadequateOrbit.
    + exact htransform.
  - rewrite hfield. exact hroot.
Qed.

Theorem
    dynamicTruthNativeCrossLevelPositiveGraph_raw_local_proof_total_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLocalRootCompiler M ->
  RawDynamicTruthNativeCrossLevelPositiveLocalProofTotal M.
Proof.
  intros M hPA hlocal tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
      hcurrentSigma & hcurrentPi).
  pose proof (raw_dynamicTruthNativePositive_adequateOrbit_of_graph M
    tail (raw_succ M predecessorLevel) currentGlobalSigma currentGlobalPi
    horbit hcurrentSigma hcurrentPi) as hadequateOrbit.
  destruct
    (dynamicTruthNativeCrossLevelFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigma hcurrentPi) as [fieldCode htransformSat].
  pose proof (proj1
    (raw_sat_dynamicTruthNativeCrossLevelFieldTransformGraph_iff M tail
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformSat) as htransform.
  destruct (raw_dynamicTruthNativeCrossLevelProofTraceAt_of_transform
    M tail predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    hadequateOrbit htransform) as
    (sigmaDomain & piDomain & currentSigma & currentPi & nextSigma & nextPi &
      hfield & htrace).
  destruct (hlocal tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi htrace) as
    [hsigma hpi].
  pose proof
    (raw_dynamicTruthNativeCrossLevelBodyLocalRootAt_of_polarity_roots
      M hPA sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hsigma hpi) as hbody.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthNativeCrossLevelField_of_body_root
      M hPA sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hbody) as [root hroot].
  exists fieldCode, root. split.
  - apply (proj2 (raw_sat_dynamicTruthNativeCrossLevelPositiveGraph_iff
      M tail predecessorLevel fieldCode)).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
          tail (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact hadequateOrbit.
    + exact htransform.
  - rewrite hfield. exact hroot.
Qed.

Theorem
    dynamicTruthNativeShiftPositiveGraph_raw_local_proof_total_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLocalRootCompiler M ->
  RawDynamicTruthNativeShiftPositiveLocalProofTotal M.
Proof.
  intros M hPA hlocal tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
      hcurrentSigma & hcurrentPi).
  pose proof (raw_dynamicTruthNativePositive_adequateOrbit_of_graph M
    tail (raw_succ M predecessorLevel) currentGlobalSigma currentGlobalPi
    horbit hcurrentSigma hcurrentPi) as hadequateOrbit.
  destruct (dynamicTruthNativeShiftFieldTransformGraph_raw_total_on_adequate
    M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
    hcurrentSigma hcurrentPi) as
    (fieldCode & htransformSat & _hfieldAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthNativeShiftFieldTransformGraph_iff M tail
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformSat) as htransform.
  destruct (raw_dynamicTruthNativeShiftProofTraceAt_of_transform
    M tail predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    hadequateOrbit htransform) as
    (sigmaDomain & piDomain & sourceSigma & targetSigma & sourcePi &
      targetPi & hfield & htrace).
  destruct (hlocal tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi htrace) as
    [hsigma hpi].
  pose proof (raw_dynamicTruthNativeShiftBodyLocalRootAt_of_same_context_roots
    M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    hsigma hpi) as hbody.
  destruct (raw_codedPALocalProofOf_dynamicTruthNativeShiftField_of_body_root
    M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    hbody) as [root hroot].
  exists fieldCode, root. split.
  - apply (proj2 (raw_sat_dynamicTruthNativeShiftPositiveGraph_iff
      M tail predecessorLevel fieldCode)).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
          tail (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact hadequateOrbit.
    + exact htransform.
  - rewrite hfield. exact hroot.
Qed.

Theorem
    dynamicTruthNativeSubstitutionPositiveGraph_raw_local_proof_total_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLocalRootCompiler M ->
  RawDynamicTruthNativeSubstitutionPositiveLocalProofTotal M.
Proof.
  intros M hPA hlocal tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
      hcurrentSigma & hcurrentPi).
  pose proof (raw_dynamicTruthNativePositive_adequateOrbit_of_graph M
    tail (raw_succ M predecessorLevel) currentGlobalSigma currentGlobalPi
    horbit hcurrentSigma hcurrentPi) as hadequateOrbit.
  destruct
    (dynamicTruthNativeSubstitutionFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigma hcurrentPi) as
    (fieldCode & htransformSat & _hfieldAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthNativeSubstitutionFieldTransformGraph_iff M tail
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformSat) as htransform.
  destruct (raw_dynamicTruthNativeSubstitutionProofTraceAt_of_transform
    M tail predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    hadequateOrbit htransform) as
    (sigmaDomain & piDomain & sourceSigma & targetSigma & sourcePi &
      targetPi & hfield & htrace).
  destruct (hlocal tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi htrace) as
    [hsigma hpi].
  pose proof
    (raw_dynamicTruthNativeSubstitutionBodyLocalRootAt_of_polarity_roots
      M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      hsigma hpi) as hbody.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthNativeSubstitutionField_of_body_root
      M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      hbody) as [root hroot].
  exists fieldCode, root. split.
  - apply (proj2 (raw_sat_dynamicTruthNativeSubstitutionPositiveGraph_iff
      M tail predecessorLevel fieldCode)).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
          tail (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact hadequateOrbit.
    + exact htransform.
  - rewrite hfield. exact hroot.
Qed.

Theorem
    dynamicTruthNativeAxiomSoundnessPositiveGraph_raw_local_proof_total_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessPositiveLocalProofTotal M.
Proof.
  intros M hPA hlocal tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
      hcurrentSigma & hcurrentPi).
  pose proof (raw_dynamicTruthNativePositive_adequateOrbit_of_graph M
    tail (raw_succ M predecessorLevel) currentGlobalSigma currentGlobalPi
    horbit hcurrentSigma hcurrentPi) as hadequateOrbit.
  destruct
    (dynamicTruthNativeAxiomSoundnessFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigma hcurrentPi) as
    (fieldCode & htransformSat & _hfieldAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthNativeAxiomSoundnessFieldTransformGraph_iff M tail
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformSat) as htransform.
  destruct (raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_of_transform
    M tail predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    hadequateOrbit htransform) as
    (sigmaDomain & piDomain & nextSigmaEvidence & hfield & htrace).
  pose proof (hlocal tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence htrace) as hleaf.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthNativeAxiomSoundnessField_of_local_root
      M hPA sigmaDomain piDomain nextSigmaEvidence hleaf) as [root hroot].
  exists fieldCode, root. split.
  - apply (proj2
      (raw_sat_dynamicTruthNativeAxiomSoundnessPositiveGraph_iff
        M tail predecessorLevel fieldCode)).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
          tail (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact hadequateOrbit.
    + exact htransform.
  - rewrite hfield. exact hroot.
Qed.

(** One package consumed by the native master assembler. *)
Theorem dynamicTruthNativePositiveLocalProofTotals_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalLeafRootCompiler M ->
  RawDynamicTruthNativeCrossLevelLocalRootCompiler M ->
  RawDynamicTruthNativeShiftLocalRootCompiler M ->
  RawDynamicTruthNativeSubstitutionLocalRootCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M ->
  RawDynamicTruthNativePositiveLocalProofTotals M.
Proof.
  intros M hPA hlocal hcross hshift hsubstitution haxiom.
  repeat split.
  - exact (dynamicTruthNativeLocalPositiveGraph_raw_local_proof_total_of_leaves
      M hPA hlocal).
  - exact
      (dynamicTruthNativeCrossLevelPositiveGraph_raw_local_proof_total_of_local_roots
        M hPA hcross).
  - exact
      (dynamicTruthNativeShiftPositiveGraph_raw_local_proof_total_of_local_roots
        M hPA hshift).
  - exact
      (dynamicTruthNativeSubstitutionPositiveGraph_raw_local_proof_total_of_local_roots
        M hPA hsubstitution).
  - exact
      (dynamicTruthNativeAxiomSoundnessPositiveGraph_raw_local_proof_total_of_local_roots
        M hPA haxiom).
Qed.

End PABoundedRawCodedDynamicTruthNativePositiveLocalProofTotals.
