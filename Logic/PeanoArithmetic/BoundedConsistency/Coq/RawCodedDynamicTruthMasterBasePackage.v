(**
  The complete level-zero component package for the six-field master graph.

  The five component coordinates are assembled in the same order as the
  master constructor and its Lean counterpart:

    1. local decision and exclusivity;
    2. adjacent-level coherence;
    3. formula-shift invariance;
    4. single-substitution invariance;
    5. witnessed PA-axiom soundness.

  Each coordinate below is an ordinary closed formula at the first dynamic
  index, together with a standard output-first quotation graph and an exact
  [BProv] derivation.  Consequently the standard branch of
  [RawSixFieldMasterZeroComponentPackage] applies directly.

  This module packages the five *base graphs themselves*.  It does not claim
  that they are already the full carrier-indexed graph families required at
  arbitrary, possibly nonstandard, positive indices.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedDynamicTruthLocalDecisionExclusiveBase
  RawCodedDynamicTruthTransportFieldBaseGraphs
  RawCodedDynamicTruthAxiomSoundnessBaseGraph
  RawCodedTruthCertificateMasterAssembler
  RawCodedTruthCertificateMasterInduction
  RawCodedTruthCertificateMasterBaseBridge.

Module PABoundedRawCodedDynamicTruthMasterBasePackage.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.
Import PABoundedRawCodedDynamicTruthTransportFieldBaseGraphs.
Import PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.
Import PABoundedRawCodedTruthCertificateMasterAssembler.
Import PABoundedRawCodedTruthCertificateMasterInduction.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.

(** A convenient exact [BProv] name for the local field's advertised base
    formula.  The underlying theorem was already uniform in the external
    fixed level; here it is instantiated at zero. *)
Theorem PA_proves_dynamicTruthLocalDecisionExclusiveBaseFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthLocalDecisionExclusiveBaseFormula.
Proof.
  exact (PA_proves_fixedLevelLocalDecisionExclusiveBundleFormula 0).
Qed.

(** The local graph's general representation theorem immediately supplies
    the standard witness required by the master-base bridge. *)
Theorem
    dynamicTruthLocalDecisionExclusiveBaseGraph_standard_zero_witness :
    forall (M : RawPAModel), RawPASatisfies M -> forall tail : nat -> M,
  raw_formula_sat M
    (scons M
      (rawQuotedFormulaCode M
        dynamicTruthLocalDecisionExclusiveBaseFormula)
      (scons M (raw_zero M) tail))
    dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph.
Proof.
  intros M hPA tail.
  apply (proj2
    (dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph_representation
      M hPA tail (raw_zero M)
      (rawQuotedFormulaCode M
        dynamicTruthLocalDecisionExclusiveBaseFormula))).
  reflexivity.
Qed.

(** The exact five-field standard package.  Keeping this stronger named
    theorem visible makes every graph/formula correspondence auditable before
    it is injected into the public sum type. *)
Theorem raw_dynamicTruthMasterBaseBProvComponentPackage : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawSixFieldMasterZeroBProvComponentPackage M
    dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph
    dynamicTruthCrossLevelBaseFieldGraph
    dynamicTruthShiftBaseFieldGraph
    dynamicTruthSubstitutionBaseFieldGraph
    dynamicTruthAxiomSoundnessBaseFieldGraph
    dynamicTruthLocalDecisionExclusiveBaseFormula
    dynamicTruthCrossLevelBaseFieldFormula
    dynamicTruthShiftBaseFieldFormula
    dynamicTruthSubstitutionBaseFieldFormula
    dynamicTruthAxiomSoundnessBaseFieldFormula.
Proof.
  intros M hPA.
  unfold RawSixFieldMasterZeroBProvComponentPackage.
  split.
  - exact
      (dynamicTruthLocalDecisionExclusiveBaseGraph_standard_zero_witness
        M hPA).
  - split.
    + exact (dynamicTruthCrossLevelBaseFieldGraph_standard_zero_witness
        M hPA).
    + split.
      * exact (dynamicTruthShiftBaseFieldGraph_standard_zero_witness
          M hPA).
      * split.
        -- exact
             (dynamicTruthSubstitutionBaseFieldGraph_standard_zero_witness
               M hPA).
        -- split.
           ++ exact
                (dynamicTruthAxiomSoundnessBaseFieldGraph_standard_zero_witness
                  M hPA).
           ++ split.
              ** exact
                   PA_proves_dynamicTruthLocalDecisionExclusiveBaseFormula.
              ** split.
                 --- exact PA_proves_dynamicTruthCrossLevelBaseFieldFormula.
                 --- split.
                     +++ exact PA_proves_dynamicTruthShiftBaseFieldFormula.
                     +++ split.
                         *** exact
                               PA_proves_dynamicTruthSubstitutionBaseFieldFormula.
                         *** exact
                               PA_proves_dynamicTruthAxiomSoundnessBaseFieldFormula.
Qed.

(** Public component package, selecting its standard-[BProv] branch rather
    than manufacturing a second common-context proof construction. *)
Theorem raw_dynamicTruthMasterBaseComponentPackage : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawSixFieldMasterZeroComponentPackage M
    dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph
    dynamicTruthCrossLevelBaseFieldGraph
    dynamicTruthShiftBaseFieldGraph
    dynamicTruthSubstitutionBaseFieldGraph
    dynamicTruthAxiomSoundnessBaseFieldGraph.
Proof.
  intros M hPA. right.
  exists dynamicTruthLocalDecisionExclusiveBaseFormula,
    dynamicTruthCrossLevelBaseFieldFormula,
    dynamicTruthShiftBaseFieldFormula,
    dynamicTruthSubstitutionBaseFieldFormula,
    dynamicTruthAxiomSoundnessBaseFieldFormula.
  exact (raw_dynamicTruthMasterBaseBProvComponentPackage M hPA).
Qed.

(** The concrete six-field graph adds the fixed compact restricted-
    consistency coordinate as its sixth field. *)
Definition dynamicTruthMasterBaseGraph : formula :=
  concreteSixFieldMasterGraph
    dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph
    dynamicTruthCrossLevelBaseFieldGraph
    dynamicTruthShiftBaseFieldGraph
    dynamicTruthSubstitutionBaseFieldGraph
    dynamicTruthAxiomSoundnessBaseFieldGraph.

(** The completed component package discharges exactly the base callback
    consumed by master induction.  The proof certificate constructed by the
    bridge targets the code selected by [dynamicTruthMasterBaseGraph]. *)
Theorem raw_dynamicTruthMasterPackageBase : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawSixFieldMasterPackageBase M dynamicTruthMasterBaseGraph.
Proof.
  intros M hPA.
  unfold dynamicTruthMasterBaseGraph.
  apply (raw_sixFieldMasterPackageBase_of_components M hPA).
  exact (raw_dynamicTruthMasterBaseComponentPackage M hPA).
Qed.

End PABoundedRawCodedDynamicTruthMasterBasePackage.
