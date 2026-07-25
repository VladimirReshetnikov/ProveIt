(**
  Constructor-local root step for context insertion in raw PA proofs.

  Every non-binder rule is rebuilt solely from the below-root induction
  hypothesis and its coverage-certified child endpoints.  Insertion depth is
  unchanged for ordinary premises; it increases under Imp-I, under both
  Or-E branch assumptions, and under the Ex-E body assumption.

  All-I and Ex-E additionally cross a de Bruijn binder.  Their only open
  inputs are stated below as two narrow interfaces: an atomically adequate
  formula has a unit shift, and context insertion commutes with a chosen
  unit shift and [RawContextShift].  No proof-transplant premise is assumed
  for either binder rule.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedContextInsert RawCodedContextShift
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofEndpoints
  RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedProofAssumptionLeaf RawCodedProofImpIConstructor
  RawCodedProofBinaryConstructors RawCodedProofUnaryConstructors
  RawCodedProofLeafConstructors RawCodedProofAndIConstructor
  RawCodedProofAndEConstructors RawCodedProofOrIConstructors
  RawCodedProofOrEConstructor RawCodedProofAllIConstructor
  RawCodedProofAllEConstructor RawCodedProofExIConstructor
  RawCodedProofExEConstructor RawCodedProofEqReflConstructor
  RawCodedProofEqElimConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertInduction.

Import ListNotations.

Module PABoundedRawCodedPALocalProofContextInsertRootStep.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedContextInsert.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofUnaryConstructors.
Import PABoundedRawCodedProofLeafConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedProofOrIConstructors.
Import PABoundedRawCodedProofOrEConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedProofExIConstructor.
Import PABoundedRawCodedProofExEConstructor.
Import PABoundedRawCodedProofEqReflConstructor.
Import PABoundedRawCodedProofEqElimConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertInduction.

(** The represented formula-shift graph is partial on arbitrary carrier
    values.  This callback asks for totality only on the atomic-adequacy
    domain already carried by the context-insertion invariant. *)
Definition RawAdequateUnitFormulaShiftExists (M : RawPAModel) : Prop :=
  forall formula : M,
    RawCodedFormulaAtomicallyAdequate M formula ->
    exists shifted : M,
      RawCodedFormulaShift M
        (raw_zero M) (rawNumeralValue M 1) formula shifted.

Arguments RawAdequateUnitFormulaShiftExists M : clear implicits.

(** A commuting square for a *chosen* shifted head.  The source and target
    shifts share the same binder, while insertion retains its carrier-valued
    depth.  Descending under an additional local premise is handled later by
    [raw_contextInsertAt_cons], not hidden in this callback. *)
Definition RawContextInsertUnitShiftSquare (M : RawPAModel) : Prop :=
  forall head shiftedHead depth source target shiftedSource : M,
    RawContextInsertAt M head depth source target ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1) head shiftedHead ->
    RawContextShift M source shiftedSource ->
    exists shiftedTarget : M,
      RawContextShift M target shiftedTarget /\
      RawContextInsertAt M shiftedHead depth shiftedSource shiftedTarget.

Arguments RawContextInsertUnitShiftSquare M : clear implicits.

(** Package the two binder callbacks and derive adequacy of the shifted
    head from the already-proved target-syntax theorem. *)
Lemma raw_contextInsert_unitShift_square : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawAdequateUnitFormulaShiftExists M ->
  RawContextInsertUnitShiftSquare M ->
  forall head depth source target shiftedSource,
  RawCodedFormulaAtomicallyAdequate M head ->
  RawContextInsertAt M head depth source target ->
  RawContextShift M source shiftedSource ->
  exists shiftedHead shiftedTarget : M,
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1) head shiftedHead /\
    RawCodedFormulaAtomicallyAdequate M shiftedHead /\
    RawContextShift M target shiftedTarget /\
    RawContextInsertAt M shiftedHead depth shiftedSource shiftedTarget.
Proof.
  intros M hPA hshiftExists hsquare
    head depth source target shiftedSource
    hhead hinsertion hsourceShift.
  destruct (hshiftExists head hhead) as [shiftedHead hheadShift].
  destruct (hsquare head shiftedHead depth source target shiftedSource
    hinsertion hheadShift hsourceShift)
    as [shiftedTarget [htargetShift hshiftedInsertion]].
  exists shiftedHead, shiftedTarget.
  repeat split; try assumption.
  exact (raw_codedFormulaShift_target_atomically_adequate M hPA
    (raw_zero M) (rawNumeralValue M 1) head shiftedHead hheadShift).
Qed.

(** Reroot coverage at one explicitly named recursive premise and pair it
    with the endpoint supplied by the current local rule row. *)
Lemma raw_codedPALocalProof_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root context a b c t child1 child2 child3 fields children child
      childContext childConclusion,
  RawProofRuleCoverage M root ->
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  In child children ->
  RawProofEndpoint M child childContext childConclusion ->
  RawCodedPALocalProofOf M childContext childConclusion child /\
  rawLt M child root.
Proof.
  intros M hPA root context a b c t child1 child2 child3
    fields children child childContext childConclusion
    hcoverage hconstructor hentry hroot hmember hendpoint.
  destruct (raw_proofRuleCoverage_public_recursive_child M hPA root
    hcoverage context a b c t child1 child2 child3 hconstructor
    fields children hentry hroot child hmember)
    as [hchildCoverage hchildBelow].
  split; [split; assumption | exact hchildBelow].
Qed.

(** Full constructor-local assembler. *)
Theorem raw_codedPALocalProof_contextInsertRootStep_of_binder_callbacks :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawAdequateUnitFormulaShiftExists M ->
  RawContextInsertUnitShiftSquare M ->
  RawCodedPALocalProofContextInsertRootStep M.
Proof.
  intros M hPA hshiftExists hsquare.
  unfold RawCodedPALocalProofContextInsertRootStep,
    RawCodedPALocalProofContextInsertAt.
  intros root hbelow head depth source target conclusion
    hhead hinsertion [hcoverage hendpoint].
  pose proof (raw_proofRuleCoverage_public_root_complete M hPA root
    hcoverage source conclusion hendpoint) as hvalid.
  destruct hvalid as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hrowContext & hcases).
  subst rowContext.
  assert (hconstructor : RawProofConstructorCode M
      root source a b c t child1 child2 child3).
  {
    unfold RawProofRuleValidCases in hcases.
    unfold RawProofConstructorCode. tauto.
  }
  unfold RawProofRuleValidCases in hcases.
  repeat match type of hcases with
  | _ \/ _ => destruct hcases as [hcases | hcases]
  end.

  (** Assumption: insertion preserves every old member. *)
  - destruct hcases as [_ [-> hmember]].
    exists (rawProofAssumptionRoot M target a).
    exact (raw_codedPALocalProof_contextInsert_assumption M hPA
      head depth source target a hinsertion hmember).

  (** Imp-I: the child lies below one additional local assumption, so the
      insertion depth increases before invoking the induction hypothesis. *)
  - destruct hcases as [hroot [-> hchildEndpoint]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 1; source; a; b; child1] [child1] child1
      (rawListNode M a source) b
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    pose proof (raw_contextInsertAt_cons M hPA
      head depth source target a hinsertion) as hchildInsertion.
    destruct (hbelow child1 hchildBelow
      head (raw_succ M depth)
      (rawListNode M a source) (rawListNode M a target) b
      hhead hchildInsertion hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofImpIRoot M target a b newChild). split.
    + exact (raw_proofImpI_ruleCoverage M hPA
        target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofImpI_endpoint M target a b newChild).

  (** Imp-E: both children stay in the parent context and retain [depth]. *)
  - destruct hcases as [hroot [-> [-> [himpEndpoint hargEndpoint]]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b (rawFormulaImpCode M a b) t
      child1 child2 child3
      [rawNumeralValue M 2; source; a; b; child1; child2]
      [child1; child2] child1 source (rawFormulaImpCode M a b)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) himpEndpoint)
      as [himpLocal himpBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b (rawFormulaImpCode M a b) t
      child1 child2 child3
      [rawNumeralValue M 2; source; a; b; child1; child2]
      [child1; child2] child2 source a
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hargEndpoint)
      as [hargLocal hargBelow].
    destruct (hbelow child1 himpBelow head depth source target
      (rawFormulaImpCode M a b) hhead hinsertion himpLocal)
      as [newImp [hnewImpCoverage hnewImpEndpoint]].
    destruct (hbelow child2 hargBelow head depth source target a
      hhead hinsertion hargLocal)
      as [newArg [hnewArgCoverage hnewArgEndpoint]].
    exists (rawProofImpERoot M target a b newImp newArg). split.
    + exact (raw_proofImpE_ruleCoverage M hPA
        target a b newImp newArg
        hnewImpCoverage hnewImpEndpoint
        hnewArgCoverage hnewArgEndpoint).
    + exact (raw_proofImpE_endpoint M target a b newImp newArg).

  (** Bot-E: its only premise remains in the parent context. *)
  - destruct hcases as [hroot [-> [-> hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a (rawFormulaBotCode M) c t child1 child2 child3
      [rawNumeralValue M 3; source; a; child1] [child1] child1
      source (rawFormulaBotCode M)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow head depth source target
      (rawFormulaBotCode M) hhead hinsertion hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofBotERoot M target a newChild). split.
    + exact (raw_proofBotE_ruleCoverage M hPA
        target a newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofBotE_endpoint M target a newChild).

  (** LEM and equality reflexivity are premise-free. *)
  - destruct hcases as [_ [-> [-> ->]]].
    exists (rawProofLemRoot M target a). split.
    + exact (raw_proofLem_ruleCoverage M hPA target a).
    + exact (raw_proofLem_endpoint M target a).

  (** And-I. *)
  - destruct hcases as [hroot [-> [hleftEndpoint hrightEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 5; source; a; b; child1; child2]
      [child1; child2] child1 source a
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hleftEndpoint)
      as [hleftLocal hleftBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 5; source; a; b; child1; child2]
      [child1; child2] child2 source b
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hrightEndpoint)
      as [hrightLocal hrightBelow].
    destruct (hbelow child1 hleftBelow head depth source target a
      hhead hinsertion hleftLocal)
      as [newLeft [hnewLeftCoverage hnewLeftEndpoint]].
    destruct (hbelow child2 hrightBelow head depth source target b
      hhead hinsertion hrightLocal)
      as [newRight [hnewRightCoverage hnewRightEndpoint]].
    exists (rawProofAndIRoot M target a b newLeft newRight). split.
    + exact (raw_proofAndI_ruleCoverage M hPA
        target a b newLeft newRight
        hnewLeftCoverage hnewLeftEndpoint
        hnewRightCoverage hnewRightEndpoint).
    + exact (raw_proofAndI_endpoint M target a b newLeft newRight).

  (** And-E-left. *)
  - destruct hcases as [hroot [-> [-> hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b (rawFormulaAndCode M a b) t
      child1 child2 child3
      [rawNumeralValue M 6; source; a; b; child1] [child1] child1
      source (rawFormulaAndCode M a b)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow head depth source target
      (rawFormulaAndCode M a b) hhead hinsertion hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofAndERoot M RawAndLeft target a b newChild). split.
    + exact (raw_proofAndE_ruleCoverage M hPA
        RawAndLeft target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofAndE_endpoint M
        RawAndLeft target a b newChild).

  (** And-E-right. *)
  - destruct hcases as [hroot [-> [-> hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b (rawFormulaAndCode M a b) t
      child1 child2 child3
      [rawNumeralValue M 7; source; a; b; child1] [child1] child1
      source (rawFormulaAndCode M a b)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow head depth source target
      (rawFormulaAndCode M a b) hhead hinsertion hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofAndERoot M RawAndRight target a b newChild). split.
    + exact (raw_proofAndE_ruleCoverage M hPA
        RawAndRight target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofAndE_endpoint M
        RawAndRight target a b newChild).

  (** Or-I-left. *)
  - destruct hcases as [hroot [-> hchildEndpoint]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 8; source; a; b; child1] [child1] child1
      source a hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow head depth source target a
      hhead hinsertion hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofOrIRoot M RawOrLeft target a b newChild). split.
    + exact (raw_proofOrI_ruleCoverage M hPA
        RawOrLeft target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofOrI_endpoint M RawOrLeft target a b newChild).

  (** Or-I-right. *)
  - destruct hcases as [hroot [-> hchildEndpoint]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 9; source; a; b; child1] [child1] child1
      source b hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow head depth source target b
      hhead hinsertion hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofOrIRoot M RawOrRight target a b newChild). split.
    + exact (raw_proofOrI_ruleCoverage M hPA
        RawOrRight target a b newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofOrI_endpoint M RawOrRight target a b newChild).

  (** Or-E: the disjunction premise retains [depth], while both branch
      premises descend beneath their respective disjunct and use [S depth]. *)
  - destruct hcases as
      [hroot [-> [-> [hdisjunctionEndpoint
        [hleftEndpoint hrightEndpoint]]]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c (rawFormulaOrCode M a b)
      child1 child2 child3
      [rawNumeralValue M 10; source; a; b; c;
        child1; child2; child3]
      [child1; child2; child3] child1 source
      (rawFormulaOrCode M a b)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hdisjunctionEndpoint)
      as [hdisjunctionLocal hdisjunctionBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c (rawFormulaOrCode M a b)
      child1 child2 child3
      [rawNumeralValue M 10; source; a; b; c;
        child1; child2; child3]
      [child1; child2; child3] child2
      (rawListNode M a source) c
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hleftEndpoint)
      as [hleftLocal hleftBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c (rawFormulaOrCode M a b)
      child1 child2 child3
      [rawNumeralValue M 10; source; a; b; c;
        child1; child2; child3]
      [child1; child2; child3] child3
      (rawListNode M b source) c
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hrightEndpoint)
      as [hrightLocal hrightBelow].
    pose proof (raw_contextInsertAt_cons M hPA
      head depth source target a hinsertion) as hleftInsertion.
    pose proof (raw_contextInsertAt_cons M hPA
      head depth source target b hinsertion) as hrightInsertion.
    destruct (hbelow child1 hdisjunctionBelow
      head depth source target (rawFormulaOrCode M a b)
      hhead hinsertion hdisjunctionLocal)
      as [newDisjunction
        [hnewDisjunctionCoverage hnewDisjunctionEndpoint]].
    destruct (hbelow child2 hleftBelow
      head (raw_succ M depth)
      (rawListNode M a source) (rawListNode M a target) c
      hhead hleftInsertion hleftLocal)
      as [newLeft [hnewLeftCoverage hnewLeftEndpoint]].
    destruct (hbelow child3 hrightBelow
      head (raw_succ M depth)
      (rawListNode M b source) (rawListNode M b target) c
      hhead hrightInsertion hrightLocal)
      as [newRight [hnewRightCoverage hnewRightEndpoint]].
    exists (rawProofOrERoot M target a b c
      newDisjunction newLeft newRight). split.
    + exact (raw_proofOrE_ruleCoverage M hPA
        target a b c newDisjunction newLeft newRight
        hnewDisjunctionCoverage hnewDisjunctionEndpoint
        hnewLeftCoverage hnewLeftEndpoint
        hnewRightCoverage hnewRightEndpoint).
    + exact (raw_proofOrE_endpoint M
        target a b c newDisjunction newLeft newRight).

  (** All-I: shift the inserted head, commute insertion with the context
      shift, then recurse at the same insertion depth. *)
  - destruct hcases as [hroot [-> [hsourceShift hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 11; source; a; child1] [child1] child1
      b a hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (raw_contextInsert_unitShift_square M hPA
      hshiftExists hsquare head depth source target b
      hhead hinsertion hsourceShift)
      as (shiftedHead & shiftedTarget & hheadShift & hshiftedHead &
        htargetShift & hshiftedInsertion).
    destruct (hbelow child1 hchildBelow
      shiftedHead depth b shiftedTarget a
      hshiftedHead hshiftedInsertion hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofAllIRoot M target a newChild). split.
    + exact (raw_proofAllI_ruleCoverage M hPA
        target shiftedTarget a newChild
        htargetShift hnewCoverage hnewEndpoint).
    + exact (raw_proofAllI_endpoint M target a newChild).

  (** All-E: substitution data are context-independent. *)
  - destruct hcases as [hroot [hsubstitution [-> hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a (rawFormulaAllCode M a) c t
      child1 child2 child3
      [rawNumeralValue M 12; source; a; t; child1] [child1] child1
      source (rawFormulaAllCode M a)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow head depth source target
      (rawFormulaAllCode M a) hhead hinsertion hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofAllERoot M target a t newChild). split.
    + exact (raw_proofAllE_ruleCoverage M hPA
        target a t newChild hnewCoverage hnewEndpoint).
    + exact (raw_proofAllE_endpoint M
        target a t conclusion newChild hsubstitution).

  (** Ex-I: the represented substitution instance remains unchanged. *)
  - destruct hcases as [hroot [-> [hsubstitution hchildEndpoint]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2 child3
      [rawNumeralValue M 13; source; a; t; child1] [child1] child1
      source b hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hchildEndpoint)
      as [hchildLocal hchildBelow].
    destruct (hbelow child1 hchildBelow head depth source target b
      hhead hinsertion hchildLocal)
      as [newChild [hnewCoverage hnewEndpoint]].
    exists (rawProofExIRoot M target a t newChild). split.
    + exact (raw_proofExI_ruleCoverage M hPA
        target a t b newChild hsubstitution hnewCoverage hnewEndpoint).
    + exact (raw_proofExI_endpoint M target a t newChild).

  (** Ex-E: the existential premise uses the parent insertion.  The body
      first crosses the context shift at the same depth, then crosses its
      local body assumption, increasing the depth exactly once. *)
  - destruct hcases as
      [hroot [-> [-> [hexEndpoint
        [hsourceShift [hconclusionShift hbodyEndpoint]]]]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2
      (rawFormulaExCode M a)
      [rawNumeralValue M 14; source; a; b; child1; child2]
      [child1; child2] child1 source (rawFormulaExCode M a)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hexEndpoint)
      as [hexLocal hexBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c t child1 child2
      (rawFormulaExCode M a)
      [rawNumeralValue M 14; source; a; b; child1; child2]
      [child1; child2] child2 (rawListNode M a c) t
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hbodyEndpoint)
      as [hbodyLocal hbodyBelow].
    destruct (raw_contextInsert_unitShift_square M hPA
      hshiftExists hsquare head depth source target c
      hhead hinsertion hsourceShift)
      as (shiftedHead & shiftedTarget & hheadShift & hshiftedHead &
        htargetShift & hshiftedInsertion).
    pose proof (raw_contextInsertAt_cons M hPA
      shiftedHead depth c shiftedTarget a hshiftedInsertion)
      as hbodyInsertion.
    destruct (hbelow child1 hexBelow head depth source target
      (rawFormulaExCode M a) hhead hinsertion hexLocal)
      as [newEx [hnewExCoverage hnewExEndpoint]].
    destruct (hbelow child2 hbodyBelow
      shiftedHead (raw_succ M depth)
      (rawListNode M a c) (rawListNode M a shiftedTarget) t
      hshiftedHead hbodyInsertion hbodyLocal)
      as [newBody [hnewBodyCoverage hnewBodyEndpoint]].
    exists (rawProofExERoot M target a b newEx newBody). split.
    + exact (raw_proofExE_ruleCoverage M hPA
        target shiftedTarget a b t newEx newBody
        hnewExCoverage hnewExEndpoint
        htargetShift hconclusionShift
        hnewBodyCoverage hnewBodyEndpoint).
    + exact (raw_proofExE_endpoint M target a b newEx newBody).

  - destruct hcases as [_ ->].
    exists (rawProofEqReflRoot M target t). split.
    + exact (raw_proofEqRefl_ruleCoverage M hPA target t).
    + exact (raw_proofEqRefl_endpoint M target t).

  (** Eq-E: both premises retain the parent insertion; source and target
      substitution traces are purely formula data and are reused verbatim. *)
  - destruct hcases as
      [hroot [htargetSubstitution [-> [hequalityEndpoint
        [hsourceSubstitution hbodyEndpoint]]]]].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c (rawFormulaEqCode M a b)
      child1 child2 child3
      [rawNumeralValue M 16; source; a; b; c; child1; child2]
      [child1; child2] child1 source (rawFormulaEqCode M a b)
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hequalityEndpoint)
      as [hequalityLocal hequalityBelow].
    destruct (raw_codedPALocalProof_recursive_child M hPA
      root source a b c (rawFormulaEqCode M a b)
      child1 child2 child3
      [rawNumeralValue M 16; source; a; b; c; child1; child2]
      [child1; child2] child2 source child3
      hcoverage hconstructor
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      hroot (ltac:(cbn; tauto)) hbodyEndpoint)
      as [hbodyLocal hbodyBelow].
    destruct (hbelow child1 hequalityBelow head depth source target
      (rawFormulaEqCode M a b) hhead hinsertion hequalityLocal)
      as [newEquality [hnewEqualityCoverage hnewEqualityEndpoint]].
    destruct (hbelow child2 hbodyBelow head depth source target child3
      hhead hinsertion hbodyLocal)
      as [newBody [hnewBodyCoverage hnewBodyEndpoint]].
    exists (rawProofEqElimRoot M target a b c
      newEquality newBody). split.
    + exact (raw_proofEqElim_ruleCoverage M hPA
        target a b c child3 newEquality newBody
        hnewEqualityCoverage hnewEqualityEndpoint
        hsourceSubstitution hnewBodyCoverage hnewBodyEndpoint).
    + exact (raw_proofEqElim_endpoint M
        target a b c conclusion newEquality newBody
        htargetSubstitution).
Qed.

End PABoundedRawCodedPALocalProofContextInsertRootStep.
