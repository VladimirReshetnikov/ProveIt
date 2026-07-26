(**
  Concrete local proof-field graph for the restricted Pi existential row.

  Under [fieldCode :: level :: tail], the graph hides the genuine paired
  global Sigma/Pi orbit witness and applies the Pi restricted-existential
  transform to that same pair.  In particular, the lower opaque predicate
  is the global Sigma code selected beside the global Pi code; it cannot be
  supplied independently by a caller.

  This remains a deliberately restricted field.  It certifies the projection
  after explicitly selecting the Pi row's final existential alternative and
  does not assert that the alternative follows from the complete six-way
  disjunction.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedPAProvability
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthPiExistentialLeafProofCompilation
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthLocalProofFieldGraph
  RawCodedDynamicTruthPiExistentialLeafTransformGraph.

Module PABoundedRawCodedDynamicTruthRestrictedExistentialLocalProofFieldGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPiExistentialLeafProofCompilation.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthLocalProofFieldGraph.
Import PABoundedRawCodedDynamicTruthPiExistentialLeafTransformGraph.

Definition dynamicTruthPiRestrictedExistentialLocalProofFieldGraph
    : formula :=
  dynamicTruthLocalProofFieldGraph
    dynamicTruthPiRestrictedExistentialFieldTransformGraph.

(** Law-free carrier semantics of the public composition. *)
Definition RawDynamicTruthPiRestrictedExistentialLocalProofFieldAt
    (M : RawPAModel) (tail : nat -> M) (level fieldCode : M) : Prop :=
  exists globalSigmaCode globalPiCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M tail level
      globalSigmaCode globalPiCode /\
    RawDynamicTruthPiRestrictedExistentialFieldTransformAt M
      globalSigmaCode globalPiCode level fieldCode.

Arguments RawDynamicTruthPiRestrictedExistentialLocalProofFieldAt
  M tail level fieldCode : clear implicits.

Theorem
    raw_sat_dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_iff :
  forall (M : RawPAModel) tail level fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M level tail))
    dynamicTruthPiRestrictedExistentialLocalProofFieldGraph <->
  RawDynamicTruthPiRestrictedExistentialLocalProofFieldAt M
    tail level fieldCode.
Proof.
  intros M tail level fieldCode.
  unfold dynamicTruthPiRestrictedExistentialLocalProofFieldGraph.
  rewrite raw_sat_dynamicTruthLocalProofFieldGraph_iff.
  unfold RawDynamicTruthLocalProofFieldGraphAt,
    RawDynamicTruthPiRestrictedExistentialLocalProofFieldAt.
  split.
  - intros (globalSigmaCode & globalPiCode & horbit & htransform).
    exists globalSigmaCode, globalPiCode. split.
    + apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail level globalSigmaCode globalPiCode)).
      exact horbit.
    + apply (proj1
        (raw_sat_dynamicTruthPiRestrictedExistentialFieldTransformGraph_iff
          M tail globalSigmaCode globalPiCode level fieldCode)).
      exact htransform.
  - intros (globalSigmaCode & globalPiCode & horbit & htransform).
    exists globalSigmaCode, globalPiCode. split.
    + apply (proj2
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail level globalSigmaCode globalPiCode)).
      exact horbit.
    + apply (proj2
        (raw_sat_dynamicTruthPiRestrictedExistentialFieldTransformGraph_iff
          M tail globalSigmaCode globalPiCode level fieldCode)).
      exact htransform.
Qed.

(** ------------------------------------------------------------------
    Direct compiler data only along actual adequate orbit witnesses. *)

Definition RawDynamicTruthPiRestrictedExistentialOrbitDirectCompilerTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level globalSigmaCode globalPiCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail level globalSigmaCode globalPiCode ->
    forall upperNumeral domain lowerApplication,
      RawNumeralTermCodeAt M (raw_succ M level) upperNumeral ->
      RawCodedFormulaSingleSubstitution M upperNumeral
        (rawNumeralValue M
          (formulaCode dynamicTruthPiRowDomainTemplate)) domain ->
      RawDynamicTruthPiCoqLowerApplication M
        globalSigmaCode lowerApplication ->
      exists inputs : RawCodedTemplateDirectStructuralInputs M,
        RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
          domain lowerApplication.

Arguments RawDynamicTruthPiRestrictedExistentialOrbitDirectCompilerTotal M
  : clear implicits.

(** This is the exact operation premise generated by deep closure of the
    Sigma coordinate selected by the paired orbit. *)
Definition RawDynamicTruthPiRestrictedExistentialOrbitTernaryInterchangeTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level globalSigmaCode globalPiCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail level globalSigmaCode globalPiCode ->
    RawCodedTernaryApplicationShiftInterchange M globalSigmaCode /\
    RawCodedTernaryApplicationOpeningInterchange M globalSigmaCode.

Arguments
  RawDynamicTruthPiRestrictedExistentialOrbitTernaryInterchangeTotal M
  : clear implicits.

(** Select the unique ternary application on the adequate Sigma predicate,
    turn the two relational squares into honest-syntax selector laws, and
    invoke the Pi direct-identification constructor. *)
Theorem
    rawDynamicTruthPiRestrictedExistentialOrbitDirectCompilerTotal_of_interchange
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiRestrictedExistentialOrbitTernaryInterchangeTotal M ->
  RawDynamicTruthPiRestrictedExistentialOrbitDirectCompilerTotal M.
Proof.
  intros M hPA hinterchange tail level globalSigmaCode globalPiCode
    horbit upperNumeral domain lowerApplication
    hupperNumeral hdomain hlowerApplication.
  pose proof (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigmaCode globalPiCode) horbit) as horbitView.
  destruct horbitView as [_horbit [hsigmaAdequate _hpiAdequate]].
  destruct (raw_codedTernaryApplicationSelector_exists M hPA
    globalSigmaCode hsigmaAdequate) as [selector _].
  destruct (hinterchange tail level globalSigmaCode globalPiCode horbit)
    as [hshift hopening].
  assert (commutingOnSyntax :
    RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
      globalSigmaCode selector).
  {
    constructor.
    - exact (rawTernaryApplicationSelector_shift_commuting_on_syntax
        M hPA globalSigmaCode selector hshift).
    - exact (rawTernaryApplicationSelector_opening_commuting_on_syntax
        M hPA globalSigmaCode selector hopening).
  }
  exact (raw_coqDynamicTruthPiDirectTemplateIdentification_exists
    M hPA level (raw_succ M level) globalSigmaCode upperNumeral
    domain lowerApplication selector commutingOnSyntax
    hupperNumeral hdomain hlowerApplication).
Qed.

(** ------------------------------------------------------------------
    Proof-producing arbitrary-model totality. *)

Theorem
    dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_adequate_proof_total
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiRestrictedExistentialOrbitDirectCompilerTotal M ->
  forall (tail : nat -> M) level,
    exists fieldCode certificate globalSigmaCode globalPiCode : M,
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail level globalSigmaCode globalPiCode /\
      RawDynamicTruthPiRestrictedExistentialFieldTransformAt M
        globalSigmaCode globalPiCode level fieldCode /\
      RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA hcompiler tail level.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail level) as
    (globalSigmaCode & globalPiCode & horbit & hsigmaAdequate &
     hpiAdequate).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail level globalSigmaCode globalPiCode).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail level globalSigmaCode globalPiCode)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail level globalSigmaCode globalPiCode)).
      exact horbit.
    - split; assumption.
  }
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (raw_dynamicTruthPiDomain_exists_adequate M hPA
    level upperNumeral hupperNumeral)
    as (domain & hdomainWitness & _hdomainAdequate).
  destruct (raw_dynamicTruthPiLower_exists_adequate M hPA
    globalSigmaCode hsigmaAdequate)
    as (lowerApplication & hlowerApplication & _hlowerAdequate).
  destruct (hcompiler tail level globalSigmaCode globalPiCode
    hadequateOrbit upperNumeral domain lowerApplication
    hupperNumeral hdomainWitness hlowerApplication)
    as [inputs identification].
  exists
    (rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
      domain lowerApplication),
    (rawCoqDynamicTruthPiRestrictedExistentialFieldCertificate
      M hPA inputs),
    globalSigmaCode, globalPiCode.
  split.
  - exact hadequateOrbit.
  - split.
    + exists upperNumeral, domain, lowerApplication.
      repeat split; assumption.
    + rewrite
        (rawDynamicTruthPiRestrictedExistentialFieldGraphCode_eq_compiled
          M hPA domain lowerApplication).
      exact
        (raw_codedPAProofOf_coqDynamicTruthPiRestrictedExistentialField_identified
          M hPA inputs domain lowerApplication identification).
Qed.

Definition RawDynamicTruthPiRestrictedExistentialLocalProofFieldTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level,
    exists fieldCode certificate : M,
      raw_formula_sat M
        (scons M fieldCode (scons M level tail))
        dynamicTruthPiRestrictedExistentialLocalProofFieldGraph /\
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthPiRestrictedExistentialLocalProofFieldTotal M
  : clear implicits.

Theorem
    dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_proof_total
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiRestrictedExistentialOrbitDirectCompilerTotal M ->
  RawDynamicTruthPiRestrictedExistentialLocalProofFieldTotal M.
Proof.
  intros M hPA hcompiler tail level.
  destruct
    (dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_adequate_proof_total
      M hPA hcompiler tail level) as
    (fieldCode & certificate & globalSigmaCode & globalPiCode &
     hadequateOrbit & htransform & hcertificate).
  exists fieldCode, certificate. split; [|exact hcertificate].
  apply (proj2
    (raw_sat_dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_iff
      M tail level fieldCode)).
  exists globalSigmaCode, globalPiCode. split; [|exact htransform].
  apply (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigmaCode globalPiCode)).
  exact hadequateOrbit.
Qed.

Corollary
    dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_proof_total_of_orbit_interchange
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiRestrictedExistentialOrbitTernaryInterchangeTotal M ->
  RawDynamicTruthPiRestrictedExistentialLocalProofFieldTotal M.
Proof.
  intros M hPA hinterchange.
  apply
    dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_proof_total;
    [exact hPA |].
  exact
    (rawDynamicTruthPiRestrictedExistentialOrbitDirectCompilerTotal_of_interchange
      M hPA hinterchange).
Qed.

End PABoundedRawCodedDynamicTruthRestrictedExistentialLocalProofFieldGraph.
