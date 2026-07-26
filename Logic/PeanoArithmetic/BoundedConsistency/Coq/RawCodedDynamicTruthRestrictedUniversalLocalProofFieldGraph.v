(**
  Concrete local proof-field graph for the restricted Sigma universal row.

  The public graph is read under

      fieldCode :: level :: tail.

  It hides a *paired* global Sigma/Pi code selected by the genuine dynamic
  truth orbit, then applies the output-first restricted-universal transform
  to that same pair.  Consequently the Pi code used by the opaque lower-row
  application cannot drift away from the Sigma code selected at the same
  hierarchy level.

  This module deliberately exports a restricted field only.  Its certified
  formula forgets the domain conjunct after explicitly entering the
  universal branch; it is not the full seven-way local decision or
  exclusivity bundle.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthUniversalLeafProofCompilation
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthLocalProofFieldGraph
  RawCodedDynamicTruthUniversalLeafTransformGraph.

Module PABoundedRawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthLocalProofFieldGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafTransformGraph.

(** The promised concrete instantiation of the generic local proof field. *)
Definition dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph
    : formula :=
  dynamicTruthLocalProofFieldGraph
    dynamicTruthSigmaRestrictedUniversalFieldTransformGraph.

(** Law-free carrier semantics.  Adequacy is intentionally absent here:
    exact satisfaction of the orbit graph only asserts its represented
    recursion relation. *)
Definition RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldAt
    (M : RawPAModel) (tail : nat -> M) (level fieldCode : M) : Prop :=
  exists globalSigmaCode globalPiCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M tail level
      globalSigmaCode globalPiCode /\
    RawDynamicTruthSigmaRestrictedUniversalFieldTransformAt M
      globalSigmaCode globalPiCode level fieldCode.

Arguments RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldAt
  M tail level fieldCode : clear implicits.

Theorem
    raw_sat_dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_iff :
  forall (M : RawPAModel) tail level fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M level tail))
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph <->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldAt M
    tail level fieldCode.
Proof.
  intros M tail level fieldCode.
  unfold dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph.
  rewrite raw_sat_dynamicTruthLocalProofFieldGraph_iff.
  unfold RawDynamicTruthLocalProofFieldGraphAt,
    RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldAt.
  split.
  - intros (globalSigmaCode & globalPiCode & horbit & htransform).
    exists globalSigmaCode, globalPiCode. split.
    + apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail level globalSigmaCode globalPiCode)).
      exact horbit.
    + apply (proj1
        (raw_sat_dynamicTruthSigmaRestrictedUniversalFieldTransformGraph_iff
          M tail globalSigmaCode globalPiCode level fieldCode)).
      exact htransform.
  - intros (globalSigmaCode & globalPiCode & horbit & htransform).
    exists globalSigmaCode, globalPiCode. split.
    + apply (proj2
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail level globalSigmaCode globalPiCode)).
      exact horbit.
    + apply (proj2
        (raw_sat_dynamicTruthSigmaRestrictedUniversalFieldTransformGraph_iff
          M tail globalSigmaCode globalPiCode level fieldCode)).
      exact htransform.
Qed.

(** ------------------------------------------------------------------
    Proof-producing arbitrary-model totality.

    The generic transform interface asks for a compiler at every pair of
    carrier elements.  The concrete paired orbit gives more information:
    its selected Pi code is atomically adequate.  The following premise is
    therefore the weakest direct-compiler interface actually consumed by
    this composite.  It asks for direct structural inputs only on those
    adequate Pi codes which can arise from the paired orbit.

    In particular, the two code-identification equalities below remain
    separate from all opaque formula shift/open traces stored in [inputs].
    No equality of codes is used to manufacture such a trace. *)
Definition
    RawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal
    (M : RawPAModel) : Prop :=
  forall globalPiCode level upperNumeral domain lowerApplication,
    RawCodedFormulaAtomicallyAdequate M globalPiCode ->
    RawNumeralTermCodeAt M (raw_succ M level) upperNumeral ->
    RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode) domain ->
    RawDynamicTruthCoqLowerApplication M
      globalPiCode lowerApplication ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
      RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
        domain lowerApplication.

Arguments
  RawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal M
  : clear implicits.

(** The genuinely weakest compiler interface is indexed by an actual paired
    orbit witness.  Later root-closure induction establishes operation laws
    for those selected codes, not for every atomically adequate formula code
    in the carrier. *)
Definition
    RawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level globalSigmaCode globalPiCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail level globalSigmaCode globalPiCode ->
    forall upperNumeral domain lowerApplication,
      RawNumeralTermCodeAt M (raw_succ M level) upperNumeral ->
      RawCodedFormulaSingleSubstitution M upperNumeral
        (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode) domain ->
      RawDynamicTruthCoqLowerApplication M
        globalPiCode lowerApplication ->
      exists inputs : RawCodedTemplateDirectStructuralInputs M,
        RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
          domain lowerApplication.

Arguments
  RawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal M
  : clear implicits.

Lemma
    rawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal_implies_orbit
  : forall (M : RawPAModel),
  RawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal M.
Proof.
  intros M hcompiler tail level globalSigmaCode globalPiCode horbit
    upperNumeral domain lowerApplication hupper hdomain hlower.
  pose proof (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigmaCode globalPiCode) horbit) as horbitView.
  destruct horbitView as [_horbit [_hsigmaAdequate hpiAdequate]].
  exact (hcompiler globalPiCode level upperNumeral domain lowerApplication
    hpiAdequate hupper hdomain hlower).
Qed.

(** The older, source-independent compiler interface is sufficient, but
    strictly stronger: it does not get to assume adequacy of [globalPiCode]. *)
Lemma
    rawDynamicTruthSigmaRestrictedUniversalDirectCompilerTotal_implies_adequate
  : forall (M : RawPAModel),
  RawDynamicTruthSigmaRestrictedUniversalDirectCompilerTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal M.
Proof.
  intros M hcompiler globalPiCode level upperNumeral domain
    lowerApplication _hadequate hupper hdomain hlower.
  exact (hcompiler globalPiCode level upperNumeral domain
    lowerApplication hupper hdomain hlower).
Qed.

(** Honest-domain selector availability is the remaining opaque-atom seam
    needed to build the direct compiler data.  The selector's trace field is
    already guarded by represented term syntax, and the two commuting laws
    have that same guard.  No off-domain behavior is required. *)
Definition
    RawDynamicTruthSigmaRestrictedUniversalAdequateTernarySelectorTotal
    (M : RawPAModel) : Prop :=
  forall globalPiCode,
    RawCodedFormulaAtomicallyAdequate M globalPiCode ->
    exists selector : RawCodedTernaryApplicationSelector M globalPiCode,
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
        globalPiCode selector.

Arguments
  RawDynamicTruthSigmaRestrictedUniversalAdequateTernarySelectorTotal M
  : clear implicits.

(** Relational interchange is an even smaller input than a selected
    function: adequacy already proves that a ternary application output
    exists, and cross-trace functionality makes every such output unique.
    Thus the two interchange relations below canonically yield the guarded
    selector laws used by the direct translator. *)
Definition
    RawDynamicTruthSigmaRestrictedUniversalAdequateTernaryInterchangeTotal
    (M : RawPAModel) : Prop :=
  forall globalPiCode,
    RawCodedFormulaAtomicallyAdequate M globalPiCode ->
    RawCodedTernaryApplicationShiftInterchange M globalPiCode /\
    RawCodedTernaryApplicationOpeningInterchange M globalPiCode.

Arguments
  RawDynamicTruthSigmaRestrictedUniversalAdequateTernaryInterchangeTotal M
  : clear implicits.

(** Orbit-refined interchange is the exact premise produced by a
    root-closure invariant.  It deliberately says nothing about adequate
    formula codes which do not occur in the chosen dynamic truth orbit. *)
Definition
    RawDynamicTruthSigmaRestrictedUniversalOrbitTernaryInterchangeTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level globalSigmaCode globalPiCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail level globalSigmaCode globalPiCode ->
    RawCodedTernaryApplicationShiftInterchange M globalPiCode /\
    RawCodedTernaryApplicationOpeningInterchange M globalPiCode.

Arguments
  RawDynamicTruthSigmaRestrictedUniversalOrbitTernaryInterchangeTotal M
  : clear implicits.

Theorem
    rawDynamicTruthSigmaRestrictedUniversalAdequateTernarySelectorTotal_of_interchange
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalAdequateTernaryInterchangeTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalAdequateTernarySelectorTotal M.
Proof.
  intros M hPA hinterchange globalPiCode hpiAdequate.
  destruct (raw_codedTernaryApplicationSelector_exists M hPA
    globalPiCode hpiAdequate) as [selector _].
  destruct (hinterchange globalPiCode hpiAdequate)
    as [hshift hopening].
  exists selector. constructor.
  - exact
      (rawTernaryApplicationSelector_shift_commuting_on_syntax
        M hPA globalPiCode selector hshift).
  - exact
      (rawTernaryApplicationSelector_opening_commuting_on_syntax
        M hPA globalPiCode selector hopening).
Qed.

(** Construct the exact direct compiler identification from graph-selected
    witnesses.  The domain equality is obtained by comparing two genuine
    represented single-substitution traces.  The lower-application equality
    similarly follows from functionality of the graph's three-step native
    application trace.  Neither equality is used in the reverse direction
    to invent an operation trace. *)
Theorem rawDynamicTruthSigmaRestrictedUniversalDirectCompiler_of_selector :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    globalPiCode level upperNumeral domain lowerApplication
    (selector : RawCodedTernaryApplicationSelector M globalPiCode),
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
    globalPiCode selector ->
  RawNumeralTermCodeAt M (raw_succ M level) upperNumeral ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode) domain ->
  RawDynamicTruthCoqLowerApplication M globalPiCode lowerApplication ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
      domain lowerApplication.
Proof.
  intros M hPA globalPiCode level upperNumeral domain lowerApplication
    selector commutingOnSyntax hupperNumeral hdomain hlowerApplication.
  destruct (raw_numeralTermCodeExists_all M hPA level)
    as [lowerNumeral hlowerNumeral].
  pose (parameters :=
    rawCoqDynamicTruthTemplateNumeralParameters M
      level (raw_succ M level) lowerNumeral upperNumeral
      hlowerNumeral hupperNumeral).
  pose (package :=
    rawCoqDynamicTruthTemplateNumeralTermPackage M hPA
      level (raw_succ M level)
      (rawCoqDynamicTruthTemplateOpaqueCode selector)
      parameters eq_refl eq_refl).
  pose (inputs :=
    rawCoqDynamicTruthTemplateDirectStructuralInputs M hPA
      level (raw_succ M level) globalPiCode selector
      commutingOnSyntax package).
  exists inputs. constructor.
  - change (rawDirectTemplateFormula inputs
      coqDynamicTruthSigmaDomainLeafTemplate = domain).
    apply
      (rawCoqDynamicTruthSigmaDomainLeaf_identifies_native_domain
        M hPA level (raw_succ M level) globalPiCode selector
        commutingOnSyntax package domain).
    change (RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
      domain).
    exact hdomain.
  - change (rawDirectTemplateFormula inputs
      coqDynamicTruthLowerPiAtomTemplate = lowerApplication).
    exact
      (rawCoqDynamicTruthLowerPiAtom_identifies_native_application
        M hPA level (raw_succ M level) globalPiCode selector
        commutingOnSyntax package lowerApplication hlowerApplication).
Qed.

Theorem
    rawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal_of_ternary_selector
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalAdequateTernarySelectorTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal M.
Proof.
  intros M hPA hselector globalPiCode level upperNumeral domain
    lowerApplication hpiAdequate hupperNumeral hdomain
    hlowerApplication.
  destruct (hselector globalPiCode hpiAdequate)
    as [selector commutingOnSyntax].
  exact
    (rawDynamicTruthSigmaRestrictedUniversalDirectCompiler_of_selector
      M hPA globalPiCode level upperNumeral domain lowerApplication
      selector commutingOnSyntax hupperNumeral hdomain hlowerApplication).
Qed.

Corollary
    rawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal_of_interchange
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalAdequateTernaryInterchangeTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal M.
Proof.
  intros M hPA hinterchange.
  apply
    rawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal_of_ternary_selector;
    [exact hPA |].
  exact
    (rawDynamicTruthSigmaRestrictedUniversalAdequateTernarySelectorTotal_of_interchange
      M hPA hinterchange).
Qed.

(** Construct compiler data only for the Pi predicate carried by the supplied
    orbit witness.  This is the bridge consumed by the strongest field
    endpoint below. *)
Theorem
    rawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal_of_interchange
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalOrbitTernaryInterchangeTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal M.
Proof.
  intros M hPA hinterchange tail level globalSigmaCode globalPiCode
    horbit upperNumeral domain lowerApplication
    hupperNumeral hdomain hlowerApplication.
  pose proof (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigmaCode globalPiCode) horbit) as horbitView.
  destruct horbitView as [_horbit [_hsigmaAdequate hpiAdequate]].
  destruct (raw_codedTernaryApplicationSelector_exists M hPA
    globalPiCode hpiAdequate) as [selector _].
  destruct (hinterchange tail level globalSigmaCode globalPiCode horbit)
    as [hshift hopening].
  assert (commutingOnSyntax :
    RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
      globalPiCode selector).
  {
    constructor.
    - exact (rawTernaryApplicationSelector_shift_commuting_on_syntax
        M hPA globalPiCode selector hshift).
    - exact (rawTernaryApplicationSelector_opening_commuting_on_syntax
        M hPA globalPiCode selector hopening).
  }
  exact
    (rawDynamicTruthSigmaRestrictedUniversalDirectCompiler_of_selector
      M hPA globalPiCode level upperNumeral domain lowerApplication
      selector commutingOnSyntax hupperNumeral hdomain hlowerApplication).
Qed.

(** A strengthened witness form retains the adequate paired orbit and the
    exact transform relation.  Besides being useful to later composites,
    this statement documents why adequacy may soundly guard the direct
    compiler premise above. *)
Theorem
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_adequate_proof_total
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal M ->
  forall (tail : nat -> M) level,
    exists fieldCode certificate globalSigmaCode globalPiCode : M,
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail level globalSigmaCode globalPiCode /\
      RawDynamicTruthSigmaRestrictedUniversalFieldTransformAt M
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
  destruct (raw_dynamicTruthSigmaDomain_exists_adequate M hPA
    level upperNumeral hupperNumeral)
    as (domain & hdomainWitness & _hdomainAdequate).
  destruct (raw_dynamicTruthSigmaLower_exists_adequate M hPA
    globalPiCode hpiAdequate)
    as (lowerApplication & hlowerApplication & _hlowerAdequate).
  destruct (hcompiler tail level globalSigmaCode globalPiCode
    hadequateOrbit upperNumeral domain lowerApplication
    hupperNumeral hdomainWitness
    hlowerApplication) as [inputs identification].
  exists
    (rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
      domain lowerApplication),
    (rawCoqDynamicTruthSigmaRestrictedUniversalFieldCertificate
      M hPA inputs),
    globalSigmaCode, globalPiCode.
  split.
  - exact hadequateOrbit.
  - split.
    + exists upperNumeral, domain, lowerApplication.
      repeat split; assumption.
    + rewrite
        (rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode_eq_compiled
          M hPA domain lowerApplication).
      exact
        (raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedUniversalField_identified
          M hPA inputs domain lowerApplication identification).
Qed.

(** Public graph totality with the exact ordinary PA proof target. *)
Definition RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level,
    exists fieldCode certificate : M,
      raw_formula_sat M
        (scons M fieldCode (scons M level tail))
        dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph /\
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M
  : clear implicits.

Theorem
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M.
Proof.
  intros M hPA hcompiler tail level.
  destruct
    (dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_adequate_proof_total
      M hPA hcompiler tail level) as
    (fieldCode & certificate & globalSigmaCode & globalPiCode &
     hadequateOrbit & htransform & hcertificate).
  exists fieldCode, certificate. split; [|exact hcertificate].
  apply (proj2
    (raw_sat_dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_iff
      M tail level fieldCode)).
  exists globalSigmaCode, globalPiCode. split; [|exact htransform].
  apply (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigmaCode globalPiCode)).
  exact hadequateOrbit.
Qed.

(** Strongest current endpoint: interchange is required only for the Pi codes
    accompanied by an actual adequate paired-orbit witness. *)
Corollary
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total_of_orbit_interchange
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalOrbitTernaryInterchangeTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M.
Proof.
  intros M hPA hinterchange.
  apply
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total;
    [exact hPA |].
  exact
    (rawDynamicTruthSigmaRestrictedUniversalOrbitDirectCompilerTotal_of_interchange
      M hPA hinterchange).
Qed.

(** Compatibility endpoint for the stronger premise covering every adequate
    formula code, including codes which never occur in the orbit. *)
Corollary
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total_of_interchange
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalAdequateTernaryInterchangeTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M.
Proof.
  intros M hPA hinterchange.
  apply
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total;
    [exact hPA |].
  apply
    rawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal_implies_orbit.
  exact
    (rawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal_of_interchange
      M hPA hinterchange).
Qed.

(** Compatibility corollary for callers already implementing the stronger
    source-independent transform premise. *)
Corollary
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total_of_direct_compiler
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalDirectCompilerTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M.
Proof.
  intros M hPA hcompiler.
  apply
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total;
    [exact hPA |].
  apply
    rawDynamicTruthSigmaRestrictedUniversalAdequateDirectCompilerTotal_implies_orbit.
  exact
    (rawDynamicTruthSigmaRestrictedUniversalDirectCompilerTotal_implies_adequate
      M hcompiler).
Qed.

End PABoundedRawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph.
