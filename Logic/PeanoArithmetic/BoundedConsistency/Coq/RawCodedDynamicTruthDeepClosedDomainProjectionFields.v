(**
  Full-row domain projections selected from the deep-closed paired orbit.

  The public Sigma and Pi projection graphs expose an orbit-wide compiler
  interface: every adequate paired-orbit witness must carry the structural
  shift/opening data used by direct template translation.  Deep-closure
  induction supplies something slightly different and strictly sufficient:
  at each level it selects one adequate paired witness with those laws.

  This module consumes that selected witness directly.  It therefore avoids
  a functionality or uniqueness theorem for the ordinary orbit, and it does
  not strengthen deep closure into an assertion about every adequate witness.
  The resulting fields prove the two genuine full-row domain eliminators

      Sigma Or7 row -> Ex^8 Sigma-domain
      Pi    Or6 row -> Ex^8 Pi-domain.

  They remain domain projections, not the complete positive local
  decision/exclusivity coordinate.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedFixedLevelTruthTotality
  RawCodedNumeralTermCode
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthGlobalSuccessorDeepClosure
  RawCodedDynamicTruthPairedSuccessorLocalDeepClosure
  RawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph
  RawCodedDynamicTruthDeepClosedRestrictedLocalProofFields
  RawCodedDynamicTruthSigmaDomainProjectionProofCompilation
  RawCodedDynamicTruthPiDomainProjectionProofCompilation
  RawCodedDynamicTruthSigmaDomainProjectionTransformGraph
  RawCodedDynamicTruthPiDomainProjectionTransformGraph.

Module PABoundedRawCodedDynamicTruthDeepClosedDomainProjectionFields.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
Import PABoundedRawCodedDynamicTruthPairedSuccessorLocalDeepClosure.
Import PABoundedRawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph.
Import PABoundedRawCodedDynamicTruthDeepClosedRestrictedLocalProofFields.
Import
  PABoundedRawCodedDynamicTruthSigmaDomainProjectionProofCompilation.
Import PABoundedRawCodedDynamicTruthPiDomainProjectionProofCompilation.
Import PABoundedRawCodedDynamicTruthSigmaDomainProjectionTransformGraph.
Import PABoundedRawCodedDynamicTruthPiDomainProjectionTransformGraph.

(** Compile the Sigma projection at the particular deeply closed orbit
    witness selected for this level. *)
Theorem
    dynamicTruthSigmaDomainProjectionPositiveFieldGraph_raw_proof_total_of_deep_closed_orbit
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawCodedTernaryPredicateDeepClosedOpeningInterchangeTotal M ->
  RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA hlocalClosure hopening tail level.
  destruct
    (dynamicTruthPairedGlobalDeepClosedOrbit_interchange_exists
      M hPA hlocalClosure hopening tail level) as
    (globalSigmaCode & globalPiCode & hadequateOrbit &
     hglobalSigmaShift & hglobalSigmaOpening &
     hglobalPiShift & hglobalPiOpening).
  pose proof (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigmaCode globalPiCode) hadequateOrbit) as
    horbitView.
  destruct horbitView as
    [horbit [hglobalSigmaAdequate hglobalPiAdequate]].
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (raw_dynamicTruthSigmaDomain_exists_adequate M hPA
    level upperNumeral hupperNumeral) as
    (domain & hdomain & _hdomainAdequate).
  destruct (raw_dynamicTruthSigmaLower_exists_adequate M hPA
    globalPiCode hglobalPiAdequate) as
    (lowerApplication & hlowerApplication & _hlowerAdequate).
  destruct (raw_codedTernaryApplicationSelector_exists M hPA
    globalPiCode hglobalPiAdequate) as [selector _hselector].
  assert (commutingOnSyntax :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
        globalPiCode selector).
  {
    constructor.
    - exact (rawTernaryApplicationSelector_shift_commuting_on_syntax
        M hPA globalPiCode selector hglobalPiShift).
    - exact (rawTernaryApplicationSelector_opening_commuting_on_syntax
        M hPA globalPiCode selector hglobalPiOpening).
  }
  destruct
    (rawDynamicTruthSigmaRestrictedUniversalDirectCompiler_of_selector
      M hPA globalPiCode level upperNumeral domain lowerApplication
      selector commutingOnSyntax hupperNumeral hdomain
      hlowerApplication) as [inputs identification].
  exists
    (rawDynamicTruthSigmaDomainProjectionFieldCode M
      domain lowerApplication),
    (rawCoqDynamicTruthSigmaDomainProjectionFieldCertificate
      M hPA inputs).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthSigmaDomainProjectionPositiveFieldGraph_iff
        M tail level
        (rawDynamicTruthSigmaDomainProjectionFieldCode M
          domain lowerApplication))).
    exists globalSigmaCode, globalPiCode. split; [exact horbit |].
    exists upperNumeral, domain, lowerApplication.
    repeat split; try assumption; reflexivity.
  - exact
      (raw_codedPAProofOf_dynamicTruthSigmaDomainProjectionField_identified
        M hPA inputs domain lowerApplication identification).
Qed.

(** Polarity-dual compilation at the selected deeply closed Sigma code. *)
Theorem
    dynamicTruthPiDomainProjectionPositiveFieldGraph_raw_proof_total_of_deep_closed_orbit
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawCodedTernaryPredicateDeepClosedOpeningInterchangeTotal M ->
  RawDynamicTruthPiDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA hlocalClosure hopening tail level.
  destruct
    (dynamicTruthPairedGlobalDeepClosedOrbit_interchange_exists
      M hPA hlocalClosure hopening tail level) as
    (globalSigmaCode & globalPiCode & hadequateOrbit &
     hglobalSigmaShift & hglobalSigmaOpening &
     hglobalPiShift & hglobalPiOpening).
  pose proof (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigmaCode globalPiCode) hadequateOrbit) as
    horbitView.
  destruct horbitView as
    [horbit [hglobalSigmaAdequate hglobalPiAdequate]].
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (raw_dynamicTruthPiDomain_exists_adequate M hPA
    level upperNumeral hupperNumeral) as
    (domain & hdomain & _hdomainAdequate).
  destruct (raw_dynamicTruthPiLower_exists_adequate M hPA
    globalSigmaCode hglobalSigmaAdequate) as
    (lowerApplication & hlowerApplication & _hlowerAdequate).
  destruct (raw_codedTernaryApplicationSelector_exists M hPA
    globalSigmaCode hglobalSigmaAdequate) as [selector _hselector].
  assert (commutingOnSyntax :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
        globalSigmaCode selector).
  {
    constructor.
    - exact (rawTernaryApplicationSelector_shift_commuting_on_syntax
        M hPA globalSigmaCode selector hglobalSigmaShift).
    - exact (rawTernaryApplicationSelector_opening_commuting_on_syntax
        M hPA globalSigmaCode selector hglobalSigmaOpening).
  }
  destruct
    (raw_coqDynamicTruthPiDirectTemplateIdentification_exists
      M hPA level (raw_succ M level) globalSigmaCode upperNumeral
      domain lowerApplication selector commutingOnSyntax
      hupperNumeral hdomain hlowerApplication) as
    [inputs identification].
  exists
    (rawDynamicTruthPiDomainProjectionFieldCode M
      domain lowerApplication),
    (rawCoqDynamicTruthPiDomainProjectionFieldCertificate
      M hPA inputs).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthPiDomainProjectionPositiveFieldGraph_iff
        M tail level
        (rawDynamicTruthPiDomainProjectionFieldCode M
          domain lowerApplication))).
    exists globalSigmaCode, globalPiCode. split; [exact horbit |].
    exists upperNumeral, domain, lowerApplication.
    repeat split; try assumption; reflexivity.
  - exact
      (raw_codedPAProofOf_dynamicTruthPiDomainProjectionField_identified
        M hPA inputs domain lowerApplication identification).
Qed.

(** The two full-row domain projections share the same deep-closure and
    opening-algebra premises, though each selects its own certificate. *)
Corollary
    dynamicTruthDeepClosedDomainProjectionFields_raw_proof_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawCodedTernaryPredicateDeepClosedOpeningInterchangeTotal M ->
  RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal M /\
  RawDynamicTruthPiDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA hlocalClosure hopening. split.
  - exact
      (dynamicTruthSigmaDomainProjectionPositiveFieldGraph_raw_proof_total_of_deep_closed_orbit
        M hPA hlocalClosure hopening).
  - exact
      (dynamicTruthPiDomainProjectionPositiveFieldGraph_raw_proof_total_of_deep_closed_orbit
        M hPA hlocalClosure hopening).
Qed.

(** Concrete substitution algebra removes the opening premise. *)
Corollary
    dynamicTruthDeepClosedDomainProjectionFields_raw_proof_total_of_local_closure
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal M /\
  RawDynamicTruthPiDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA hlocalClosure.
  exact
    (dynamicTruthDeepClosedDomainProjectionFields_raw_proof_total
      M hPA hlocalClosure
      (raw_codedTernaryPredicateDeepClosedOpeningInterchangeTotal_of_PA
        M hPA)).
Qed.

(** PA itself supplies the paired local-row deep closure. *)
Corollary
    dynamicTruthSigmaDomainProjectionPositiveFieldGraph_raw_proof_total_unconditional
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA.
  exact (proj1
    (dynamicTruthDeepClosedDomainProjectionFields_raw_proof_total_of_local_closure
      M hPA (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA))).
Qed.

Corollary
    dynamicTruthPiDomainProjectionPositiveFieldGraph_raw_proof_total_unconditional
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA.
  exact (proj2
    (dynamicTruthDeepClosedDomainProjectionFields_raw_proof_total_of_local_closure
      M hPA (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA))).
Qed.

Corollary
    dynamicTruthDeepClosedDomainProjectionFields_raw_proof_total_unconditional
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaDomainProjectionPositiveFieldTotal M /\
  RawDynamicTruthPiDomainProjectionPositiveFieldTotal M.
Proof.
  intros M hPA.
  exact
    (dynamicTruthDeepClosedDomainProjectionFields_raw_proof_total_of_local_closure
      M hPA (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA)).
Qed.

End PABoundedRawCodedDynamicTruthDeepClosedDomainProjectionFields.
