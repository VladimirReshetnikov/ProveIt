(**
  Synchronize the three carried arithmetic roots for the direct open shell.

  Each fixed PA theorem may select a different finite standard axiom prefix.
  We therefore compile boundedness and adequacy first, grow once more for
  admissibility, and transport the two earlier roots under the unchanged five
  bridge heads.  The result is the exact arithmetic residual expected by the
  open-shell integration, but over one honest final witnessed PA context.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedNumeralTermCode
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration
  RawCodedRestrictedPAOpenShellArithmeticCarriedCompilation.

Import ListNotations.

Module PABoundedRawCodedRestrictedPAOpenShellArithmeticCarriedResidual.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration.
Import
  PABoundedRawCodedRestrictedPAOpenShellArithmeticCarriedCompilation.

(** All three roots inhabit the literal same final bridge-body context. *)
Theorem raw_coqRestrictedPAOpenShell_arithmetic_residual_growing : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    level numeralCode witnessList baseContext,
  RawNumeralTermCodeAt M (raw_succ M level) numeralCode ->
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists boundedPrefix adequatePrefix admissiblePrefix
      admissibleRoot contextBoundedRoot contextAdequateRoot,
    let boundedWitnessList :=
      rawStandardPAAxiomWitnessPrefixWitnessListCode M
        boundedPrefix witnessList in
    let boundedContext :=
      rawStandardPAAxiomWitnessPrefixContextCode M
        boundedPrefix baseContext in
    let adequateWitnessList :=
      rawStandardPAAxiomWitnessPrefixWitnessListCode M
        adequatePrefix boundedWitnessList in
    let adequateContext :=
      rawStandardPAAxiomWitnessPrefixContextCode M
        adequatePrefix boundedContext in
    let finalWitnessList :=
      rawStandardPAAxiomWitnessPrefixWitnessListCode M
        admissiblePrefix adequateWitnessList in
    let finalContext :=
      rawStandardPAAxiomWitnessPrefixContextCode M
        admissiblePrefix adequateContext in
    RawCodedPAAxiomWitnessContext M finalWitnessList finalContext /\
    RawContextListIncluded M baseContext finalContext /\
    RawCoqRestrictedPAOpenShellArithmeticResidual M inputs
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode finalContext)
      admissibleRoot contextBoundedRoot contextAdequateRoot.
Proof.
  intros M hPA inputs level numeralCode witnessList baseContext
    hnumeral hlevel hwitness.
  destruct
    (raw_coqRestrictedPAOpenShell_context_bounds_and_adequacy_growing
      M hPA inputs level numeralCode witnessList baseContext
      hnumeral hlevel hwitness)
    as (boundedPrefix & adequatePrefix & boundedRoot & adequateRoot &
      hboundsAndAdequacy).
  set (boundedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      boundedPrefix witnessList).
  set (boundedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      boundedPrefix baseContext).
  set (adequateWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      adequatePrefix boundedWitnessList).
  set (adequateContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      adequatePrefix boundedContext).
  cbn zeta in hboundsAndAdequacy.
  destruct hboundsAndAdequacy as
    [hadequateWitness [hbaseAdequateIncluded [hbounded hadequate]]].
  destruct (raw_coqRestrictedPAOpenShell_admissible_growing
    M hPA inputs level numeralCode adequateWitnessList adequateContext
    hnumeral hlevel hadequateWitness) as
    (admissiblePrefix & admissibleRoot & hfinalWitness &
      hadequateFinalIncluded & hadmissible).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      admissiblePrefix adequateWitnessList).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      admissiblePrefix adequateContext).
  destruct
    (raw_codedPALocalProof_same_restrictedPABridgeBody_witnessedTail_transport
      M hPA inputs numeralCode adequateWitnessList adequateContext
      finalWitnessList finalContext
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextBoundedTemplate)
      boundedRoot hadequateWitness hfinalWitness
      hadequateFinalIncluded hbounded)
    as [transportedBoundedRoot htransportedBounded].
  destruct
    (raw_codedPALocalProof_same_restrictedPABridgeBody_witnessedTail_transport
      M hPA inputs numeralCode adequateWitnessList adequateContext
      finalWitnessList finalContext
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextAdequateTemplate)
      adequateRoot hadequateWitness hfinalWitness
      hadequateFinalIncluded hadequate)
    as [transportedAdequateRoot htransportedAdequate].
  exists boundedPrefix, adequatePrefix, admissiblePrefix,
    admissibleRoot, transportedBoundedRoot, transportedAdequateRoot.
  cbn zeta.
  split; [exact hfinalWitness |].
  split.
  - intros member hmember.
    exact (hadequateFinalIncluded member
      (hbaseAdequateIncluded member hmember)).
  - exact (conj hadmissible
      (conj htransportedBounded htransportedAdequate)).
Qed.

End PABoundedRawCodedRestrictedPAOpenShellArithmeticCarriedResidual.
