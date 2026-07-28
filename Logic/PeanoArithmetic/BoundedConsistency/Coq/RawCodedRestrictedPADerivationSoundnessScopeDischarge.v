(**
  Discharge the metatheoretic scope premise of the fixed-level
  derivation-soundness induction data.

  [RawCodedRestrictedPADerivationSoundnessPredicate] deliberately exposed
  the scope of its recursively expanded source formula as a premise.  The
  compositional scope development now proves that premise for every external
  [level : nat].  The first theorem below is the exact adapter between those
  modules.

  The two compiler corollaries make the remaining mathematical boundary
  explicit.  They still require concrete local PA proofs of the zero and
  successor cases.  Thus this file neither performs represented induction on
  proof codes nor turns the external standard [level] into an arbitrary
  element of a nonstandard PA model.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedNumeralTermCode
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedPAInductionAxiomCertificate
  RawCodedPAClosureInductionCompiler
  RawCodedRestrictedPADerivationSoundnessPredicate
  RawCodedRestrictedPADerivationSoundnessScope.

Module PABoundedRawCodedRestrictedPADerivationSoundnessScopeDischarge.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedPAClosureInductionCompiler.
Import PABoundedRawCodedRestrictedPADerivationSoundnessPredicate.
Import PABoundedRawCodedRestrictedPADerivationSoundnessScope.

(** All represented syntax-operation data for ordinary induction on the
    strong proof-code prefix.  Only the model-internal numeral trace remains
    explicit; the purely metatheoretic scope premise has been discharged. *)
Theorem raw_codedRestrictedPADerivationSoundnessClosureInductionData_scoped :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    level numeralBound numeralCode,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedPAClosureInductionData M numeralCode
    (rawRestrictedPADerivationSoundnessInductionSourceCode M level)
    (rawRestrictedPADerivationSoundnessInductionAxiomCode M level)
    (rawRestrictedPADerivationSoundnessInductionShiftedCode M level)
    (rawRestrictedPADerivationSoundnessInductionSuccessorCode M level)
    (rawRestrictedPADerivationSoundnessInductionZeroCode M level)
    (rawRestrictedPADerivationSoundnessInductionSourceAllCode M level)
    (rawRestrictedPADerivationSoundnessInductionStepImpCode M level)
    (rawRestrictedPADerivationSoundnessInductionStepAllCode M level)
    (rawRestrictedPADerivationSoundnessInductionPremiseCode M level)
    (rawRestrictedPADerivationSoundnessInductionBodyCode M level)
    (rawRestrictedPADerivationSoundnessInductionClosureCount M level).
Proof.
  intros M hPA level numeralBound numeralCode hnumeral.
  exact (raw_codedRestrictedPADerivationSoundnessClosureInductionData
    M hPA level numeralBound numeralCode
    (restrictedPADerivationSoundnessPrefix_scoped level) hnumeral).
Qed.

(** Specialization of the generic compiler inside the context extended by
    the represented induction axiom.  The two local-proof hypotheses are the
    still-open base and successor obligations; this theorem only composes
    them with the now-complete syntax data. *)
Theorem raw_codedPALocalProofOf_restrictedPADerivationSoundness_induction :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    level numeralBound numeralCode baseWitnessList baseContext
      zeroChild stepChild,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext
      (rawRestrictedPADerivationSoundnessInductionAxiomCode M level))
    (rawRestrictedPADerivationSoundnessInductionZeroCode M level)
    zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext
      (rawRestrictedPADerivationSoundnessInductionAxiomCode M level))
    (rawRestrictedPADerivationSoundnessInductionStepAllCode M level)
    stepChild ->
  exists bodyChild : M,
    RawCodedPALocalProofOf M
      (rawPAInductionExtendedContext M baseContext
        (rawRestrictedPADerivationSoundnessInductionAxiomCode M level))
      (rawRestrictedPADerivationSoundnessInductionSourceAllCode M level)
      (rawPAClosureInductionProofRoot M
        baseContext
        (rawRestrictedPADerivationSoundnessInductionAxiomCode M level)
        (rawRestrictedPADerivationSoundnessInductionPremiseCode M level)
        (rawRestrictedPADerivationSoundnessInductionSourceAllCode M level)
        (rawRestrictedPADerivationSoundnessInductionZeroCode M level)
        (rawRestrictedPADerivationSoundnessInductionStepAllCode M level)
        bodyChild zeroChild stepChild).
Proof.
  intros M hPA level numeralBound numeralCode
    baseWitnessList baseContext zeroChild stepChild
    hnumeral hbase hzero hstep.
  exact (raw_codedPALocalProofOf_closure_induction M hPA
    baseWitnessList baseContext numeralCode
    (rawRestrictedPADerivationSoundnessInductionSourceCode M level)
    (rawRestrictedPADerivationSoundnessInductionAxiomCode M level)
    (rawRestrictedPADerivationSoundnessInductionShiftedCode M level)
    (rawRestrictedPADerivationSoundnessInductionSuccessorCode M level)
    (rawRestrictedPADerivationSoundnessInductionZeroCode M level)
    (rawRestrictedPADerivationSoundnessInductionSourceAllCode M level)
    (rawRestrictedPADerivationSoundnessInductionStepImpCode M level)
    (rawRestrictedPADerivationSoundnessInductionStepAllCode M level)
    (rawRestrictedPADerivationSoundnessInductionPremiseCode M level)
    (rawRestrictedPADerivationSoundnessInductionBodyCode M level)
    (rawRestrictedPADerivationSoundnessInductionClosureCount M level)
    zeroChild stepChild hbase
    (raw_codedRestrictedPADerivationSoundnessClosureInductionData_scoped
      M hPA level numeralBound numeralCode hnumeral)
    hzero hstep).
Qed.

(** Ordinary PA-proof packaging of the same conditional compilation.  The
    certificate root is explicit, and the zero/step proof codes remain inputs
    rather than being manufactured here. *)
Theorem raw_codedPAProofOf_restrictedPADerivationSoundness_induction :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    level numeralBound numeralCode baseWitnessList baseContext
      zeroChild stepChild,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext
      (rawRestrictedPADerivationSoundnessInductionAxiomCode M level))
    (rawRestrictedPADerivationSoundnessInductionZeroCode M level)
    zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext
      (rawRestrictedPADerivationSoundnessInductionAxiomCode M level))
    (rawRestrictedPADerivationSoundnessInductionStepAllCode M level)
    stepChild ->
  exists bodyChild : M,
    RawCodedPAProofOf M
      (rawRestrictedPADerivationSoundnessInductionSourceAllCode M level)
      (rawPAClosureInductionCertificate M
        baseWitnessList baseContext
        (rawRestrictedPADerivationSoundnessInductionSourceCode M level)
        (rawRestrictedPADerivationSoundnessInductionAxiomCode M level)
        (rawRestrictedPADerivationSoundnessInductionPremiseCode M level)
        (rawRestrictedPADerivationSoundnessInductionSourceAllCode M level)
        (rawRestrictedPADerivationSoundnessInductionZeroCode M level)
        (rawRestrictedPADerivationSoundnessInductionStepAllCode M level)
        bodyChild zeroChild stepChild).
Proof.
  intros M hPA level numeralBound numeralCode
    baseWitnessList baseContext zeroChild stepChild
    hnumeral hbase hzero hstep.
  exact (raw_codedPAProofOf_closure_induction M hPA
    baseWitnessList baseContext numeralCode
    (rawRestrictedPADerivationSoundnessInductionSourceCode M level)
    (rawRestrictedPADerivationSoundnessInductionAxiomCode M level)
    (rawRestrictedPADerivationSoundnessInductionShiftedCode M level)
    (rawRestrictedPADerivationSoundnessInductionSuccessorCode M level)
    (rawRestrictedPADerivationSoundnessInductionZeroCode M level)
    (rawRestrictedPADerivationSoundnessInductionSourceAllCode M level)
    (rawRestrictedPADerivationSoundnessInductionStepImpCode M level)
    (rawRestrictedPADerivationSoundnessInductionStepAllCode M level)
    (rawRestrictedPADerivationSoundnessInductionPremiseCode M level)
    (rawRestrictedPADerivationSoundnessInductionBodyCode M level)
    (rawRestrictedPADerivationSoundnessInductionClosureCount M level)
    zeroChild stepChild hbase
    (raw_codedRestrictedPADerivationSoundnessClosureInductionData_scoped
      M hPA level numeralBound numeralCode hnumeral)
    hzero hstep).
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessScopeDischarge.
