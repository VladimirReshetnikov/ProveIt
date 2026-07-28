(**
  Close the direct strong-prefix induction shell using ordinary substitution
  identity.

  Universal-closure opening does not require a single substitution table
  shared by all depths.  The ordinary all-depth identity proved in
  [RawCodedUniversalClosureOrdinarySubstitution] already propagates through
  every, including nonstandard, universal-closure prefix.  Consequently the
  exact direct closure remainder can be assembled from just a formula bound
  and that ordinary identity.

  The second theorem also removes the explicit formula-bound premise.  The
  direct induction body is atomically adequate, and carrier-wide bound
  totality therefore chooses its (possibly nonstandard) bound internally.
  Thus ordinary all-depth identity is the only remaining premise specific to
  closing this remainder.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedUniversalClosureOrdinarySubstitution
  RawCodedUniversalClosureAllCarrierTotality
  RawCodedFormulaRankTotality
  RawCodedPAAxiomWitness
  RawCodedTemplateDirectStructuralTranslation
  RawCodedFormulaBoundAllCarrierBoundary
  RawCodedFormulaBoundAtomicallyAdequateTotality
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrdinaryClosureRemainder.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedUniversalClosureOrdinarySubstitution.
Import PABoundedRawCodedUniversalClosureAllCarrierTotality.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedFormulaBoundAllCarrierBoundary.
Import PABoundedRawCodedFormulaBoundAtomicallyAdequateTotality.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

(** A supplied bound fixes the closure count.  Carrier-wide universal-closure
    totality chooses the axiom code, while ordinary substitution identity
    supplies self-instantiation through every strict closure prefix. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_exists_of_ordinary_identity
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement closureCount,
  RawCodedFormulaBound M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs)
    closureCount ->
  RawCodedFormulaSubstitutionIdentityAtAllDepths M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs) ->
  exists axiom : M,
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs replacement axiom closureCount.
Proof.
  intros M hPA inputs replacement closureCount hbound hidentity.
  destruct (raw_codedUniversalClosure_exists_all M hPA closureCount
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs)) as [axiom hclosure].
  exists axiom. repeat split.
  - exact hbound.
  - exact hclosure.
  - exact
      (raw_codedUniversalClosureSelfInstantiationThrough_of_identity
        M hPA replacement
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
          M inputs)
        closureCount hidentity).
Qed.

(** Bound totality applies because every directly translated template, and
    hence the literal strong-prefix body template, is atomically adequate.
    Both the closure count and the sealed axiom code are chosen internally. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_exists_of_ordinary_identity_total
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) replacement,
  RawCodedFormulaSubstitutionIdentityAtAllDepths M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs) ->
  exists closureCount axiom : M,
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs replacement axiom closureCount.
Proof.
  intros M hPA inputs replacement hidentity.
  pose proof
    (raw_codedFormulaBound_atomically_adequate_total M hPA)
    as hboundTotal.
  destruct (hboundTotal
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M inputs)
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode_atomically_adequate
      M hPA inputs)) as [closureCount hbound].
  destruct
    (raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_exists_of_ordinary_identity
      M hPA inputs replacement closureCount hbound hidentity)
    as [axiom hremainder].
  exists closureCount, axiom. exact hremainder.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrdinaryClosureRemainder.
