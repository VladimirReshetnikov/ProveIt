import DiophantineConsistency.FoundationZFCConsistencyNat
import DiophantineConsistency.FoundationHACurrentTransfer

/-! # Closed HA comparison of two fixed translated consistency sentences

The actual, closed Foundation PA theorem is transferred through the existing
Peano-to-HA proof map. The existing implication bridge then gives ordinary HA
implications between the two GG-translated sentences. No source-proof premise
or semantic implication is used in place of an HA derivation.

The validator target remains its literal GG image. This does not identify it
with an untranslated checker in HA, and makes no current-equation claim.
-/
set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.FoundationHAZFCValidator
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.PA HA FoundationPAHFSyntax
open FoundationZFCConsistencyNat
open LeanProofs.ZFCinPA.ValidatorConsistencyForward254
open LeanProofs.ZFCinPA.ValidatorConsistencyEquivalence

/-- The fixed target is the GG image of the actual C254 consistency sentence. -/
noncomputable def ggValidator : Formula :=
  sentence validatorConsistencySentenceᴺ

/-- A closed HA theorem, obtained from the existing closed PA theorem rather
than an assumption that the desired source equivalence is provable. -/
theorem translated_equivalence :
    Proves (sentence (sourceSentence 🡘 validatorConsistencySentence)ᴺ) :=
  FoundationHAPeano.peano_provable peano_proves_con_ZFC_iff_validator

/-- Both endpoints are fixed translated sentences; this is an ordinary
object-language implication in the conventional HA proof relation. -/
theorem consistency_to_validator : Proves (.imp ggConsistency ggValidator) := by
  have h := translated_equivalence
  change Proves (.and (sentence (sourceSentence 🡒 validatorConsistencySentence)ᴺ)
    (sentence (validatorConsistencySentence 🡒 sourceSentence)ᴺ)) at h
  exact FoundationHACurrentTransfer.sentence_imp_elim h.and_left

theorem validator_to_consistency : Proves (.imp ggValidator ggConsistency) := by
  have h := translated_equivalence
  change Proves (.and (sentence (sourceSentence 🡒 validatorConsistencySentence)ᴺ)
    (sentence (validatorConsistencySentence 🡒 sourceSentence)ᴺ)) at h
  exact FoundationHACurrentTransfer.sentence_imp_elim h.and_right

/-- This pair of HA derivations is unconditional. Its targets remain
`GG(Con(ZFC))` and `GG(validator consistency)` under the fixed syntax map. -/
theorem equivalence : Proves (.and
    (.imp ggConsistency ggValidator) (.imp ggValidator ggConsistency)) :=
  consistency_to_validator.and_intro validator_to_consistency

end DiophantineConsistency.FoundationHAZFCValidator
