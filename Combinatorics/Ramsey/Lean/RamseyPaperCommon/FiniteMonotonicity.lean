import RamseyPaperCommon.FiniteBridges

/-!
# Monotonicity in the forbidden progression length

A long arithmetic progression contains every shorter initial progression.
Consequently, avoiding a `small`-term progression is stronger than avoiding a
`large`-term progression when `small ≤ large`.  This file records that fact at
four useful levels: arbitrary sequences, finite permutations in either paper
encoding, canonical embeddings of the avoiding subtypes, and their cardinalities.
-/

set_option autoImplicit false

namespace LeanProofs.RamseyPaperCommon

/-- Every `large`-term AP subsequence contains a `small`-term AP subsequence
when `small ≤ large`, obtained by retaining its initial entries. -/
theorem hasAPSubsequence_of_le {I : Type*} [LinearOrder I]
    {small large : Nat} (hsmalllarge : small ≤ large) {sequence : I -> Nat}
    (hlarge : LeanProofs.LeSaulnierVijay2011.HasAPSubsequence large sequence) :
    LeanProofs.LeSaulnierVijay2011.HasAPSubsequence small sequence := by
  rcases hlarge with
    ⟨indices, hindices, a, d, hd, _, hformula⟩
  let embed : Fin small -> Fin large := Fin.castLE hsmalllarge
  refine ⟨fun i => indices (embed i), hindices.comp (Fin.strictMono_castLE _),
    a, d, hd, trivial, ?_⟩
  intro i
  exact hformula (embed i)

/-- Finite avoidance in the LeSaulnier--Vijay encoding is monotone in the
forbidden progression length. -/
theorem isFiniteKAvoiding_mono_length {n small large : Nat}
    (hsmalllarge : small ≤ large) (sigma : Equiv.Perm (Fin n))
    (hsmall : LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding small sigma) :
    LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding large sigma := by
  intro hlarge
  exact hsmall (hasAPSubsequence_of_le hsmalllarge hlarge)

/-- Finite avoidance in the Davis encoding is monotone in the forbidden
progression length. -/
theorem finiteAPFree_mono_length {n small large : Nat}
    (hsmalllarge : small ≤ large) (sigma : Equiv.Perm (Fin n))
    (hsmall : LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma small) :
    LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma large := by
  rw [finiteAPFree_iff] at hsmall ⊢
  exact isFiniteKAvoiding_mono_length hsmalllarge sigma hsmall

/-- The inclusion from `small`-avoiding to `large`-avoiding finite
permutations, in the Davis encoding. -/
def finiteAPFreeEmbedding (n : Nat) {small large : Nat}
    (hsmalllarge : small ≤ large) :
    {sigma : Equiv.Perm (Fin n) //
      LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma small} ↪
      {sigma : Equiv.Perm (Fin n) //
        LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma large} where
  toFun sigma :=
    ⟨sigma.1, finiteAPFree_mono_length hsmalllarge sigma.1 sigma.2⟩
  inj' a b h := by
    apply Subtype.ext
    simpa using congrArg Subtype.val h

/-- The inclusion from `small`-avoiding to `large`-avoiding finite
permutations, in the LeSaulnier--Vijay encoding. -/
def finiteKAvoidingEmbedding (n : Nat) {small large : Nat}
    (hsmalllarge : small ≤ large) :
    {sigma : Equiv.Perm (Fin n) //
      LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding small sigma} ↪
      {sigma : Equiv.Perm (Fin n) //
        LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding large sigma} where
  toFun sigma :=
    ⟨sigma.1, isFiniteKAvoiding_mono_length hsmalllarge sigma.1 sigma.2⟩
  inj' a b h := by
    apply Subtype.ext
    simpa using congrArg Subtype.val h

/-- The number of Davis-encoded avoiding permutations is nondecreasing in the
forbidden progression length. -/
theorem natCard_finiteAPFree_mono_length (n : Nat) {small large : Nat}
    (hsmalllarge : small ≤ large) :
    Nat.card {sigma : Equiv.Perm (Fin n) //
      LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma small} ≤
      Nat.card {sigma : Equiv.Perm (Fin n) //
        LeanProofs.DavisEntringerGrahamSimmons1977.FiniteAPFree sigma large} :=
  Nat.card_le_card_of_injective _ (finiteAPFreeEmbedding n hsmalllarge).injective

/-- The number of LeSaulnier--Vijay-encoded avoiding permutations is
nondecreasing in the forbidden progression length. -/
theorem natCard_isFiniteKAvoiding_mono_length (n : Nat) {small large : Nat}
    (hsmalllarge : small ≤ large) :
    Nat.card {sigma : Equiv.Perm (Fin n) //
      LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding small sigma} ≤
      Nat.card {sigma : Equiv.Perm (Fin n) //
        LeanProofs.LeSaulnierVijay2011.IsFiniteKAvoiding large sigma} :=
  Nat.card_le_card_of_injective _ (finiteKAvoidingEmbedding n hsmalllarge).injective

end LeanProofs.RamseyPaperCommon
