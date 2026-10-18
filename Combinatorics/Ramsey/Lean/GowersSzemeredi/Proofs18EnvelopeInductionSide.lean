import GowersSzemeredi.Proofs18EnvelopeInduction

/-! Declarations of `Proofs18EnvelopeInduction` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Instantiate a class-cover theorem from recurrence profiles and raise each
lower-dimensional cover to the common base of the current dimension. -/
theorem classCovers_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    {degree : Nat → Nat}
    (hclass : (∀ k, 1 ≤ Kc k) →
      (∀ k, 1 ≤ k → AbstractFamilyLemma166At k
        (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) →
      ∀ {l : Nat}, 1 ≤ l →
        PolyCoverAt l (uCount (classV Kc pc l) (degree l)) (uExp (classV Kc pc l) (degree l)))
    {k : Nat} : ∀ l, 1 ≤ l → l ≤ k →
      PolyCoverAt l (uCount (classV Kc pc k) (degree l)) (uExp (classV Kc pc k) (degree l)) := by
  intro l hl hlk
  have hcover := hclass (fun j => (by omega : 1 ≤ 2).trans (hK j))
    (fun j hj => abstractFamilyLemma166At_of j (hK j) (hp j) (hrec j hj)) hl
  exact hcover.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl

end LeanProofs.GowersSzemeredi
