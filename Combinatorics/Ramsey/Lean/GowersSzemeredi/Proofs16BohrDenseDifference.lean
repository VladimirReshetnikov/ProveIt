import GowersSzemeredi.Proofs16BohrDoubling
import GowersSzemeredi.Proofs16BohrBohrSections

/-! Milićević's Lemma 2.5: very dense subsets of Bohr sets have full
difference sets on the half-radius Bohr set.

arXiv:2601.01682, Lemma 2.5. Let `A ⊆ B(Γ;ρ)` with
`|A| ≥ (1 − 4^(−k−1))|B(Γ;ρ)|`, where `k = |Γ|`. Then `A − A ⊇ B(Γ;ρ/2)`.

It is stated here as `4^(k+1)·|B(Γ;ρ) ∖ A| ≤ |B(Γ;ρ)|`. The proof counts.
For `d ∈ B(ρ/2)`, every `z ∈ B(ρ/2)` has `z, z + d ∈ B(ρ)`. At most
`|B ∖ A|` of these `z` have `z ∉ A`, and at most `|B ∖ A|` have `z + d ∉ A`.
But `|B(ρ/2)| ≥ 4^(−k)|B(ρ)|` (`bohr_card_le_four_pow`) is more than twice
that. This is the first leaf of Milićević's pipeline toward Theorem 1.4
formalized here; the rest of the pipeline is not. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Bohr sets are closed under adding two half-radius elements. -/
theorem bohr_add_half {N : Nat} [NeZero N] {K : Finset (ZMod N)} {ρ : Real} {x y : ZMod N}
    (hx : x ∈ bohr K (ρ / 2)) (hy : y ∈ bohr K (ρ / 2)) : x + y ∈ bohr K ρ := by
  unfold bohr at hx hy ⊢
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  have h1 := (Finset.mem_filter.mp hx).2 r hr
  have h2 := (Finset.mem_filter.mp hy).2 r hr
  have h3 : (centeredAbs (r * (x + y)) : Real) ≤ centeredAbs (r * x) + centeredAbs (r * y) := by
    rw [mul_add]
    exact_mod_cast centeredAbs_add_le _ _
  linarith

/-- The centre lies in every Bohr set of nonnegative radius. -/
theorem zero_mem_bohr {N : Nat} [NeZero N] (K : Finset (ZMod N)) {ρ : Real} (hρ : 0 ≤ ρ) :
    (0 : ZMod N) ∈ bohr K ρ := by
  unfold bohr
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r _ => ?_⟩
  simp only [mul_zero, centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.cast_zero]
  positivity

/-- **Milićević, Lemma 2.5.** -/
theorem bohr_dense_sub_cover {N : Nat} [NeZero N] (K : Finset (ZMod N)) {ρ : Real} (hρ : 0 < ρ)
    (A : Finset (ZMod N)) (hA : 4 ^ (K.card + 1) * (bohr K ρ \ A).card ≤ (bohr K ρ).card)
    (d : ZMod N) (hd : d ∈ bohr K (ρ / 2)) : ∃ a ∈ A, ∃ b ∈ A, d = a - b := by
  set B := bohr K ρ
  set T := bohr K (ρ / 2)
  have hBT : B.card ≤ 4 ^ K.card * T.card := bohr_card_le_four_pow K hρ
  have hTB : ∀ z ∈ T, z ∈ B := fun z hz => bohr_mono_radius K (by linarith) hz
  by_contra hcon
  push Not at hcon
  -- every `z ∈ T` is bad
  have hbad : T ⊆ (T.filter fun z => z ∉ A) ∪ (T.filter fun z => z + d ∉ A) := by
    intro z hz
    by_cases hzA : z ∈ A
    · by_cases hzdA : z + d ∈ A
      · exact absurd (by ring : d = (z + d) - z) (hcon _ hzdA _ hzA)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hzdA⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hzA⟩)
  have h1 : (T.filter fun z => z ∉ A).card ≤ (B \ A).card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hzT, hzA⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_sdiff.mpr ⟨hTB z hzT, hzA⟩
  have h2 : (T.filter fun z => z + d ∉ A).card ≤ (B \ A).card := by
    calc (T.filter fun z => z + d ∉ A).card
        = ((T.filter fun z => z + d ∉ A).image fun z => z + d).card :=
          (Finset.card_image_of_injective _ (add_left_injective d)).symm
      _ ≤ (B \ A).card := by
          apply Finset.card_le_card
          intro w hw
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨hzT, hzdA⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_sdiff.mpr ⟨bohr_add_half hzT hd, hzdA⟩
  have hT2 : T.card ≤ 2 * (B \ A).card :=
    (Finset.card_le_card hbad).trans ((Finset.card_union_le _ _).trans (by omega))
  have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨0, zero_mem_bohr K (by linarith)⟩
  -- `4^(k+1)|B∖A| ≤ |B| ≤ 4^k|T| ≤ 2·4^k|B∖A|` forces `|B∖A| = 0`, then `|T| = 0`
  have hpow : 0 < 4 ^ K.card := by positivity
  have hchain : 4 ^ K.card * (4 * (B \ A).card) ≤ 4 ^ K.card * (2 * (B \ A).card) := by
    calc 4 ^ K.card * (4 * (B \ A).card) = 4 ^ (K.card + 1) * (B \ A).card := by ring
      _ ≤ B.card := hA
      _ ≤ 4 ^ K.card * T.card := hBT
      _ ≤ 4 ^ K.card * (2 * (B \ A).card) := Nat.mul_le_mul_left _ hT2
  have hzero : (B \ A).card = 0 := by
    have := Nat.le_of_mul_le_mul_left hchain hpow
    omega
  omega

end LeanProofs.GowersSzemeredi
