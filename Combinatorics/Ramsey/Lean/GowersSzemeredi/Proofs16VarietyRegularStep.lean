import GowersSzemeredi.Proofs16BohrLowerBound
import GowersSzemeredi.Proofs16BohrRegularStep
import GowersSzemeredi.Proofs16BohrBohrSections

/-! A regular step for bilinear Bohr varieties.

Naive variety doubling fails (research notes J.2: the shifted-family
problem). But the telescoping argument needs only a *global* ratio bound
between the end radii, and that follows from Bohr lower bounds.

* `bohr_union`: `B(K₁ ∪ K₂;ρ) = B(K₁;ρ) ∩ B(K₂;ρ)`.
* `variety_card_eq_sum`: `|V(ρ)| = Σ_{y ∈ B(Ψ;ρ)} |B(Γ ∪ {L_k y};ρ)|`.
* `variety_card_lower`: `N² ≤ M^(|Ψ| + |Γ| + r) · |V(ρ)|` for `1 ≤ ρM`.
* `variety_exists_regular_step`: among radii `ρ(1 − j/(2m))`, some
  consecutive ratio `|V(ρ_j)| / |V(ρ_{j+1})|` is at most
  `(M^(|Ψ|+|Γ|+r))^(1/m)`, with `M ≥ 2/ρ`.

For `m ≈ dim · log M / θ` this ratio is at most about `1 + θ`. Then all but
a `θ`-fraction of `V(ρ_j)` lies in `V(ρ_{j+1})`, which bounds the boundary
mass of the packing in research notes J.2. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

theorem bohr_union {N : Nat} [NeZero N] (K₁ K₂ : Finset (ZMod N)) (ρ : Real) :
    bohr (K₁ ∪ K₂) ρ = bohr K₁ ρ ∩ bohr K₂ ρ := by
  ext x
  simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    Finset.mem_union]
  constructor
  · intro h; exact ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩
  · rintro ⟨h1, h2⟩ r (hr | hr)
    · exact h1 r hr
    · exact h2 r hr

/-- The fibre decomposition of a bilinear Bohr variety. -/
theorem variety_card_eq_sum {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) (ρ : Real) :
    (bilinearBohrVariety Γ Ψ L ρ).card =
      ∑ y ∈ bohr Ψ ρ, (bohr (Γ ∪ Finset.univ.image fun k => L k y) ρ).card := by
  unfold bilinearBohrVariety
  rw [Finset.card_filter, Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.card_filter, bohr_union]
  congr 1

/-- **The variety lower bound.** -/
theorem variety_card_lower {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) {ρ : Real} (M : Nat) [NeZero M] (hM : 1 ≤ ρ * M) :
    N * N ≤ M ^ (Ψ.card + (Γ.card + r)) * (bilinearBohrVariety Γ Ψ L ρ).card := by
  rw [variety_card_eq_sum]
  have hfib : ∀ y, N ≤ M ^ (Γ.card + r) *
      (bohr (Γ ∪ Finset.univ.image fun k => L k y) ρ).card := by
    intro y
    have h := bohr_card_lower (Γ ∪ Finset.univ.image fun k => L k y) M hM
    have hcard : (Γ ∪ Finset.univ.image fun k => L k y).card ≤ Γ.card + r := by
      calc _ ≤ Γ.card + (Finset.univ.image fun k => L k y).card := Finset.card_union_le _ _
        _ ≤ Γ.card + r := by
            apply Nat.add_le_add_left
            calc _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
              _ = r := by simp
    calc N ≤ M ^ (Γ ∪ Finset.univ.image fun k => L k y).card * _ := h
      _ ≤ M ^ (Γ.card + r) * _ := by
          apply Nat.mul_le_mul_right
          exact Nat.pow_le_pow_right (NeZero.pos M) hcard
  have hΨ := bohr_card_lower Ψ M hM
  calc N * N ≤ (M ^ Ψ.card * (bohr Ψ ρ).card) * N := Nat.mul_le_mul_right N hΨ
    _ = M ^ Ψ.card * ∑ _y ∈ bohr Ψ ρ, N := by rw [Finset.sum_const, smul_eq_mul]; ring
    _ ≤ M ^ Ψ.card * ∑ y ∈ bohr Ψ ρ,
          M ^ (Γ.card + r) * (bohr (Γ ∪ Finset.univ.image fun k => L k y) ρ).card := by
        apply Nat.mul_le_mul_left
        exact Finset.sum_le_sum fun y _ => hfib y
    _ = M ^ (Ψ.card + (Γ.card + r)) *
          ∑ y ∈ bohr Ψ ρ, (bohr (Γ ∪ Finset.univ.image fun k => L k y) ρ).card := by
        rw [← Finset.mul_sum, pow_add]; ring

/-- Varieties grow with the radius. -/
theorem bilinearBohrVariety_mono {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) {ρ ρ' : Real} (h : ρ' ≤ ρ) :
    bilinearBohrVariety Γ Ψ L ρ' ⊆ bilinearBohrVariety Γ Ψ L ρ := by
  intro p hp
  unfold bilinearBohrVariety at hp ⊢
  obtain ⟨hprod, hvar⟩ := Finset.mem_filter.mp hp
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hprod
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨bohr_mono_radius Γ h hx,
    bohr_mono_radius Ψ h hy⟩, bohr_mono_radius _ h hvar⟩

/-- **A regular step for bilinear Bohr varieties.** -/
theorem variety_exists_regular_step {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) {ρ : Real} (hρ : 0 < ρ) (M : Nat) [NeZero M]
    (hM : 1 ≤ ρ / 2 * M) (m : Nat) (hm : 0 < m) :
    ∃ j, j < m ∧
      ((bilinearBohrVariety Γ Ψ L (ρ * (1 - j / (2 * m)))).card : Real) ≤
        ((M : Real) ^ (Ψ.card + (Γ.card + r))) ^ ((1 : Real) / m) *
          (bilinearBohrVariety Γ Ψ L (ρ * (1 - (j + 1 : Nat) / (2 * m)))).card := by
  set s : Nat → Real := fun j => ((bilinearBohrVariety Γ Ψ L (ρ * (1 - j / (2 * m)))).card : Real)
    with hsdef
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  set D := Ψ.card + (Γ.card + r)
  have hend : s 0 ≤ (((M : Real) ^ D) ^ ((1 : Real) / m)) ^ m * s m := by
    have hpow : (((M : Real) ^ D) ^ ((1 : Real) / m)) ^ m = (M : Real) ^ D := by
      rw [← Real.rpow_natCast (((M : Real) ^ D) ^ ((1 : Real) / m)) m, ← Real.rpow_mul (by positivity)]
      rw [one_div_mul_cancel hmR.ne', Real.rpow_one]
    rw [hpow]
    have em : ρ * (1 - (m : Real) / (2 * m)) = ρ / 2 := by field_simp; ring
    have hlow := variety_card_lower Γ Ψ L (ρ := ρ / 2) M hM
    have hup : (bilinearBohrVariety Γ Ψ L ρ).card ≤ N * N := by
      calc _ ≤ (Finset.univ : Finset (ZMod N × ZMod N)).card := Finset.card_le_univ _
        _ = N * N := by simp [ZMod.card]
    simp only [hsdef]
    have e0 : ρ * (1 - ((0 : Nat) : Real) / (2 * m)) = ρ := by simp
    rw [e0, em]
    have : (bilinearBohrVariety Γ Ψ L ρ).card ≤ M ^ D * (bilinearBohrVariety Γ Ψ L (ρ / 2)).card :=
      hup.trans hlow
    exact_mod_cast this
  exact exists_step_ratio_le (s := s) (C := ((M : Real) ^ D) ^ ((1 : Real) / m)) (by positivity) m hm hend

end LeanProofs.GowersSzemeredi
