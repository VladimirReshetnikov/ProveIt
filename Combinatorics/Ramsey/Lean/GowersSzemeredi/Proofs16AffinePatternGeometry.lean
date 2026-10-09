import GowersSzemeredi.Proofs16PatternRecentering

/-! Constant and varying frequencies for affine formulas on a common
parameter domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def affinePatternConstants {N m : Nat} (c₀ c₂ : Fin m → ZMod N)
    (L : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m)) (z w : ZMod N) :
    Finset (ZMod N) :=
  (J 0).image c₀ ∪ (J 1).image (fun i => L i z) ∪
    (J 2).image c₂ ∪ (J 3).image (fun i => L i w)

theorem affinePatternConstants_card_le {N m ell : Nat} (c₀ c₂ : Fin m → ZMod N)
    (L : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m)) (z w : ZMod N)
    (hJ : ∀ i, (J i).card ≤ ell) : (affinePatternConstants c₀ c₂ L J z w).card ≤ 4 * ell := by
  have h0 := (Finset.card_image_le (s := J 0) (f := c₀)).trans (hJ 0)
  have h1 := (Finset.card_image_le (s := J 1) (f := fun i => L i z)).trans (hJ 1)
  have h2 := (Finset.card_image_le (s := J 2) (f := c₂)).trans (hJ 2)
  have h3 := (Finset.card_image_le (s := J 3) (f := fun i => L i w)).trans (hJ 3)
  have hu1 := Finset.card_union_le ((J 0).image c₀) ((J 1).image fun i => L i z)
  have hu2 := Finset.card_union_le ((J 0).image c₀ ∪ (J 1).image fun i => L i z) ((J 2).image c₂)
  have hu3 := Finset.card_union_le
    ((J 0).image c₀ ∪ (J 1).image (fun i => L i z) ∪ (J 2).image c₂)
    ((J 3).image fun i => L i w)
  unfold affinePatternConstants
  omega

theorem pattern_bohr_of_affine {N m : Nat} [NeZero N]
    (L psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m))
    (c₀ c₂ : Fin m → ZMod N) (x y z w d : ZMod N) {eta : Real} (heta : 0 ≤ eta)
    (h0 : ∀ i ∈ J 0, L i (y + z) = c₀ i + psi i x)
    (h2 : ∀ i ∈ J 2, L i (y + w) = c₂ i + psi i x)
    (hc : d ∈ bohr (affinePatternConstants c₀ c₂ L J z w) (eta / 2))
    (hv : d ∈ bohr (varyingPatternFrequencies psi J x) (eta / 2)) :
    d ∈ bohr (patternFrequencies L J y z w) eta := by
  have hconst := (Finset.mem_filter.mp hc).2
  have hvar := (Finset.mem_filter.mp hv).2
  have hadd (u v : ZMod N)
      (hu : (centeredAbs (u * d) : Real) ≤ eta / 2 * N)
      (hv' : (centeredAbs (v * d) : Real) ≤ eta / 2 * N) :
      (centeredAbs ((u + v) * d) : Real) ≤ eta * N := by
    have h : (centeredAbs ((u + v) * d) : Real) ≤ centeredAbs (u * d) + centeredAbs (v * d) := by
      rw [add_mul]
      exact_mod_cast centeredAbs_add_le (u * d) (v * d)
    linarith
  have hhalf : eta / 2 * (N : Real) ≤ eta * N := by
    have hN : (0 : Real) ≤ N := Nat.cast_nonneg N
    nlinarith
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  simp only [patternFrequencies, Finset.mem_union, Finset.mem_image] at hr
  rcases hr with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · rw [h0 i hi]
    exact hadd _ _ (hconst _ (by
      simp only [affinePatternConstants, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩))))
      (hvar _ (Finset.mem_image.mpr ⟨i, Finset.mem_union_left _ hi, rfl⟩))
  · exact (hconst _ (by
      simp only [affinePatternConstants, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩)))).trans hhalf
  · rw [h2 i hi]
    exact hadd _ _ (hconst _ (by
      simp only [affinePatternConstants, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inr ⟨i, hi, rfl⟩)))
      (hvar _ (Finset.mem_image.mpr ⟨i, Finset.mem_union_right _ hi, rfl⟩))
  · exact (hconst _ (by
      simp only [affinePatternConstants, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨i, hi, rfl⟩)).trans hhalf

end LeanProofs.GowersSzemeredi
