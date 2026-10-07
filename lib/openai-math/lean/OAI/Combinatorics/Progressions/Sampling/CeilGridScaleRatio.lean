import OAI.Combinatorics.Progressions.Estimates.AllocatedPrincipalSourceScale
import OAI.Combinatorics.Progressions.Fourier.AllocatedGridSpectrumSize

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

noncomputable def allocatedPrincipalGridScale : ℕ :=
  ⌈gamma * (basisAxisScale (basis j) i : ℝ)⌉₊

include hR hactive

theorem allocatedPrincipal_support_scale_one_le :
    1 ≤ gamma * (basisAxisScale (basis j) i : ℝ) := by
  have hw := integerAxisPrincipal_width (Nat.zero_lt_succ j.val) S.positive
    (principalProfileSize_pos (hR j) _) (S.gap j i hactive)
  have hL : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hpow : (1 : ℝ) ≤ (S.value : ℝ) ^ (j.val + 1) := one_le_pow₀ hL
  have hp : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hw' : 8 * (probabilityProfileLipschitz : ℝ) * (S.value : ℝ) ^ (j.val + 1) ≤
      gamma / 2 * (basisAxisScale (basis j) i : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (S.value : ℝ) ^ (j.val + 1))).mp
    simpa only [mul_div_assoc] using hw
  nlinarith

theorem allocatedPrincipalGridScale_bounds :
    gamma * (basisAxisScale (basis j) i : ℝ) ≤ (allocatedPrincipalGridScale (G := G) B U basis (R := R) j i : ℝ) ∧
    (allocatedPrincipalGridScale (G := G) B U basis (R := R) j i : ℝ) ≤ 2 * gamma * basisAxisScale (basis j) i := by
  have h := allocatedPrincipal_support_scale_one_le B U basis hR S j i hactive
  refine ⟨Nat.le_ceil _, ?_⟩
  have hu := Nat.ceil_lt_add_one (show 0 ≤ gamma * (basisAxisScale (basis j) i : ℝ) by linarith)
  change (⌈gamma * (basisAxisScale (basis j) i : ℝ)⌉₊ : ℝ) ≤ _
  linarith

theorem allocatedPrincipalGridScale_pos :
    0 < allocatedPrincipalGridScale (G := G) B U basis (R := R) j i := by
  have h := allocatedPrincipal_support_scale_one_le B U basis hR S j i hactive
  have hl := (allocatedPrincipalGridScale_bounds B U basis hR S j i hactive).1
  have hp : (0 : ℝ) < allocatedPrincipalGridScale (G := G) B U basis (R := R) j i := by linarith
  exact_mod_cast hp

theorem allocatedPrincipalGridScale_ratio {H : ℝ} {M : ℕ} (hH : 0 ≤ H)
    (hM : (M : ℝ) ≤ H * allocatedPrincipalGridScale (G := G) B U basis (R := R) j i) :
    (M : ℝ) / (((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1)) ≤ H := by
  have hlen : (0 : ℝ) < (csource).length := Nat.cast_pos.mpr (csource).length_pos
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  apply (div_le_iff₀ (by positivity)).mpr
  exact hM.trans (mul_le_mul_of_nonneg_left
    ((allocatedPrincipalGridScale_bounds B U basis hR S j i hactive).2.trans
      (allocatedPrincipalNormalizedSource_scale_bounds B U basis hR S j i hactive).1) hH)

theorem allocatedPrincipalGridScale_cardinality
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value)
    {H : ℝ} {M : ℕ} (hH : 0 ≤ H)
    (hM : (M : ℝ) ≤ H * allocatedPrincipalGridScale (G := G) B U basis (R := R) j i) (d : ℕ) :
    (M : ℝ) ^ d ≤ (2 * H) ^ d * (S.value : ℝ) ^ ((layerTailDegree m + 2) * d) := by
  have hgamma0 : 0 ≤ gamma := (principalProfileSize_pos (hR j) _).le
  change basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1) at hgrid
  have hK : (basisAxisScale (basis j) i : ℝ) ≤ (S.value : ℝ) ^ (layerTailDegree m + 1) := by
    exact_mod_cast hgrid
  have hbase : (M : ℝ) ≤ 2 * H * (S.value : ℝ) ^ (layerTailDegree m + 2) := by
    calc
      (M : ℝ) ≤ H * (2 * gamma * basisAxisScale (basis j) i) :=
        hM.trans (mul_le_mul_of_nonneg_left
          (allocatedPrincipalGridScale_bounds B U basis hR S j i hactive).2 hH)
      _ ≤ H * (2 * (S.value : ℝ) * (S.value : ℝ) ^ (layerTailDegree m + 1)) := by
        gcongr
      _ = _ := by rw [pow_succ]; ring
  calc
    (M : ℝ) ^ d ≤ (2 * H * (S.value : ℝ) ^ (layerTailDegree m + 2)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg M) hbase d
    _ = _ := by rw [mul_pow, ← pow_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem ceilGridScale_ratio_bounds (K : ℕ) (hK : 0 < K) {γ : ℝ} (hγ : 0 < γ) :
    0 < ⌈γ * (K : ℝ)⌉₊ ∧
    γ ≤ (⌈γ * (K : ℝ)⌉₊ : ℝ) / K ∧
    (⌈γ * (K : ℝ)⌉₊ : ℝ) / K ≤ γ + 1 ∧
    (K : ℝ) / ⌈γ * (K : ℝ)⌉₊ ≤ γ⁻¹ := by
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hK1 : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK
  have hN : 0 < ⌈γ * (K : ℝ)⌉₊ := Nat.ceil_pos.mpr (mul_pos hγ hKr)
  have hNr : (0 : ℝ) < ⌈γ * (K : ℝ)⌉₊ := Nat.cast_pos.mpr hN
  have hlow := Nat.le_ceil (γ * (K : ℝ))
  have hu := Nat.ceil_lt_add_one (mul_nonneg hγ.le hKr.le)
  refine ⟨hN, (le_div_iff₀ hKr).mpr hlow, (div_le_iff₀ hKr).mpr ?_, ?_⟩
  · nlinarith only [hu, hK1]
  · apply (div_le_iff₀ hNr).mpr
    calc
      (K : ℝ) = γ⁻¹ * (γ * (K : ℝ)) := by rw [← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul]
      _ ≤ γ⁻¹ * ⌈γ * (K : ℝ)⌉₊ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hγ.le)

theorem ceilGridScale_mass_bound (K d : ℕ) (hK : 0 < K) {γ μ C : ℝ}
    (hγ : 0 < γ) (hμ : 0 ≤ μ) (_hC : 0 ≤ C)
    (hcap : (K : ℝ) ^ d * μ ≤ C) :
    (⌈γ * (K : ℝ)⌉₊ : ℝ) ^ d * μ ≤ (γ + 1) ^ d * C := by
  obtain ⟨_, _, hratio, _⟩ := ceilGridScale_ratio_bounds K hK hγ
  have hK0 : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hr : ((⌈γ * (K : ℝ)⌉₊ : ℝ) / K) * K = ⌈γ * (K : ℝ)⌉₊ := div_mul_cancel₀ _ hK0
  calc
    _ = ((⌈γ * (K : ℝ)⌉₊ : ℝ) / K) ^ d * ((K : ℝ) ^ d * μ) := by
      rw [← mul_assoc, ← mul_pow, hr]
    _ ≤ (γ + 1) ^ d * C := mul_le_mul
      (pow_le_pow_left₀ (by positivity) hratio d) hcap (by positivity) (by positivity)

end Erdos3

end

end OAI
