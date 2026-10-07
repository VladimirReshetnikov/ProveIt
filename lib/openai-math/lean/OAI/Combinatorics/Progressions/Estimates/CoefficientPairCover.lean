import OAI.Combinatorics.Progressions.Probability.CanonicalCoverLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory

variable {K : Type*} [finiteK : Fintype K] {m : ℕ} {J : Fin m → Type*}
  [finiteCoordinates : ∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientAmbientTorus_continuous : Continuous (coefficientAmbientTorus (K := K) U) := by
  apply continuous_pi
  intro a
  exact (continuous_apply a.2).comp ((subspaceAmbientTorus_continuous (U a.1.1)).comp
    ((continuous_apply a.1).comp (coefficientCoordinateTorus_continuous U)))

omit finiteK finiteCoordinates in
theorem coefficientAmbientTorus_cover [Fintype K] [∀ j, Fintype (J j)]
    (a : ℕ) (z : CoefficientTorus (K := K) U) :
    coefficientAmbientTorus U (quotientIntegerCover (coefficientIntegerLattice U) a z) =
      a • coefficientAmbientTorus U z := by
  funext t
  change subspaceAmbientTorus (U t.1.1) (coefficientCoordinateTorus U (a • z) t.1) t.2 =
    a • subspaceAmbientTorus (U t.1.1) (coefficientCoordinateTorus U z t.1) t.2
  simp only [map_nsmul, Pi.smul_apply]

theorem coefficientAmbient_pair_integral_common_cover
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (a : ℕ) (ha : 0 < a) (b c : ℕ)
    (f g : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ z, f ((a * b) • coefficientAmbientTorus U z) * star (g ((a * c) • coefficientAmbientTorus U z)) ∂μ) =
      ∫ z, f (b • coefficientAmbientTorus U z) * star (g (c • coefficientAmbientTorus U z)) ∂μ := by
  have hcont := coefficientAmbientTorus_continuous (K := K) U
  have hF : Continuous (fun z : CoefficientTorus (K := K) U =>
      f (b • coefficientAmbientTorus U z) * star (g (c • coefficientAmbientTorus U z))) :=
    (hf.comp (hcont.nsmul b)).mul (hg.comp (hcont.nsmul c)).star
  have he := coefficientCover_integral U μ a ha _ hF.measurable.aestronglyMeasurable
  simpa only [coefficientAmbientTorus_cover, smul_smul, mul_comm] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical

theorem exists_finite_pair_common_cover {A : Type*} [Fintype A]
    (period : A → ℕ) (hp : ∀ a, 0 < period a) :
    ∃ D : ℕ, 0 < D ∧ ∀ a b, period a * period b ∣ D := by
  let Q := ∏ a, period a
  have hQ : 0 < Q := Finset.prod_pos (fun a _ => hp a)
  refine ⟨Q * Q, Nat.mul_pos hQ hQ, ?_⟩
  intro a b
  exact Nat.mul_dvd_mul (Finset.dvd_prod_of_mem period (Finset.mem_univ a))
    (Finset.dvd_prod_of_mem period (Finset.mem_univ b))

theorem exists_finite_pair_common_cover_with_base {A : Type*} [Fintype A]
    (d : ℕ) (hd : 0 < d) (period : A → ℕ) (hp : ∀ a, 0 < period a) :
    ∃ D : ℕ, 0 < D ∧ d ∣ D ∧ ∀ a b, period a * period b ∣ D := by
  obtain ⟨D, hD, hdiv⟩ := exists_finite_pair_common_cover period hp
  exact ⟨d * D, Nat.mul_pos hd hD, dvd_mul_right d D,
    fun a b => (hdiv a b).trans (dvd_mul_left D d)⟩

theorem div_factor_of_mul_dvd {a b D : ℕ} (ha : 0 < a) (hab : a * b ∣ D) :
    D / a = (D / (a * b)) * b := by
  have hd : a ∣ D := (dvd_mul_right a b).trans hab
  apply Nat.eq_of_mul_eq_mul_right ha
  calc
    (D / a) * a = D := Nat.div_mul_cancel hd
    _ = (D / (a * b)) * (a * b) := (Nat.div_mul_cancel hab).symm
    _ = _ := by ac_rfl

theorem coefficientAmbient_pair_integral_divisors
    {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D a b : ℕ) (hD : 0 < D) (ha : 0 < a) (hb : 0 < b) (hab : a * b ∣ D)
    (f g : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ z, f ((D / a) • coefficientAmbientTorus U z) * star (g ((D / b) • coefficientAmbientTorus U z)) ∂μ) =
      ∫ z, f (b • coefficientAmbientTorus U z) * star (g (a • coefficientAmbientTorus U z)) ∂μ := by
  have hratio : 0 < D / (a * b) := Nat.div_pos (Nat.le_of_dvd hD hab) (Nat.mul_pos ha hb)
  have hba : b * a ∣ D := by simpa only [mul_comm] using hab
  rw [div_factor_of_mul_dvd ha hab, div_factor_of_mul_dvd hb hba]
  simpa only [mul_comm a b] using
    coefficientAmbient_pair_integral_common_cover U μ (D / (a * b)) hratio b a f g hf hg

end Erdos3.VectorPolynomial

end

end OAI
