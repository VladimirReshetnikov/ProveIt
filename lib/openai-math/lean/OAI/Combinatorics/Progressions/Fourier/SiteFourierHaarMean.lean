/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FiniteImageProducts
import OAI.Combinatorics.Progressions.Linear.IntegralCoefficientBasis

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteTensorExpansion {D : Type*} [Fintype D] [DecidableEq D]
    {A Z : D → Type*} [∀ d, Fintype (A d)] (c : ∀ d, A d → ℂ)
    (ψ : ∀ d, A d → Z d → ℂ) (z : ∀ d, Z d) :
    (∏ d, ∑ a, c d a * ψ d a (z d)) =
      ∑ a : ∀ d, A d, (∏ d, c d (a d)) * (∏ d, ψ d (a d) (z d)) := by
  simp only [← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun d a => c d a * ψ d a (z d))

theorem finiteTensorCoefficientMass {D : Type*} [Fintype D] [DecidableEq D]
    {A : D → Type*} [∀ d, Fintype (A d)] (c : ∀ d, A d → ℂ) :
    (∑ a : ∀ d, A d, ‖∏ d, c d (a d)‖) = ∏ d, ∑ a, ‖c d a‖ := by
  simp only [norm_prod]
  exact (Fintype.prod_sum (fun d a => ‖c d a‖)).symm

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

noncomputable def coefficientTorusFourierSum {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (x : CoefficientTorus (K := K) U) : ℂ := ∑ a, c a * coefficientTorusCharacter U (frequency a) x

theorem coefficientTorusFourierSum_integrable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ] :
    Integrable (coefficientTorusFourierSum U frequency c) μ := by
  apply integrable_finsetSum
  intro a _
  exact (coefficientTorusCharacter_integrable U (frequency a) μ).const_mul (c a)

theorem coefficientTorusFourierSum_integral {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, coefficientTorusFourierSum U frequency c x ∂μ) =
      ∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0 := by
  change (∫ x, ∑ a, c a * coefficientTorusCharacter U (frequency a) x ∂μ) = _
  rw [integral_finsetSum _ (fun a _ => (coefficientTorusCharacter_integrable U (frequency a) μ).const_mul (c a))]
  simp only [integral_const_mul, coefficientTorusCharacter_integral]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def dilateCoefficientFrequency {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (q : ℕ) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : ∀ j, (K →₀ ℕ) → J j → ℤ :=
  fun j d a => (q : ℤ) * frequency j d a

theorem coefficientArrayFunctional_dilate {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (q : ℕ) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    coefficientArrayFunctional U (dilateCoefficientFrequency q frequency) =
      (q : ℝ) • coefficientArrayFunctional U frequency := by
  apply LinearMap.ext
  intro x
  change (∑ s : CoefficientSlot K m, ∑ a,
    (dilateCoefficientFrequency q frequency s.1 s.2.val a : ℝ) * (x s).val a) =
      (q : ℝ) * (∑ s : CoefficientSlot K m, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a)
  simp only [dilateCoefficientFrequency, Int.cast_mul, Int.cast_natCast, Finset.mul_sum, mul_assoc]

theorem affineCoefficientModeTrivial_dilate_iff {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (q : ℕ) (hq : 0 < q) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    affineCoefficientModeTrivial U (dilateCoefficientFrequency q frequency) ↔
      affineCoefficientModeTrivial U frequency := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← coefficientArrayFunctional_eq_zero_iff_trivial U (dilateCoefficientFrequency q frequency),
    ← coefficientArrayFunctional_eq_zero_iff_trivial U frequency, coefficientArrayFunctional_dilate]
  simp only [smul_eq_zero, hq0, false_or]

theorem coefficientTorusCharacter_cover {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (q : ℕ) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) (x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U frequency (quotientIntegerCover (coefficientIntegerLattice U) q x) =
      coefficientTorusCharacter U (dilateCoefficientFrequency q frequency) x := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [quotientIntegerCover_mk, coefficientTorusCharacter_mk, coefficientTorusCharacter_mk,
    coefficientArrayFunctional_dilate]
  simp only [map_smul, LinearMap.smul_apply]

theorem dilateCoefficientFrequency_bound {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (q : ℕ) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) {C : ℝ}
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C) :
    ∀ j d, d.degree ≤ j.val + 1 → ∀ a,
      |(dilateCoefficientFrequency q frequency j d a : ℝ)| ≤ (q : ℝ) * C := by
  intro j d hd a
  simp only [dilateCoefficientFrequency, Int.cast_mul, Int.cast_natCast, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ q from Nat.cast_nonneg q)]
  exact mul_le_mul_of_nonneg_left (hbound j d hd a) (Nat.cast_nonneg q)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientTorusCharacter_norm (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientTorus (K := K) U) : ‖coefficientTorusCharacter U frequency x‖ = 1 :=
  quotientLinearCharacter_norm _ _ _ _

theorem coefficientTorusFourierSum_norm_le
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (x : CoefficientTorus (K := K) U) :
    ‖coefficientTorusFourierSum U frequency c x‖ ≤ ∑ a, ‖c a‖ := by
  unfold coefficientTorusFourierSum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  simp only [norm_mul, coefficientTorusCharacter_norm, mul_one, le_refl]

theorem coefficientDensity_cap_of_fourier
    (D : CoefficientTorus (K := K) U → ℝ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    {ε M : ℝ} (hc : (∑ a, ‖c a‖) ≤ M)
    (herr : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ ε)
    (x : CoefficientTorus (K := K) U) : D x ≤ ε + M := by
  have hnorm := norm_le_norm_sub_add (D x : ℂ) (coefficientTorusFourierSum U frequency c x)
  have hsum := (coefficientTorusFourierSum_norm_le U frequency c x).trans hc
  have hreal : D x ≤ ‖(D x : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using le_abs_self (D x)
  linarith [herr x]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {K Y : Type*} [Fintype K] [Fintype Y] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (law : FiniteProbabilityWeights Y)
variable {F : Y → Type*} [∀ y, Fintype (F y)]
variable (frequency : ∀ y, F y → ∀ j, (K →₀ ℕ) → J j → ℤ)
variable (coeff : ∀ y, F y → ℂ)

theorem coefficientTorusFourierSum_mixture (z : CoefficientTorus (K := K) U) :
    coefficientTorusFourierSum U (fun a : Σ y, F y => frequency a.1 a.2)
      (fun a : Σ y, F y => (law.weight a.1 : ℂ) * coeff a.1 a.2) z =
      law.complexMean (fun y => coefficientTorusFourierSum U (frequency y) (coeff y) z) := by
  simp only [coefficientTorusFourierSum, Fintype.sum_sigma,
    FiniteProbabilityWeights.complexMean, Finset.mul_sum, mul_assoc]

omit [Fintype K] [∀ j, Fintype (J j)] in
theorem coefficientFourierMixture_mass_le {C : ℝ}
    (hcoeff : ∀ y, (∑ a, ‖coeff y a‖) ≤ C) :
    (∑ a : Σ y, F y, ‖(law.weight a.1 : ℂ) * coeff a.1 a.2‖) ≤ C := by
  simp only [Fintype.sum_sigma, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (law.nonneg _), ← Finset.mul_sum]
  exact (law.mean_mono hcoeff).trans_eq (law.mean_const C)

theorem coefficientFourierMixture_uniform_error
    (g : Y → CoefficientTorus (K := K) U → ℝ) {δ : ℝ}
    (happrox : ∀ y z, ‖(g y z : ℂ) - coefficientTorusFourierSum U (frequency y) (coeff y) z‖ ≤ δ)
    (z : CoefficientTorus (K := K) U) :
    ‖(law.mean (fun y => g y z) : ℂ) -
      coefficientTorusFourierSum U (fun a : Σ y, F y => frequency a.1 a.2)
        (fun a : Σ y, F y => (law.weight a.1 : ℂ) * coeff a.1 a.2) z‖ ≤ δ := by
  rw [coefficientTorusFourierSum_mixture, ← law.complexMean_ofReal]
  exact (law.norm_complexMean_sub_le _ _ (fun _ => δ) (fun y _ => happrox y z)).trans_eq
    (law.mean_const δ)

theorem exists_coefficientFourierMixture
    (g : Y → CoefficientTorus (K := K) U → ℝ) {C L δ : ℝ}
    (h : ∀ y, ∃ (F : Type) (inst : Fintype F), let _ := inst
      ∃ (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : F → ℂ),
        (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ L) ∧
        (∑ a, ‖coeff a‖) ≤ C ∧
        ∀ z, ‖(g y z : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ δ) :
    ∃ (F : Type) (inst : Fintype F), let _ := inst
      ∃ (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : F → ℂ),
        (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ L) ∧
        (∑ a, ‖coeff a‖) ≤ C ∧
        ∀ z, ‖(law.mean (fun y => g y z) : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ δ := by
  choose F inst frequency coeff hfreq hcoeff happ using h
  let _ := inst
  let e := (Fintype.equivFin (Σ y, F y)).symm
  let mixfreq := fun a : Σ y, F y => frequency a.1 a.2
  let mixcoeff := fun a : Σ y, F y => (law.weight a.1 : ℂ) * coeff a.1 a.2
  refine ⟨Fin (Fintype.card (Σ y, F y)), inferInstance, mixfreq ∘ e, mixcoeff ∘ e, ?_, ?_, ?_⟩
  · intro a j k hk t
    exact hfreq (e a).1 (e a).2 j k hk t
  · calc
      _ = ∑ a : Σ y, F y, ‖mixcoeff a‖ := e.sum_comp (fun a => ‖mixcoeff a‖)
      _ ≤ C := coefficientFourierMixture_mass_le law coeff hcoeff
  · intro z
    have heq : coefficientTorusFourierSum U (mixfreq ∘ e) (mixcoeff ∘ e) z =
        coefficientTorusFourierSum U mixfreq mixcoeff z :=
      e.sum_comp (fun a => mixcoeff a * coefficientTorusCharacter U (mixfreq a) z)
    rw [heq]
    exact coefficientFourierMixture_uniform_error U law frequency coeff g happ z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def coefficientSlotFrequency {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (frequency : ∀ s : CoefficientSlot K m, J s.1 → ℤ) :
    ∀ j, (K →₀ ℕ) → J j → ℤ := fun j d a =>
  if h : d.degree ≤ j.val + 1 then frequency ⟨j, ⟨d, h⟩⟩ a else 0

theorem coefficientSlotFrequency_apply {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (frequency : ∀ s : CoefficientSlot K m, J s.1 → ℤ)
    (s : CoefficientSlot K m) (a : J s.1) :
    coefficientSlotFrequency frequency s.1 s.2.val a = frequency s a := by
  simp only [coefficientSlotFrequency, dite_eq_left s.2.property]

theorem coefficientSlotFrequency_bound {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (frequency : ∀ s : CoefficientSlot K m, J s.1 → ℤ) {C : ℝ}
    (hfrequency : ∀ s a, |(frequency s a : ℝ)| ≤ C) :
    ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(coefficientSlotFrequency frequency j d a : ℝ)| ≤ C := by
  intro j d hd a
  simpa only [coefficientSlotFrequency, dite_eq_left hd] using hfrequency ⟨j, ⟨d, hd⟩⟩ a

theorem coefficientTorusCharacter_slot_product {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ s : CoefficientSlot K m, J s.1 → ℤ) (x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U (coefficientSlotFrequency frequency) x =
      ∏ s : CoefficientSlot K m, subspaceArrayCharacter (U s.1) (fun _ a => frequency s a)
        (coefficientCoordinateTorus U x s) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [coefficientTorusCharacter_mk]
  change CircleFourier.character ((∑ s : CoefficientSlot K m, ∑ a,
    (coefficientSlotFrequency frequency s.1 s.2.val a : ℝ) * (y s).val a : ℝ) :
      CircleFourier.Circle) = _
  simp only [coefficientSlotFrequency_apply]
  rw [character_real_sum]
  apply Finset.prod_congr rfl
  intro s _
  rw [coefficientCoordinateTorus_mk]
  change _ = CircleFourier.character
    ((∑ _u : Unit, ∑ a, (frequency s a : ℝ) * (y s).val a : ℝ) : CircleFourier.Circle)
  simp only [Fintype.sum_unique]

theorem coefficientTensorFourier_eq {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    {F : CoefficientSlot K m → Type*} [∀ s, Fintype (F s)]
    (frequency : ∀ s : CoefficientSlot K m, F s → J s.1 → ℤ) (c : ∀ s, F s → ℂ)
    (x : CoefficientTorus (K := K) U) :
    (∏ s : CoefficientSlot K m, ∑ a, c s a *
      subspaceArrayCharacter (U s.1) (fun _ t => frequency s a t) (coefficientCoordinateTorus U x s)) =
    coefficientTorusFourierSum U (fun a : ∀ s, F s => coefficientSlotFrequency (fun s => frequency s (a s)))
      (fun a => ∏ s, c s (a s)) x := by
  rw [finiteTensorExpansion c (fun s a y => subspaceArrayCharacter (U s.1) (fun _ t => frequency s a t) y)]
  simp only [coefficientTorusFourierSum, coefficientTorusCharacter_slot_product]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

def sitePullbackFrequency {K S : Type*} [Fintype S] {m : ℕ} {J : Fin m → Type*}
    (site : S → K → ℤ) (b : ∀ j, Matrix S (J j) ℤ) :
    ∀ j, (K →₀ ℕ) → J j → ℤ :=
  fun j d a => ∑ s, d.prod (fun k n => site s k ^ n) * b j s a

theorem sitePullbackFrequency_matrix {K S : Type*} [Fintype S] {m : ℕ}
    {J : Fin m → Type*} (site : S → K → ℤ) (b : ∀ j, Matrix S (J j) ℤ) (j : Fin m) :
    (fun (d : BoundedCoefficientExponent K (j.val + 1)) a => (sitePullbackFrequency site b j d.val a : ℝ)) =
      (Matrix.of (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)))ᵀ *
        Matrix.of (fun s a => (b j s a : ℝ)) := by
  funext d a
  simp only [sitePullbackFrequency, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, boundedSiteMatrix, Int.cast_sum, Int.cast_mul]

theorem coefficientArrayFunctional_sitePullback {K S : Type*} [Fintype K] [Fintype S]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ)
    (b : ∀ j, Matrix S (J j) ℤ) (x : CoefficientArray (K := K) U) :
    coefficientArrayFunctional U (sitePullbackFrequency site b) x =
      ∑ j, subspaceArrayFunctional (U j) (fun s a => (b j s a : ℝ))
        (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
          (coefficientLayerArray U j x)) := by
  change (∑ s : CoefficientSlot K m, ∑ a, (sitePullbackFrequency site b s.1 s.2.val a : ℝ) *
    (x s).val a) = _
  rw [show (∑ s : CoefficientSlot K m, ∑ a, (sitePullbackFrequency site b s.1 s.2.val a : ℝ) *
    (x s).val a) = ∑ j, ∑ d : BoundedCoefficientExponent K (j.val + 1), ∑ a,
      (sitePullbackFrequency site b j d.val a : ℝ) * (x ⟨j, d⟩).val a from Fintype.sum_sigma _]
  apply Finset.sum_congr rfl
  intro j _
  change subspaceArrayFunctional (U j) (fun d a => (sitePullbackFrequency site b j d.val a : ℝ))
    (coefficientLayerArray U j x) = _
  exact (congrArg (fun f => subspaceArrayFunctional (U j) f (coefficientLayerArray U j x))
    (sitePullbackFrequency_matrix site b j)).trans
      (subspaceArrayFunctional_matrix (U j)
        (Matrix.of (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)))
        (Matrix.of (fun s a => (b j s a : ℝ))) (coefficientLayerArray U j x)).symm

theorem coefficientTorusCharacter_sitePullback {K S : Type*} [Fintype K] [Fintype S]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ)
    (b : ∀ j, Matrix S (J j) ℤ) (x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U (sitePullbackFrequency site b) x =
      ∏ j, subspaceArrayCharacter (U j) (b j) (coefficientSiteTorusMap U site x j) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [coefficientTorusCharacter_mk, coefficientArrayFunctional_sitePullback, character_real_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [coefficientSiteTorusMap_mk, subspaceArrayCharacter_mk]

noncomputable def siteTorusFourierSum {S F : Type*} [Fintype S] [Fintype F]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (b : F → ∀ j, Matrix S (J j) ℤ) (c : F → ℂ)
    (x : SiteTorus S U) : ℂ := ∑ a, c a * ∏ j, subspaceArrayCharacter (U j) (b a j) (x j)

theorem siteTorusFourierSum_pullback {K S F : Type*} [Fintype K] [Fintype S] [Fintype F]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ)
    (b : F → ∀ j, Matrix S (J j) ℤ) (c : F → ℂ) (x : CoefficientTorus (K := K) U) :
    siteTorusFourierSum U b c (coefficientSiteTorusMap U site x) =
      coefficientTorusFourierSum U (fun a => sitePullbackFrequency site (b a)) c x := by
  simp only [siteTorusFourierSum, coefficientTorusFourierSum, coefficientTorusCharacter_sitePullback]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem coefficientTorusFourierSum_cover {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (q : ℕ) (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (x : CoefficientTorus (K := K) U) :
    coefficientTorusFourierSum U frequency c (quotientIntegerCover (coefficientIntegerLattice U) q x) =
      coefficientTorusFourierSum U (fun a => dilateCoefficientFrequency q (frequency a)) c x := by
  simp only [coefficientTorusFourierSum, coefficientTorusCharacter_cover]

theorem coefficientTorusFourierSum_cover_integral {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (q : ℕ) (hq : 0 < q) (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, coefficientTorusFourierSum U frequency c
      (quotientIntegerCover (coefficientIntegerLattice U) q x) ∂μ) =
        ∫ x, coefficientTorusFourierSum U frequency c x ∂μ := by
  simp_rw [coefficientTorusFourierSum_cover]
  rw [coefficientTorusFourierSum_integral, coefficientTorusFourierSum_integral]
  simp only [affineCoefficientModeTrivial_dilate_iff U q hq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem siteTorusFourierSum_pullback_integrable {K S F : Type*}
    [Fintype K] [Fintype S] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (b : F → ∀ j, Matrix S (J j) ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ] :
    Integrable (fun x => siteTorusFourierSum U b c (coefficientSiteTorusMap U site x)) μ := by
  have he : (fun x => siteTorusFourierSum U b c (coefficientSiteTorusMap U site x)) =
      coefficientTorusFourierSum U (fun a => sitePullbackFrequency site (b a)) c :=
    funext (siteTorusFourierSum_pullback U site b c)
  rw [he]
  exact coefficientTorusFourierSum_integrable U _ c μ

theorem siteTorusFourierSum_haar_mean {K S F : Type*}
    [Fintype K] [Fintype S] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (b : F → ∀ j, Matrix S (J j) ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, siteTorusFourierSum U b c (coefficientSiteTorusMap U site x) ∂μ) =
      ∑ a, if affineCoefficientModeTrivial U (sitePullbackFrequency site (b a)) then c a else 0 := by
  have he : (fun x => siteTorusFourierSum U b c (coefficientSiteTorusMap U site x)) =
      coefficientTorusFourierSum U (fun a => sitePullbackFrequency site (b a)) c :=
    funext (siteTorusFourierSum_pullback U site b c)
  rw [he]
  exact coefficientTorusFourierSum_integral U _ c μ

end Erdos3.VectorPolynomial

end

end OAI
