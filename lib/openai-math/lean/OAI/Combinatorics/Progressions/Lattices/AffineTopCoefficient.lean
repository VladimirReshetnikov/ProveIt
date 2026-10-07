import OAI.Combinatorics.Progressions.Geometry.TopSupportSubstitution
import OAI.Combinatorics.Progressions.Polynomial.AffineShiftPolynomial

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem affineShiftPullback_translate {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) (P : MvPolynomial I ℝ) :
    affineShiftPullback (fun _ => 0) direction (polynomialTranslate base P) =
      affineShiftPullback base direction P := by
  have he : (affineShiftPullback (fun _ => 0) direction).comp (polynomialTranslate base) =
      affineShiftPullback base direction := by
    apply algHom_ext
    intro i
    simp [AlgHom.comp_apply, polynomialTranslate_X, affineShiftPullback,
      affineShiftCoordinate, add_comm]
  exact AlgHom.congr_fun he P

theorem affineShift_full_coefficient_base {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) :
    (affineShiftPullback base direction P).coeff (fullShiftExponent n) =
      (affineShiftPullback (fun _ => 0) direction P).coeff (fullShiftExponent n) := by
  have hc (i : I) : affineShiftCoordinate (fun _ => 0) direction i ∈
      weightedSupportLE (1 : Fin n → ℕ) ((1 : I → ℕ) i) :=
    (mem_weightedSupportLE_one_iff _ 1).mpr (affineShiftCoordinate_degree _ _ _)
  have hp := (mem_weightedSupportLE_one_iff P n).mpr hP
  have ht := polynomialTranslate_sub_mem_weightedSupportLT base (1 : I → ℕ)
    (fun _ => by simp) hp
  have hl := weightedSupportLT_aeval (1 : I → ℕ) (1 : Fin n → ℕ)
    (affineShiftCoordinate (fun _ => 0) direction) hc ht
  have hz := full_coefficient_zero_of_lower_support hl
  change (affineShiftPullback (fun _ => 0) direction (polynomialTranslate base P - P)).coeff
    (fullShiftExponent n) = 0 at hz
  rw [map_sub, coeff_sub, affineShiftPullback_translate] at hz
  exact sub_eq_zero.mp hz

theorem sub_topComponent_mem_lowerSupport {I R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n) :
    P - homogeneousComponent n P ∈ weightedSupportLT (1 : I → ℕ) n := by
  intro a ha
  change Finsupp.weight (1 : I → ℕ) a < n
  have hne : (P - homogeneousComponent n P).coeff a ≠ 0 := mem_support_iff.mp ha
  simp only [coeff_sub, coeff_homogeneousComponent] at hne
  by_cases hd : a.degree = n
  · simp only [hd, ite_true, sub_self, ne_eq, not_true_eq_false] at hne
  · have haP : P.coeff a ≠ 0 := by
      intro hz
      simp only [hz, hd, ite_false, sub_self, ne_eq, not_true_eq_false] at hne
    have hle : Finsupp.weight (1 : I → ℕ) a ≤ n :=
      (mem_weightedSupportLE_one_iff P n).mpr hP (mem_support_iff.mpr haP)
    have hn : Finsupp.weight (1 : I → ℕ) a ≠ n := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
    omega

theorem affineShift_full_coefficient_top {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) :
    (affineShiftPullback base direction P).coeff (fullShiftExponent n) =
      (affineShiftPullback base direction (homogeneousComponent n P)).coeff (fullShiftExponent n) := by
  have hc (i : I) : affineShiftCoordinate base direction i ∈
      weightedSupportLE (1 : Fin n → ℕ) ((1 : I → ℕ) i) :=
    (mem_weightedSupportLE_one_iff _ 1).mpr (affineShiftCoordinate_degree _ _ _)
  have hl := weightedSupportLT_aeval (1 : I → ℕ) (1 : Fin n → ℕ)
    (affineShiftCoordinate base direction) hc (sub_topComponent_mem_lowerSupport P hP)
  have hz := full_coefficient_zero_of_lower_support hl
  change (affineShiftPullback base direction (P - homogeneousComponent n P)).coeff
    (fullShiftExponent n) = 0 at hz
  rw [map_sub, coeff_sub] at hz
  exact sub_eq_zero.mp hz

noncomputable def polynomialTopSymbol {I : Type*} (n : ℕ) (P : MvPolynomial I ℝ)
    (direction : Fin n → I → ℝ) : ℝ :=
  (affineShiftPullback (fun _ => 0) direction (homogeneousComponent n P)).coeff (fullShiftExponent n)

theorem affineShift_difference_eq_topSymbol {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) (u v : Fin n → ℝ) :
    additiveBoxDifference n
      (fun t (_ : Unit) => eval (fun i => base i + ∑ j, direction j i * t j) P) u v () =
      polynomialTopSymbol n P direction * ∏ i, (u i - v i) := by
  rw [affineShift_full_difference base direction P hP,
    affineShift_full_coefficient_base base direction P hP,
    affineShift_full_coefficient_top (fun _ => 0) direction P hP]
  rfl

end Erdos3

end

end OAI
