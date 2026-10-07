/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.LinearRestrictionDenominatorSize
import OAI.Combinatorics.Progressions.Estimates.LinearRestrictionHeight

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

omit [Fintype σ] in

theorem map_polynomialLinearRestriction_ratCast
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) :
    map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P) =
      eval₂Hom C (fun i => map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i))
        (map (algebraMap ℚ ℝ) P) :=
  map_eval₂ (algebraMap ℚ ℝ) (linearCoordinatePolynomial A) P

omit [Fintype σ] [Fintype τ] in

theorem polynomialDenominator_coefficientGrid (P : MvPolynomial σ ℚ) :
    (fun m => P.coeff m) ∈ denominatorGrid (polynomialDenominator P) := by
  classical
  refine ⟨fun m => if hm : m ∈ P.support then
    clearedArray (fun n : P.support => P.coeff n.val) ⟨m, hm⟩ else 0, ?_⟩
  intro m
  change (polynomialDenominator P : ℚ) * P.coeff m = _
  by_cases hm : m ∈ P.support
  · simp only [dite_eq_left hm]
    exact (clearedArray_cast (fun n : P.support => P.coeff n.val) ⟨m, hm⟩).symm
  · simp [hm, notMem_support_iff.mp hm]

theorem linearCoordinatePolynomial_realCoefficientGrid [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) :
    realPolynomialCoefficientGrid
      (matrixDenominator (fun i j => A (Pi.single j 1) i))
      (map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i)) := by
  classical
  let M : Matrix σ τ ℚ := fun i j => A (Pi.single j 1) i
  have hc (j : τ) : ((clearedMatrix M i j : ℤ) : ℝ) =
      (matrixDenominator M : ℝ) * (M i j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast M) i) j
    change ((clearedMatrix M i j : ℤ) : ℚ) = (matrixDenominator M : ℚ) * M i j at h
    exact_mod_cast h
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  refine ⟨∑ j, C (clearedMatrix M i j) * X j, ?_⟩
  simp only [linearCoordinatePolynomial, ← C_mul', map_sum, map_mul, map_C, map_X,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hcast (q : ℚ) : algebraMap ℚ ℝ q = (q : ℝ) := by norm_num
  simp only [hcast, Int.coe_castRingHom]
  rw [hc, map_mul, mul_assoc]
  simp only [M]
  congr 3
  apply congrArg (fun x : τ → ℚ => (A x i : ℝ))
  ext k
  simp [Pi.single_apply]

theorem polynomialLinearRestriction_denominatorGrid [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    (d : ℕ) (hd : P.totalDegree ≤ d) :
    (fun m => (polynomialLinearRestriction A P).coeff m) ∈
      denominatorGrid (polynomialDenominator P *
        matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d) := by
  apply (realPolynomialCoefficientGrid_ratCast_iff _ _).mp
  rw [map_polynomialLinearRestriction_ratCast]
  apply realPolynomialCoefficientGrid_substitute
  · apply le_trans (b := P.totalDegree) ?_ hd
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) P hm)
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr
      (polynomialDenominator_coefficientGrid P)
  · exact linearCoordinatePolynomial_realCoefficientGrid A

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

theorem rationalPolynomial_realMass_le {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) {K d : ℕ}
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) :
    realPolynomialMass (map (algebraMap ℚ ℝ) P) ≤
      ((Fintype.card σ + 1) ^ d * K : ℕ) := by
  classical
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support
    (support_map_subset (algebraMap ℚ ℝ) P)]
  have hc : P.support.card ≤ (Fintype.card σ + 1) ^ d :=
    boundedExponentSet_card_le P.support d (fun _ hm => (le_totalDegree hm).trans hd)
  calc
    _ ≤ ∑ _m ∈ P.support, (K : ℝ) := by
      apply Finset.sum_le_sum
      intro m _
      rw [coeff_map]
      exact (hP m).abs_real_le
    _ = (P.support.card : ℝ) * K := by simp
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_right K hc

theorem linearCoordinatePolynomial_realMass_le
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) {H : ℕ}
    (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H) (i : σ) :
    realPolynomialMass (map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i)) ≤
      (Fintype.card τ * H : ℕ) := by
  classical
  have hcast (q : ℚ) : algebraMap ℚ ℝ q = (q : ℝ) := by norm_num
  rw [linearCoordinatePolynomial, map_sum]
  simp only [← C_mul', map_mul, map_C, map_X, hcast]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : τ, (H : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      apply (realPolynomialMass_C_mul_le _ _).trans
      rw [realPolynomialMass_X, mul_one]
      convert (hA i j).abs_real_le using 1
      congr 3
      apply congrArg (fun coordinates : τ → ℚ => A coordinates i)
      ext index
      simp [Pi.single_apply]
    _ = _ := by simp

theorem polynomialLinearRestriction_realMass_le
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    {H K d : ℕ} (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H)
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) :
    realPolynomialMass (map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P)) ≤
      (((Fintype.card σ + 1) ^ d * K) * (Fintype.card τ * H + 1) ^ d : ℕ) := by
  have he : map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P) =
      eval₂Hom C (fun i => map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i))
        (map (algebraMap ℚ ℝ) P) := map_eval₂ _ _ _
  rw [he]
  have hd' : (map (algebraMap ℚ ℝ) P).totalDegree ≤ d := by
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact (le_totalDegree (support_map_subset (algebraMap ℚ ℝ) P hm)).trans hd
  have hmass := realPolynomialMass_substitution_le (map (algebraMap ℚ ℝ) P)
    (fun i => map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i))
    (M := (Fintype.card τ * H + 1 : ℕ)) (by exact_mod_cast Nat.le_add_left 1 _)
    (fun i => (linearCoordinatePolynomial_realMass_le A hA i).trans
      (by exact_mod_cast Nat.le_succ (Fintype.card τ * H))) hd'
  refine hmass.trans ?_
  simpa only [Nat.cast_mul, Nat.cast_pow] using mul_le_mul_of_nonneg_right
    (rationalPolynomial_realMass_le P hP hd)
    (pow_nonneg (Nat.cast_nonneg (Fintype.card τ * H + 1)) d)

theorem polynomialLinearRestriction_coeff_abs_le
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    {H K d : ℕ} (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H)
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) (m : τ →₀ ℕ) :
    |(((polynomialLinearRestriction A P).coeff m : ℚ) : ℝ)| ≤
      (((Fintype.card σ + 1) ^ d * K) * (Fintype.card τ * H + 1) ^ d : ℕ) := by
  have h := (realPolynomialMass_coeff_le
    (map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P)) m).trans
      (polynomialLinearRestriction_realMass_le A P hA hP hd)
  rw [coeff_map] at h
  exact h

theorem rationalHeightLE_of_integral_mul_of_abs_le (q : ℚ) {Q B D : ℕ}
    (hQ : 0 < Q) (hQD : Q ≤ D) (hB : 1 ≤ B)
    (hint : ∃ z : ℤ, (Q : ℚ) * q = z) (habs : |(q : ℝ)| ≤ B) :
    RationalHeightLE q (B * D) := by
  obtain ⟨z, hz⟩ := hint
  have hzR : (Q : ℝ) * (q : ℝ) = z := by exact_mod_cast hz
  have hzbound : z.natAbs ≤ B * D := by
    apply (Nat.cast_le (α := ℝ)).mp
    simp only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_mul]
    rw [← hzR, abs_mul, abs_of_nonneg (Nat.cast_nonneg Q)]
    exact (mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg Q)).trans
      (by nlinarith [show (Q : ℝ) ≤ D by exact_mod_cast hQD])
  have he : q = (z : ℚ) / (Q : ℤ) := by
    apply (eq_div_iff (by exact_mod_cast hQ.ne' : ((Q : ℤ) : ℚ) ≠ 0)).mpr
    simpa only [Int.cast_natCast, mul_comm] using hz
  rw [he]
  exact rationalHeightLE_fraction z Q (by exact_mod_cast hQ.ne') hzbound
    (by simpa only [Int.natAbs_natCast] using hQD.trans (Nat.le_mul_of_pos_left D hB))

theorem polynomialLinearRestriction_height
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    {H K d : ℕ} (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H)
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) :
    RationalPolynomialHeightLE (polynomialLinearRestriction A P)
      (linearRestrictionHeight (Fintype.card σ) (Fintype.card τ) d H K) := by
  have hK : 0 < K := hP.one_le
  have hmasspos : 1 ≤ ((Fintype.card σ + 1) ^ d * K) *
      (Fintype.card τ * H + 1) ^ d := by
    change 0 < ((Fintype.card σ + 1) ^ d * K) * (Fintype.card τ * H + 1) ^ d
    positivity
  obtain ⟨z, hz⟩ := polynomialLinearRestriction_denominatorGrid A P d hd
  intro m
  exact rationalHeightLE_of_integral_mul_of_abs_le _
    (polynomialLinearRestriction_denominator_pos A P d)
    (polynomialLinearRestriction_denominator_le A P hd hP hA)
    hmasspos ⟨z m, hz m⟩ (polynomialLinearRestriction_coeff_abs_le A P hA hP hd m)

theorem polynomialLinearRestriction_height_le
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    {H K d n m : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H)
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d)
    (hn : Fintype.card σ ≤ n) (hm : Fintype.card τ ≤ m) :
    RationalPolynomialHeightLE (polynomialLinearRestriction A P)
      (linearRestrictionHeight n m d H K) :=
  (polynomialLinearRestriction_height A P hA hP hd).mono
    (linearRestrictionHeight_mono hH hP.one_le hn hm le_rfl le_rfl)

end Erdos3

end

end OAI
