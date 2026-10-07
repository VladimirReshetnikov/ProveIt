/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.GaussianTailRadius
import OAI.Combinatorics.Progressions.Fourier.AffineTorusDensityIncrement
import OAI.Combinatorics.Progressions.Lattices.IntegerIntervalReindex
import OAI.Combinatorics.Progressions.Lattices.IntegerIntervalShift
import OAI.Combinatorics.Progressions.Polynomial.WeylStepScales

namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem norm_linear_interval_sum (u v : ℤ) (a b : ℝ) :
    ‖∑ x ∈ Finset.Ico u v,
      character (((x : ℝ) * a + b : ℝ) : CircleFourier.Circle)‖ =
      ‖geometricCharacterSum (v - u).toNat (a : CircleFourier.Circle)‖ := by
  rw [sum_integerInterval_eq_range]
  have heq (n : ℕ) :
      character ((((u + (n : ℤ) : ℤ) : ℝ) * a + b : ℝ) : CircleFourier.Circle) =
        character (((u : ℝ) * a + b : ℝ) : CircleFourier.Circle) *
          character (n • (a : CircleFourier.Circle)) := by
    have hr : ((u + (n : ℤ) : ℤ) : ℝ) * a + b = (u : ℝ) * a + b + n • a := by
      simp only [Int.cast_add, Int.cast_natCast, nsmul_eq_mul]
      ring
    rw [hr, AddCircle.coe_add, AddCircle.coe_nsmul, character_add]
  simp_rw [heq]
  rw [← Finset.mul_sum, norm_mul, norm_character, one_mul]
  rfl

theorem linear_interval_inverse (u v : ℤ) (a b : ℝ) {S : ℝ} (hS : 0 < S)
    (hlarge : S ≤ ‖∑ x ∈ Finset.Ico u v,
      character (((x : ℝ) * a + b : ℝ) : CircleFourier.Circle)‖) :
    integerDistance (a : CircleFourier.Circle) ≤ 1 / (2 * S) := by
  rw [norm_linear_interval_sum] at hlarge
  have h := two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one
    (v - u).toNat (a : CircleFourier.Circle)
  have hmul := mul_le_mul_of_nonneg_left hlarge
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (integerDistance_nonneg (a : CircleFourier.Circle)))
  apply (le_div_iff₀ (by positivity : 0 < 2 * S)).mpr
  nlinarith only [h, hmul]

theorem polynomial_linear_eval (P : Polynomial ℝ) (hP : P.natDegree ≤ 1) (x : ℝ) :
    P.eval x = x * P.coeff 1 + P.coeff 0 := by
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hP]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem linear_polynomial_interval_inverse (P : Polynomial ℝ) (hP : P.natDegree ≤ 1)
    (u v : ℤ) {S : ℝ} (hS : 0 < S)
    (hlarge : S ≤ ‖∑ x ∈ Finset.Ico u v,
      character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖) :
    integerDistance (P.coeff 1 : CircleFourier.Circle) ≤ 1 / (2 * S) := by
  simp_rw [polynomial_linear_eval P hP] at hlarge
  exact linear_interval_inverse u v (P.coeff 1) (P.coeff 0) hS hlarge

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped NNReal

theorem affine_comp_top_coeff (P : Polynomial ℝ) {k : ℕ} (hP : P.natDegree ≤ k)
    (a q : ℝ) (hq : q ≠ 0) :
    (P.comp (C q * X + C a)).coeff k = P.coeff k * q ^ k := by
  have hdeg : (P.comp (C q * X + C a)).natDegree = P.natDegree := by
    rw [natDegree_comp, natDegree_linear hq, mul_one]
  by_cases heq : P.natDegree = k
  · have hc := coeff_comp_degree_mul_degree (p := P) (q := C q * X + C a)
      (by rw [natDegree_linear hq]; decide)
    rw [natDegree_linear hq, mul_one, leadingCoeff_linear hq, heq] at hc
    simpa only [Polynomial.leadingCoeff, heq] using hc
  · have hlt : P.natDegree < k := lt_of_le_of_ne hP heq
    rw [coeff_eq_zero_of_natDegree_lt (hdeg ▸ hlt),
      coeff_eq_zero_of_natDegree_lt hlt, zero_mul]

noncomputable def affinePhaseRemainder (P : Polynomial ℝ) (k : ℕ) (a q : ℝ) :
    Polynomial ℝ := (P.comp (C q * X + C a)).erase k

theorem affinePhaseRemainder_degree (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k + 1) (a q : ℝ) (hq : q ≠ 0) :
    (affinePhaseRemainder P (k + 1) a q).natDegree ≤ k := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases heq : n = k + 1
  · simp [affinePhaseRemainder, heq]
  · rw [affinePhaseRemainder, erase_ne _ heq]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_comp, natDegree_linear hq, mul_one]
    omega

theorem affinePhaseRemainder_eval (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k) (a q x : ℝ) (hq : q ≠ 0) :
    P.eval (a + q * x) = (affinePhaseRemainder P k a q).eval x +
      (P.coeff k * q ^ k) * x ^ k := by
  have heq := congrArg (fun Q : Polynomial ℝ => Q.eval x)
    (monomial_add_erase (P.comp (C q * X + C a)) k)
  rw [eval_add, eval_monomial, affine_comp_top_coeff P hP a q hq] at heq
  simpa only [affinePhaseRemainder, eval_comp, eval_add, eval_mul, eval_C, eval_X,
    add_comm (q * x) a, add_comm] using heq.symm

theorem affinePhaseRemainder_error (P : Polynomial ℝ) {k H : ℕ}
    (hP : P.natDegree ≤ k) (a q : ℝ) (hq : q ≠ 0) (m : ℤ) {τ : ℝ}
    (hτ : 0 ≤ τ) (happrox : |P.coeff k * q ^ k - m| ≤ τ)
    {j : ℕ} (hj : j < H) :
    |P.eval (a + q * j) -
      ((affinePhaseRemainder P k a q).eval (j : ℝ) + ((m * (j : ℤ) ^ k : ℤ) : ℝ))| ≤
      τ * (H : ℝ) ^ k := by
  have hjR : (j : ℝ) ≤ H := by exact_mod_cast hj.le
  calc
    _ = |(P.coeff k * q ^ k - m) * (j : ℝ) ^ k| := by
      rw [affinePhaseRemainder_eval P hP a q j hq]
      push_cast
      congr 1
      ring
    _ = |P.coeff k * q ^ k - m| * (j : ℝ) ^ k := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) k)]
    _ ≤ τ * (H : ℝ) ^ k :=
      mul_le_mul happrox (pow_le_pow_left₀ (Nat.cast_nonneg _) hjR k)
        (pow_nonneg (Nat.cast_nonneg _) _) hτ

theorem polynomial_torus_degree_reduction {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℝ) {k H : ℕ} (hP : ∀ i, (P i).natDegree ≤ k + 1)
    (a q : ℝ) (hq : q ≠ 0) (m : ι → ℤ) {τ : ℝ} (hτ : 0 ≤ τ)
    (happrox : ∀ i, |(P i).coeff (k + 1) * q ^ (k + 1) - m i| ≤ τ)
    {F : (ι → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hperiod : ∀ x : ι → ℝ, ∀ m : ι → ℤ, F (fun i => x i + m i) = F x) :
    ∃ R : ι → Polynomial ℝ, (∀ i, (R i).natDegree ≤ k) ∧
      ∀ j < H, dist (F (fun i => (P i).eval (a + q * j)))
        (F (fun i => (R i).eval (j : ℝ))) ≤ L * (τ * (H : ℝ) ^ (k + 1)) := by
  refine ⟨fun i => affinePhaseRemainder (P i) (k + 1) a q,
    fun i => affinePhaseRemainder_degree (P i) (hP i) a q hq, ?_⟩
  intro j hj
  apply periodic_lipschitz_dist_le_of_integer_approx hF hperiod
    _ _ (fun i => m i * (j : ℤ) ^ (k + 1)) (mul_nonneg hτ (by positivity))
  intro i
  exact affinePhaseRemainder_error (P i) (hP i) a q hq (m i) hτ (happrox i) hj

end Erdos3

end

section

namespace Erdos3

open Polynomial

noncomputable def polynomialShiftDifference (P : Polynomial ℝ) (h : ℝ) : Polynomial ℝ :=
  P - P.comp (X + C h)

theorem polynomialShiftDifference_eval (P : Polynomial ℝ) (h x : ℝ) :
    (polynomialShiftDifference P h).eval x = P.eval x - P.eval (x + h) := by
  simp only [polynomialShiftDifference, eval_sub, eval_comp, eval_add, eval_X, eval_C]

theorem polynomialShiftDifference_degree (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k + 1) (h : ℝ) :
    (polynomialShiftDifference P h).natDegree ≤ k := by
  have htop : (P.comp (X + C h)).coeff (k + 1) = P.coeff (k + 1) := by
    simpa only [C_1, one_mul, one_pow, mul_one] using
      affine_comp_top_coeff P hP h 1 one_ne_zero
  have hdeg : (P.comp (X + C h)).natDegree = P.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [polynomialShiftDifference, coeff_sub]
  by_cases heq : n = k + 1
  · rw [heq, htop, sub_self]
  · have hlt : P.natDegree < n := by omega
    rw [coeff_eq_zero_of_natDegree_lt hlt,
      coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hlt), sub_self]

theorem affine_shift_next_coeff (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k + 1) (h : ℝ) :
    (P.comp (X + C h)).coeff k = P.coeff k + (k + 1 : ℝ) * h * P.coeff (k + 1) := by
  have hD : (hasseDeriv k P).natDegree ≤ 1 := by
    apply (natDegree_hasseDeriv_le P k).trans
    omega
  rw [← taylor_apply, taylor_coeff]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hD]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff, zero_add,
    Nat.choose_self, Nat.cast_one, one_mul]
  rw [Nat.add_comm 1 k, Nat.choose_succ_self_right]
  push_cast
  ring

theorem polynomialShiftDifference_top_coeff (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k + 1) (h : ℝ) :
    (polynomialShiftDifference P h).coeff k = -(k + 1 : ℝ) * h * P.coeff (k + 1) := by
  rw [polynomialShiftDifference, coeff_sub, affine_shift_next_coeff P hP h]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def intervalPolynomialPhase (N : ℕ) (P : Polynomial ℝ) (x : ℤ) : ℂ :=
  if x ∈ Finset.Ico (0 : ℤ) (N : ℤ) then character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle) else 0

theorem intervalPolynomialPhase_support (N : ℕ) (P : Polynomial ℝ) (x : ℤ)
    (hx : x ∉ Finset.Ico (0 : ℤ) (N : ℤ)) : intervalPolynomialPhase N P x = 0 := by
  simp only [intervalPolynomialPhase, ite_eq_right hx]

theorem intervalPolynomialPhase_norm_le (N : ℕ) (P : Polynomial ℝ) (x : ℤ) :
    ‖intervalPolynomialPhase N P x‖ ≤ 1 := by
  unfold intervalPolynomialPhase
  split_ifs <;> simp only [norm_character, norm_zero, le_refl, zero_le_one]

theorem intervalPolynomialPhase_sum (N : ℕ) (P : Polynomial ℝ) :
    (∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), intervalPolynomialPhase N P x) =
      ∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle) := by
  apply Finset.sum_congr rfl
  intro x hx
  simp only [intervalPolynomialPhase, ite_eq_left hx]

theorem integerInterval_overlap (N : ℕ) (h : ℤ) :
    (Finset.Ico (0 : ℤ) (N : ℤ)).filter (fun x => x + h ∈ Finset.Ico (0 : ℤ) (N : ℤ)) =
      Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ico, max_le_iff, lt_min_iff]
  omega

theorem intervalPolynomialPhase_correlation (N : ℕ) (P : Polynomial ℝ) (h : ℤ) :
    shiftCorrelation (Finset.Ico (0 : ℤ) (N : ℤ)) (intervalPolynomialPhase N P) h =
      ∑ x ∈ Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h)),
        character (((polynomialShiftDifference P (h : ℝ)).eval (x : ℝ) : ℝ) : CircleFourier.Circle) := by
  rw [← integerInterval_overlap, Finset.sum_filter]
  unfold shiftCorrelation
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxh : x + h ∈ Finset.Ico (0 : ℤ) (N : ℤ)
  · simp only [intervalPolynomialPhase, ite_eq_left hx, ite_eq_left hxh,
      polynomialShiftDifference_eval, Int.cast_add]
    rw [AddCircle.coe_sub, sub_eq_add_neg, character_add, character_neg]
  · simp only [intervalPolynomialPhase, ite_eq_left hx, ite_eq_right hxh,
      star_zero, mul_zero]

theorem integerInterval_overlap_card_lower (N H : ℕ) (h : ℤ)
    (hh : |h| < (H : ℤ)) :
    N - H ≤ (Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h))).card := by
  simp only [Int.card_Ico]
  have hbounds := abs_lt.mp hh
  omega

theorem polynomial_weyl_step (P : Polynomial ℝ) {k N H : ℕ}
    (hP : P.natDegree ≤ k + 1) (hN : 0 < N) (hH : H ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * H)
    (hscore : δ * N ≤ ‖∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖) :
    ∃ (h : ℤ) (R : Polynomial ℝ), h ≠ 0 ∧ |h| < (H : ℤ) ∧ R.natDegree ≤ k ∧
      R.coeff k = -(k + 1 : ℝ) * (h : ℝ) * P.coeff (k + 1) ∧
      N - H ≤ (Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h))).card ∧
      δ ^ 2 * N / 4 ≤ ‖∑ x ∈ Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h)),
        character ((R.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖ := by
  obtain ⟨h, hh, hbound, hcorr⟩ := exists_large_interval_shift (intervalPolynomialPhase N P)
    hN hH (intervalPolynomialPhase_support N P)
    (fun x _ => intervalPolynomialPhase_norm_le N P x) hδ hshift
    (by rwa [intervalPolynomialPhase_sum])
  refine ⟨h, polynomialShiftDifference P (h : ℝ), hh, hbound,
    polynomialShiftDifference_degree P hP (h : ℝ),
    polynomialShiftDifference_top_coeff P hP (h : ℝ),
    integerInterval_overlap_card_lower N H h hbound, ?_⟩
  rwa [intervalPolynomialPhase_correlation] at hcorr

theorem many_polynomial_weyl_shifts (P : Polynomial ℝ) {k N H : ℕ}
    (hP : P.natDegree ≤ k + 1) (hN : 0 < N) (hH : H ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * H)
    (hscore : δ * N ≤ ‖∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖) :
    ∃ D : Finset ℤ, δ ^ 2 * H / 8 ≤ (D.card : ℝ) ∧
      ∀ h ∈ D, h ≠ 0 ∧ |h| < (H : ℤ) ∧
        ∃ R : Polynomial ℝ, R.natDegree ≤ k ∧
          R.coeff k = -(k + 1 : ℝ) * (h : ℝ) * P.coeff (k + 1) ∧
          N - H ≤ (Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h))).card ∧
          δ ^ 2 * N / 8 ≤ ‖∑ x ∈ Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h)),
            character ((R.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖ := by
  obtain ⟨D, hD, hgood⟩ := many_large_interval_shifts (intervalPolynomialPhase N P)
    hN hH (intervalPolynomialPhase_support N P)
    (fun x _ => intervalPolynomialPhase_norm_le N P x) hδ hshift
    (by rwa [intervalPolynomialPhase_sum])
  refine ⟨D, hD, ?_⟩
  intro h hh
  obtain ⟨hne, hbound, hcorr⟩ := hgood h hh
  refine ⟨hne, hbound, polynomialShiftDifference P (h : ℝ),
    polynomialShiftDifference_degree P hP (h : ℝ),
    polynomialShiftDifference_top_coeff P hP (h : ℝ),
    integerInterval_overlap_card_lower N H h hbound, ?_⟩
  rwa [intervalPolynomialPhase_correlation] at hcorr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open Polynomial CircleFourier

theorem polynomial_translate_degree (P : Polynomial ℝ) (u : ℝ) :
    (P.comp (X + C u)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

theorem polynomial_translate_top_coeff (P : Polynomial ℝ) {k : ℕ}
    (hP : P.natDegree ≤ k) (u : ℝ) :
    (P.comp (X + C u)).coeff k = P.coeff k := by
  simpa only [C_1, one_mul, one_pow, mul_one] using affine_comp_top_coeff P hP u 1 one_ne_zero

theorem polynomial_interval_sum_translate (P : Polynomial ℝ) (u v : ℤ) :
    (∑ x ∈ Finset.Ico u v, character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)) =
      ∑ x ∈ Finset.Ico (0 : ℤ) ((v - u).toNat : ℤ),
        character (((P.comp (X + C (u : ℝ))).eval (x : ℝ) : ℝ) : CircleFourier.Circle) := by
  rw [sum_integerInterval_eq_range, sum_integerInterval_eq_range]
  simp only [sub_zero, Int.toNat_natCast, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Int.cast_add, Int.cast_natCast, eval_comp, eval_add, eval_X, eval_C]
  rw [add_comm (n : ℝ) (u : ℝ)]

theorem integerInterval_overlap_length (N : ℕ) (h : ℤ) :
    (Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h))).card =
      (min (N : ℤ) ((N : ℤ) - h) - max 0 (-h)).toNat := Int.card_Ico _ _

theorem integerInterval_overlap_card_le (N : ℕ) (h : ℤ) :
    (Finset.Ico (max 0 (-h)) (min (N : ℤ) ((N : ℤ) - h))).card ≤ N := by
  rw [← integerInterval_overlap]
  have hh := Finset.card_filter_le (Finset.Ico (0 : ℤ) (N : ℤ))
    (fun x => x + h ∈ Finset.Ico (0 : ℤ) (N : ℤ))
  simpa only [Int.card_Ico, sub_zero, Int.toNat_natCast] using hh

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem quadratic_weyl_many_multiples (P : Polynomial ℝ) {N H : ℕ}
    (hP : P.natDegree ≤ 2) (hN : 0 < N) (hH : H ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * H)
    (hscore : δ * N ≤ ‖∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖) :
    ∃ D : Finset ℤ, δ ^ 2 * H / 8 ≤ (D.card : ℝ) ∧
      ∀ h ∈ D, h ≠ 0 ∧ |h| < (H : ℤ) ∧
        |2 * (h : ℝ) * P.coeff 2 - round (2 * (h : ℝ) * P.coeff 2)| ≤
          4 / (δ ^ 2 * N) := by
  obtain ⟨D, hD, hgood⟩ := many_polynomial_weyl_shifts P (k := 1) hP hN hH hδ hshift hscore
  refine ⟨D, hD, ?_⟩
  intro h hh
  obtain ⟨hne, hbound, R, hR, hcoeff, _, hlarge⟩ := hgood h hh
  refine ⟨hne, hbound, ?_⟩
  have hpos : (0 : ℝ) < δ ^ 2 * N := mul_pos (sq_pos_of_pos hδ) (Nat.cast_pos.mpr hN)
  have happrox := linear_polynomial_interval_inverse R hR _ _ (div_pos hpos (by norm_num)) hlarge
  have hcoeff' : R.coeff 1 = -(2 * (h : ℝ) * P.coeff 2) := by
    rw [hcoeff]
    ring
  rw [hcoeff', AddCircle.coe_neg, integerDistance_neg, integerDistance_coe] at happrox
  convert happrox using 1
  field_simp
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def polynomialExponentialSum (P : Polynomial ℝ) (N : ℕ) : ℂ :=
  ∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)

def LeadingWeylBound (k B K : ℕ) : Prop :=
  ∀ (P : Polynomial ℝ), P.natDegree ≤ k → ∀ N : ℕ, 0 < N → K ≤ N →
    (N : ℝ) / B ≤ ‖polynomialExponentialSum P N‖ →
    ∃ q : ℕ, 0 < q ∧ q ≤ K ∧ ∃ p : ℤ,
      |(q : ℝ) * P.coeff k - p| ≤ (K : ℝ) / (N : ℝ) ^ k

theorem leadingWeylBound_one {B : ℕ} (hB : 1 ≤ B) : LeadingWeylBound 1 B B := by
  intro P hP N hN hBN hscore
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h := linear_polynomial_interval_inverse P hP 0 N (div_pos hNR hBR) hscore
  rw [integerDistance_coe] at h
  refine ⟨1, by decide, hB, round (P.coeff 1), ?_⟩
  simp only [Nat.cast_one, one_mul, pow_one]
  calc
    _ ≤ 1 / (2 * ((N : ℝ) / B)) := h
    _ = (B : ℝ) / (2 * N) := by field_simp
    _ ≤ (B : ℝ) / N := div_le_div_of_nonneg_left hBR.le hNR (by linarith)

theorem LeadingWeylBound.on_integer_interval {k B K : ℕ} (hbound : LeadingWeylBound k B K)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ k) (u v : ℤ)
    (hM : 0 < (v - u).toNat) (hKM : K ≤ (v - u).toNat)
    (hscore : ((v - u).toNat : ℝ) / B ≤
      ‖∑ x ∈ Finset.Ico u v, character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ K ∧ ∃ p : ℤ,
      |(q : ℝ) * P.coeff k - p| ≤ (K : ℝ) / ((v - u).toNat : ℝ) ^ k := by
  rw [polynomial_interval_sum_translate] at hscore
  obtain ⟨q, hq, hqK, p, hp⟩ := hbound (P.comp (Polynomial.X + Polynomial.C (u : ℝ)))
    (by rwa [polynomial_translate_degree]) (v - u).toNat hM hKM hscore
  rw [polynomial_translate_top_coeff P hP] at hp
  exact ⟨q, hq, hqK, p, hp⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem quadratic_weyl_inverse_with_denominator_scale (P : Polynomial ℝ) {N Q : ℕ}
    (hP : P.natDegree ≤ 2) (hN : 0 < N) (hQ : 0 < Q)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hQsize : 32 ≤ δ ^ 2 * Q) (hNsize : 512 * Q ≤ δ ^ 4 * N)
    (hscore : δ * N ≤ ‖∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2 * Q ∧ ∃ p : ℤ,
      |(q : ℝ) * P.coeff 2 - p| ≤ 768 * Q / (δ ^ 4 * (N : ℝ) ^ 2) := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hδsqone : δ ^ 2 ≤ 1 := by nlinarith
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hden : 0 < δ ^ 2 * N := mul_pos hδsq hNR
  have hNH : 32 ≤ δ ^ 2 * N := by
    have hpower : δ ^ 4 ≤ δ ^ 2 := by nlinarith [sq_nonneg (δ ^ 2 - 1)]
    have hh := mul_le_mul_of_nonneg_right hpower hNR.le
    nlinarith only [hNsize, hQR, hh]
  obtain ⟨D, hD, hgood⟩ := quadratic_weyl_many_multiples P hP hN le_rfl hδ
    (by linarith only [hNH]) hscore
  have hfrac : (Q : ℝ) * (4 / (δ ^ 2 * N)) ≤ δ ^ 2 / 128 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hNsize]
  have hsmall : 16 * ((Q : ℝ) * (4 / (δ ^ 2 * N))) ≤ δ ^ 2 / 8 := by
    linarith only [hfrac]
  have hcap : (Q : ℝ) * (4 / (δ ^ 2 * N)) ≤ 1 := by
    linarith only [hfrac, hδsqone]
  have hclose : ∀ h ∈ D,
      |(h : ℝ) * (2 * P.coeff 2) - round ((h : ℝ) * (2 * P.coeff 2))| ≤
        4 / (δ ^ 2 * N) := by
    intro h hh
    have hid : (h : ℝ) * (2 * P.coeff 2) = 2 * (h : ℝ) * P.coeff 2 := by ring
    rw [hid]
    exact (hgood h hh).2.2
  obtain ⟨q, hq, hqQ, p, happrox⟩ := many_multiples_rational_approximation D
    (fun h => round ((h : ℝ) * (2 * P.coeff 2))) hN hQ
    (div_pos hδsq (by norm_num)) (div_nonneg (by norm_num) hden.le)
    (by nlinarith only [hQsize]) (by nlinarith only [hNH]) hsmall hcap
    (by convert hD using 1; ring) (fun h hh => (hgood h hh).2.1.le) hclose
  refine ⟨2 * q, by omega, by omega, p, ?_⟩
  have hlhs : ((2 * q : ℕ) : ℝ) * P.coeff 2 = (q : ℝ) * (2 * P.coeff 2) := by
    push_cast
    ring
  have hrhs : 24 * (Q : ℝ) * (4 / (δ ^ 2 * N)) / ((δ ^ 2 / 8) * N) =
      768 * Q / (δ ^ 4 * (N : ℝ) ^ 2) := by
    field_simp
    ring
  rw [hlhs, ← hrhs]
  exact happrox

theorem quadratic_weyl_inverse (P : Polynomial ℝ) {N : ℕ}
    (hP : P.natDegree ≤ 2) (hN : 0 < N)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hNsize : 32768 ≤ δ ^ 6 * N)
    (hscore : δ * N ≤ ‖∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 66 / δ ^ 2 ∧ ∃ p : ℤ,
      |(q : ℝ) * P.coeff 2 - p| ≤ 25344 / (δ ^ 6 * (N : ℝ) ^ 2) := by
  let Q := ⌈32 / δ ^ 2⌉₊
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hδsqone : δ ^ 2 ≤ 1 := by nlinarith
  have hQ : 0 < Q := Nat.ceil_pos.mpr (div_pos (by norm_num) hδsq)
  have hQsize : 32 ≤ δ ^ 2 * Q := by
    have h := (div_le_iff₀ hδsq).mp (Nat.le_ceil (32 / δ ^ 2))
    simpa only [mul_comm] using h
  have hQbound : (Q : ℝ) * δ ^ 2 ≤ 33 := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 32 / δ ^ 2 by positivity)
    have hm := mul_lt_mul_of_pos_right hc hδsq
    have hid : (32 / δ ^ 2 + 1) * δ ^ 2 = 32 + δ ^ 2 := by
      field_simp
    rw [hid] at hm
    change (Q : ℝ) * δ ^ 2 < 32 + δ ^ 2 at hm
    linarith only [hm, hδsqone]
  have hsize : 512 * (Q : ℝ) ≤ δ ^ 4 * N := by
    apply (mul_le_mul_iff_left₀ hδsq).mp
    nlinarith only [hNsize, hQbound]
  obtain ⟨q, hq, hqQ, p, happrox⟩ := quadratic_weyl_inverse_with_denominator_scale
    P hP hN hQ hδ hδone hQsize hsize hscore
  refine ⟨q, hq, ?_, p, happrox.trans ?_⟩
  · apply (le_div_iff₀ hδsq).mpr
    have hqQ' : (q : ℝ) ≤ 2 * Q := by exact_mod_cast hqQ
    have hm := mul_le_mul_of_nonneg_right hqQ' hδsq.le
    nlinarith only [hm, hQbound]
  · have hid : 768 * (Q : ℝ) / (δ ^ 4 * (N : ℝ) ^ 2) =
        (768 * ((Q : ℝ) * δ ^ 2)) / (δ ^ 6 * (N : ℝ) ^ 2) := by
      field_simp
    rw [hid]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [hQbound]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem LeadingWeylBound.step {k B K : ℕ} (hk : 0 < k) (hB : 2 ≤ B) (hK : 0 < K)
    (ih : LeadingWeylBound k (8 * B ^ 2) K) :
    LeadingWeylBound (k + 1) B (weylNextBudget k B K) := by
  classical
  intro P hP N hN hbudget hscore
  obtain ⟨hb₁, hb₂, hb₃, hb₄, hb₅, hb₆⟩ := weylNextBudget_bounds k B K
  have h₂K := hb₁.trans hbudget
  have h₃₂ := hb₂.trans hbudget
  have hQbound := hb₃.trans hbudget
  have hsmallbound := hb₄.trans hbudget
  have hBpos : 0 < B := by omega
  have hBsq : 0 < B ^ 2 := pow_pos hBpos 2
  have hN₂ : 2 ≤ N := by omega
  have hBR : (0 : ℝ) < B := Nat.cast_pos.mpr hBpos
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hδ : 0 < 1 / (B : ℝ) := one_div_pos.mpr hBR
  have hshift : 8 ≤ (1 / (B : ℝ)) ^ 2 * (N / 2 : ℕ) := by
    have hh : 8 * B ^ 2 ≤ N / 2 := by omega
    have hhR : (8 : ℝ) * (B : ℝ) ^ 2 ≤ (N / 2 : ℕ) := by exact_mod_cast hh
    calc
      8 ≤ (N / 2 : ℕ) / (B : ℝ) ^ 2 := (le_div_iff₀ (by positivity)).mpr hhR
      _ = (1 / (B : ℝ)) ^ 2 * (N / 2 : ℕ) := by field_simp
  have hscore' : (1 / (B : ℝ)) * N ≤ ‖polynomialExponentialSum P N‖ := by
    have hid : (1 / (B : ℝ)) * N = (N : ℝ) / B := by ring
    rwa [hid]
  obtain ⟨D, hDsize, hDgood⟩ := many_polynomial_weyl_shifts P hP hN (Nat.div_le_self N 2)
    hδ hshift hscore'
  let α : ℝ := -(k + 1 : ℝ) * P.coeff (k + 1)
  have hchoice : ∀ h : ℤ, ∃ (q : ℕ) (p : ℤ), (0 < q ∧ q ≤ K) ∧
      (h ∈ D → |(q : ℝ) * ((h : ℝ) * α) - p| ≤ weylShiftError k N K) := by
    intro h
    by_cases hh : h ∈ D
    · obtain ⟨hne, hshort, R, hR, hcoeff, hlength, hlarge⟩ := hDgood h hh
      let u := max 0 (-h)
      let v := min (N : ℤ) ((N : ℤ) - h)
      let M := (v - u).toNat
      have hML : N - N / 2 ≤ M := by
        simpa only [Int.card_Ico] using hlength
      have hKM : K ≤ M := by omega
      have hM : 0 < M := lt_of_lt_of_le hK hKM
      have hMN : M ≤ N := by
        simpa only [Int.card_Ico] using integerInterval_overlap_card_le N h
      have hMbias : (M : ℝ) / (8 * B ^ 2 : ℕ) ≤
          ‖∑ x ∈ Finset.Ico u v, character ((R.eval (x : ℝ) : ℝ) : CircleFourier.Circle)‖ := by
        calc
          _ ≤ (N : ℝ) / (8 * B ^ 2 : ℕ) :=
            div_le_div_of_nonneg_right (Nat.cast_le.mpr hMN) (by positivity)
          _ = (1 / (B : ℝ)) ^ 2 * N / 8 := by push_cast; field_simp
          _ ≤ _ := hlarge
      obtain ⟨q, hq, hqK, p, hp⟩ := ih.on_integer_interval R hR u v hM hKM hMbias
      refine ⟨q, p, ⟨hq, hqK⟩, fun _ => ?_⟩
      have hid : R.coeff k = (h : ℝ) * α := by rw [hcoeff]; dsimp [α]; ring
      rw [hid] at hp
      exact hp.trans (weylShiftError_of_half_length hM hN (by omega))
    · exact ⟨1, 0, ⟨by decide, hK⟩, fun hd => (hh hd).elim⟩
  choose q p hq hp using hchoice
  have hsmall := weylShiftError_small hk hBpos hK hN hsmallbound
  have hρ := weylShiftDensity_pos hBpos hK
  have hρone := weylShiftDensity_le_one hBpos hK
  have hρQ := weylShiftDensity_mul_denom hBpos hK
  have hρN : 4 ≤ weylShiftDensity B K * N := by
    rw [← hρQ]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hQbound) hρ.le
  obtain ⟨r, hr, hrQK, m, hm⟩ := varying_denominator_multiples_approximation D q p
    hN hK (weylShiftDenom_pos hBpos hK) hρ
    (by unfold weylShiftError; positivity) hρQ.ge hρN hsmall
    (by linarith only [hsmall, hρone])
    ((weylShiftDensity_card_bound hBpos hK hN₂).trans hDsize)
    (fun h hh => (hDgood h hh).2.1.le.trans (by exact_mod_cast Nat.div_le_self N 2))
    (fun h _ => hq h) hp
  refine ⟨(k + 1) * r, Nat.mul_pos (by omega) hr, ?_, -m, ?_⟩
  · calc
      (k + 1) * r ≤ (k + 1) * (weylShiftDenom B K * K) := Nat.mul_le_mul_left _ hrQK
      _ = 128 * (k + 1) * B ^ 2 * K ^ 2 := by unfold weylShiftDenom; ring
      _ ≤ _ := hb₅
  · have hid : (((k + 1) * r : ℕ) : ℝ) * P.coeff (k + 1) - ((-m : ℤ) : ℝ) =
        -((r : ℝ) * α - m) := by dsimp [α]; push_cast; ring
    rw [hid, abs_neg]
    apply hm.trans
    rw [weylShiftError_output]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hb₆

end Erdos3

end

section

namespace Erdos3

theorem leadingWeylBound_all_degrees (j : ℕ) {B : ℕ} (hB : 2 ≤ B) :
    LeadingWeylBound (j + 1) B (weylBudget j B) := by
  induction j generalizing B with
  | zero => exact leadingWeylBound_one (by omega)
  | succ j ih =>
    have hB' : 2 ≤ 8 * B ^ 2 := by
      have : 0 < B ^ 2 := pow_pos (by omega) 2
      omega
    exact LeadingWeylBound.step (by omega) hB (weylBudget_pos j (by omega)) (ih hB')

theorem polynomial_weyl_inverse (j : ℕ) (P : Polynomial ℝ) {B N : ℕ}
    (hB : 2 ≤ B) (hP : P.natDegree ≤ j + 1) (hN : 0 < N)
    (hsize : weylBudget j B ≤ N)
    (hscore : (N : ℝ) / B ≤ ‖polynomialExponentialSum P N‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ weylBudget j B ∧ ∃ p : ℤ,
      |(q : ℝ) * P.coeff (j + 1) - p| ≤ (weylBudget j B : ℝ) / (N : ℝ) ^ (j + 1) :=
  leadingWeylBound_all_degrees j hB P hP N hN hsize hscore

end Erdos3

end

section

namespace Erdos3

theorem exists_reciprocal_bias_integer {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ∃ B : ℕ, 2 ≤ B ∧ (B : ℝ) ≤ 3 / δ ∧ 1 ≤ δ * B := by
  let B := ⌈2 / δ⌉₊
  have hlo : 2 / δ ≤ (B : ℝ) := Nat.le_ceil _
  have hhi : (B : ℝ) < 2 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have htwo : (2 : ℝ) ≤ 2 / δ := (le_div_iff₀ hδ).mpr (by linarith)
  refine ⟨B, by exact_mod_cast htwo.trans hlo, ?_, ?_⟩
  · have hb := mul_lt_mul_of_pos_right hhi hδ
    have hid : (2 / δ + 1) * δ = 2 + δ := by field_simp
    rw [hid] at hb
    apply (le_div_iff₀ hδ).mpr
    linarith
  · have hb := (div_le_iff₀ hδ).mp hlo
    nlinarith only [hb]

theorem polynomial_weyl_inverse_power_bound (j : ℕ) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      ∀ (P : Polynomial ℝ) (N : ℕ) (δ : ℝ),
        P.natDegree ≤ j + 1 → 0 < N → 0 < δ → δ ≤ 1 →
        (C : ℝ) ≤ δ ^ d * N →
        δ * N ≤ ‖polynomialExponentialSum P N‖ →
        ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C / δ ^ d ∧ ∃ p : ℤ,
          |(q : ℝ) * P.coeff (j + 1) - p| ≤ C / (δ ^ d * (N : ℝ) ^ (j + 1)) := by
  obtain ⟨A, d, hA, hd, hbudget⟩ := weylBudget_polynomial_bound j
  refine ⟨A * 3 ^ d, d, by positivity, hd, ?_⟩
  intro P N δ hP hN hδ hδone hsize hscore
  obtain ⟨B, hB, hBupper, hBlower⟩ := exists_reciprocal_bias_integer hδ hδone
  have hBR : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hδd : 0 < δ ^ d := pow_pos hδ d
  have hbudgetR : (weylBudget j B : ℝ) ≤ (A * 3 ^ d : ℕ) / δ ^ d := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg B : (0 : ℝ) ≤ B) hBupper d
    have hbp : (weylBudget j B : ℝ) ≤ (A : ℝ) * (B : ℝ) ^ d := by
      exact_mod_cast hbudget B (by omega)
    apply hbp.trans
    have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) A)
    simpa only [div_pow, mul_div_assoc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hm
  have hsizeB : weylBudget j B ≤ N := by
    have hs : ((A * 3 ^ d : ℕ) : ℝ) / δ ^ d ≤ N := (div_le_iff₀ hδd).mpr (by nlinarith only [hsize])
    exact_mod_cast hbudgetR.trans hs
  have hscoreB : (N : ℝ) / B ≤ ‖polynomialExponentialSum P N‖ := by
    apply le_trans _ hscore
    apply (div_le_iff₀ hBR).mpr
    have hm := mul_le_mul_of_nonneg_right hBlower hNR.le
    nlinarith only [hm]
  obtain ⟨q, hq, hqbound, p, hp⟩ := polynomial_weyl_inverse j P hB hP hN hsizeB hscoreB
  refine ⟨q, hq, (Nat.cast_le.mpr hqbound).trans hbudgetR, p, hp.trans ?_⟩
  calc
    (weylBudget j B : ℝ) / (N : ℝ) ^ (j + 1) ≤
        (((A * 3 ^ d : ℕ) : ℝ) / δ ^ d) / (N : ℝ) ^ (j + 1) :=
      div_le_div_of_nonneg_right hbudgetR (by positivity)
    _ = _ := by rw [div_div]

end Erdos3

end

section

namespace Erdos3

open Polynomial CircleFourier

def PolynomialIntervalPowerBound (k C d : ℕ) : Prop :=
      ∀ (P : Polynomial ℝ) (u v : ℤ) (δ : ℝ),
        P.natDegree ≤ k → 0 < (v - u).toNat → 0 < δ → δ ≤ 1 →
        (C : ℝ) ≤ δ ^ d * (v - u).toNat →
        δ * (v - u).toNat ≤
          ‖∑ n ∈ Finset.Ico u v, character ((P.eval (n : ℝ) : ℝ) : CircleFourier.Circle)‖ →
        ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C / δ ^ d ∧ ∃ p : ℤ,
          |(q : ℝ) * P.coeff k - p| ≤ C / (δ ^ d * ((v - u).toNat : ℝ) ^ k)

theorem polynomial_weyl_inverse_power_interval (j : ℕ) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ PolynomialIntervalPowerBound (j + 1) C d := by
  obtain ⟨C, d, hC, hd, hW⟩ := polynomial_weyl_inverse_power_bound j
  refine ⟨C, d, hC, hd, ?_⟩
  intro P u v δ hP hN hδ hδone hsize hscore
  rw [polynomial_interval_sum_translate] at hscore
  obtain ⟨q, hq, hqbound, p, hp⟩ := hW (P.comp (X + Polynomial.C (u : ℝ)))
    (v - u).toNat δ (by rwa [polynomial_translate_degree]) hN hδ hδone hsize hscore
  rw [polynomial_translate_top_coeff P hP] at hp
  exact ⟨q, hq, hqbound, p, hp⟩

end Erdos3

end

section

namespace Erdos3

open Polynomial CircleFourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem PolynomialIntervalPowerBound.monomial_character_mean {k C d : ℕ}
    (hW : PolynomialIntervalPowerBound k C d) (α ξ : E) (N : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hsize : (C : ℝ) ≤ δ ^ d * (2 * N + 1))
    (hscore : δ ≤ ‖monomialCharacterMean k α N ξ‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C / δ ^ d ∧ ∃ p : ℤ,
      |(q : ℝ) * inner ℝ ξ α - p| ≤ C / (δ ^ d * (2 * (N : ℝ) + 1) ^ k) := by
  let P : Polynomial ℝ := Polynomial.C (inner ℝ ξ α) * X ^ k
  have hP : P.natDegree ≤ k := natDegree_C_mul_X_pow_le _ _
  have hlength : (((N : ℤ) + 1 - -(N : ℤ)).toNat) = 2 * N + 1 := by omega
  have hset : Finset.Ico (-(N : ℤ)) ((N : ℤ) + 1) = Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hcard : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [← hset, Int.card_Ico, hlength]
  have hsum : (∑ n ∈ Finset.Ico (-(N : ℤ)) ((N : ℤ) + 1), character ((P.eval (n : ℝ) : ℝ) : CircleFourier.Circle)) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), euclideanCharacter ξ ((n : ℝ) ^ k • α) := by
    rw [hset]
    apply Finset.sum_congr rfl
    intro n _
    simp only [P, eval_mul, eval_C, eval_pow, eval_X, euclideanCharacter, inner_smul_right]
    rw [mul_comm (inner ℝ ξ α)]
  have hscore' : δ * ((N : ℤ) + 1 - -(N : ℤ)).toNat ≤
      ‖∑ n ∈ Finset.Ico (-(N : ℤ)) ((N : ℤ) + 1), character ((P.eval (n : ℝ) : ℝ) : CircleFourier.Circle)‖ := by
    rw [monomialCharacterMean, norm_div, Complex.norm_natCast, hcard] at hscore
    rw [hsum, hlength]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (2 * N + 1 : ℕ))).mp hscore
  obtain ⟨q, hq, hqbound, p, hp⟩ := hW P (-(N : ℤ)) ((N : ℤ) + 1) δ hP
    (by rw [hlength]; omega) hδ hδone (by simpa only [hlength, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using hsize) hscore'
  refine ⟨q, hq, hqbound, p, ?_⟩
  simpa only [P, coeff_C_mul_X_pow, ite_true, hlength, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one] using hp

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem PolynomialIntervalPowerBound.short_dual_vector {k C d : ℕ}
    (hW : PolynomialIntervalPowerBound k C d)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {t : ℝ} (ht : 0 < t) (α : E) (N : ℕ)
    (hsize : (C : ℝ) * (8 * normalizedLatticeGaussian Λ t 0) ^ d ≤ 2 * N + 1)
    (hsmall : latticeGaussianMean Λ t k α N < 1 / 2) :
    ∃ ξ : E, ξ ∈ euclideanDualLattice Λ ∧ ξ ≠ 0 ∧
      ‖ξ‖ ≤ Real.sqrt t * schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) ∧
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C * (8 * normalizedLatticeGaussian Λ t 0) ^ d ∧
        ∃ p : ℤ, |(q : ℝ) * inner ℝ ξ α - p| ≤
          C * (8 * normalizedLatticeGaussian Λ t 0) ^ d / (2 * (N : ℝ) + 1) ^ k := by
  obtain ⟨ξ, hξΛ, hξ, hnorm, hscore⟩ :=
    exists_logarithmically_short_dual_correlation Λ ht k α N hsmall
  have hA := normalizedLatticeGaussian_origin_ge_one Λ ht
  let B := 8 * normalizedLatticeGaussian Λ t 0
  have hB : 0 < B := by dsimp [B]; linarith
  have hBone : 1 ≤ B := by dsimp [B]; linarith
  have hδone : B⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hBone
  have hsize' : (C : ℝ) ≤ (B⁻¹) ^ d * (2 * N + 1) := by
    rw [inv_pow, inv_mul_eq_div]
    exact (le_div_iff₀ (pow_pos hB d)).mpr hsize
  obtain ⟨q, hq, hqbound, p, hp⟩ := hW.monomial_character_mean α ξ N (inv_pos.mpr hB) hδone
    hsize' hscore.le
  refine ⟨ξ, hξΛ, hξ, hnorm, q, hq, ?_, p, ?_⟩
  · simpa only [B, inv_pow, div_inv_eq_mul] using hqbound
  · simpa only [B, div_mul_eq_div_div, inv_pow, div_inv_eq_mul] using hp

theorem schmidt_short_dual_vector (j : ℕ) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
        (t : ℝ) (α : E) (N : ℕ), 0 < t →
        (C : ℝ) * (8 * normalizedLatticeGaussian Λ t 0) ^ d ≤ 2 * N + 1 →
        latticeGaussianMean Λ t (j + 1) α N < 1 / 2 →
        ∃ ξ : E, ξ ∈ euclideanDualLattice Λ ∧ ξ ≠ 0 ∧
          ‖ξ‖ ≤ Real.sqrt t * schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) ∧
          ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C * (8 * normalizedLatticeGaussian Λ t 0) ^ d ∧
            ∃ p : ℤ, |(q : ℝ) * inner ℝ ξ α - p| ≤
              C * (8 * normalizedLatticeGaussian Λ t 0) ^ d / (2 * (N : ℝ) + 1) ^ (j + 1) := by
  obtain ⟨C, d, hC, hd, hW⟩ := polynomial_weyl_inverse_power_interval j
  exact ⟨C, d, hC, hd, fun Λ _ _ t α N ht hsize hsmall =>
    hW.short_dual_vector Λ ht α N hsize hsmall⟩

end Erdos3

end

end OAI
