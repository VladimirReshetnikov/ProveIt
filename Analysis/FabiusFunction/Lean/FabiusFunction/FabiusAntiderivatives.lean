import FabiusFunction.GlobalExtension
import FabiusFunction.NormalizedVolterra

/-!
# Exact Volterra primitives of the Fabius function

The signed Fabius extension satisfies a global dilation differential equation.
Combining that equation with the general normalized Volterra calculus gives
its complete zero-based primitive ladder:

`J n 0 extendedFabius x = 2 ^ C(n, 2) * extendedFabius (x / 2 ^ n)`.

The formula includes order zero and every real endpoint.  Since the bounded
Fabius function agrees with the signed extension on `(-∞, 1]`, the same
identity holds there.  The generic polynomial commutator then yields finite
closed forms for every natural monomial weight, again with all order-zero and
endpoint cases included.
-/

open scoped BigOperators ContDiff Interval
open Finset MeasureTheory Set

namespace Fabius

set_option autoImplicit false

private noncomputable def extendedFabiusPrimitiveCandidate
    (F : BoundedFabius) (n : ℕ) (x : ℝ) : ℝ :=
  2 ^ n.choose 2 * extendedFabius F (((2 : ℝ) ^ n)⁻¹ * x)

private theorem iteratedDeriv_extendedFabiusPrimitiveCandidate
    (F : BoundedFabius) (hF : IsFabius F) (n k : ℕ) (x : ℝ) :
    iteratedDeriv k (extendedFabiusPrimitiveCandidate F n) x =
      2 ^ n.choose 2 * (((2 : ℝ) ^ n)⁻¹) ^ k *
        2 ^ (k + 1).choose 2 *
          extendedFabius F
            (2 ^ k * (((2 : ℝ) ^ n)⁻¹ * x)) := by
  unfold extendedFabiusPrimitiveCandidate
  rw [iteratedDeriv_const_mul_field]
  rw [congrFun (iteratedDeriv_comp_const_mul
    ((extendedFabius_contDiff F hF).of_le (by
      exact WithTop.coe_le_coe.mpr le_top)) (((2 : ℝ) ^ n)⁻¹)) x]
  rw [iteratedDeriv_extendedFabius F hF]
  ring

private theorem iteratedDeriv_extendedFabiusPrimitiveCandidate_self
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    iteratedDeriv n (extendedFabiusPrimitiveCandidate F n) =
      extendedFabius F := by
  funext x
  rw [iteratedDeriv_extendedFabiusPrimitiveCandidate F hF]
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have harg :
      (2 : ℝ) ^ n * (((2 : ℝ) ^ n)⁻¹ * x) = x := by
    rw [← mul_assoc, mul_inv_cancel₀ hpow, one_mul]
  have hcoeff :
      (2 : ℝ) ^ n.choose 2 * (((2 : ℝ) ^ n)⁻¹) ^ n *
          2 ^ (n + 1).choose 2 = 1 := by
    rw [inv_pow]
    field_simp
    rw [← pow_add, add_comm, ← choose_square_split n, pow_mul]
  rw [harg]
  rw [hcoeff, one_mul]

private theorem iteratedDeriv_extendedFabiusPrimitiveCandidate_zero
    (F : BoundedFabius) (hF : IsFabius F) (n k : ℕ) :
    iteratedDeriv k (extendedFabiusPrimitiveCandidate F n) 0 = 0 := by
  rw [iteratedDeriv_extendedFabiusPrimitiveCandidate F hF]
  simp only [mul_zero]
  rw [extendedFabius_zero F hF, mul_zero]

/-- The complete normalized primitive ladder for the signed Fabius
extension.  It is valid for every order and every real endpoint. -/
theorem normalizedVolterra_extendedFabius
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    normalizedVolterra n 0 (extendedFabius F) x =
      2 ^ n.choose 2 * extendedFabius F (x / 2 ^ n) := by
  cases n with
  | zero => simp
  | succ n =>
      let G : ℝ → ℝ := extendedFabiusPrimitiveCandidate F (n + 1)
      have hG : ContDiff ℝ (n + 1 : ℕ) G := by
        dsimp only [G, extendedFabiusPrimitiveCandidate]
        have houter : ContDiff ℝ (n + 1 : ℕ) (extendedFabius F) :=
          (extendedFabius_contDiff F hF).of_le (by
            exact WithTop.coe_le_coe.mpr le_top)
        exact contDiff_const.mul
          (houter.comp (contDiff_const.mul contDiff_id))
      have hzero : ∀ k ≤ n, iteratedDeriv k G 0 = 0 := by
        intro k hk
        exact iteratedDeriv_extendedFabiusPrimitiveCandidate_zero
          F hF (n + 1) k
      have hreconstruct :=
        normalizedVolterra_succ_iteratedDeriv_eq_of_zero_jet
          n 0 x G hG hzero
      rw [iteratedDeriv_extendedFabiusPrimitiveCandidate_self
        F hF (n + 1)] at hreconstruct
      simpa only [G, extendedFabiusPrimitiveCandidate, div_eq_inv_mul,
        Nat.succ_eq_add_one] using hreconstruct

/-- The bounded Fabius function has the same normalized primitive ladder on
the maximal interval `(-∞, 1]` where it agrees with the signed extension. -/
theorem normalizedVolterra_fabiusReal_of_le_one
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) {x : ℝ} (hx : x ≤ 1) :
    normalizedVolterra n 0 (fabiusReal F) x =
      2 ^ n.choose 2 * fabiusReal F (x / 2 ^ n) := by
  have harg : x / (2 : ℝ) ^ n ≤ 1 := by
    have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    exact (div_le_one (by positivity)).2 (hx.trans hpow)
  calc
    normalizedVolterra n 0 (fabiusReal F) x =
        normalizedVolterra n 0 (extendedFabius F) x := by
      apply normalizedVolterra_congr
      intro t ht
      apply fabiusReal_eq_extendedFabius_of_le_one F hF
      have ht' : t ∈ Icc (min 0 x) (max 0 x) := by
        simpa only [Set.uIcc] using ht
      exact ht'.2.trans (max_le (by norm_num) hx)
    _ = 2 ^ n.choose 2 * extendedFabius F (x / 2 ^ n) :=
      normalizedVolterra_extendedFabius F hF n x
    _ = 2 ^ n.choose 2 * fabiusReal F (x / 2 ^ n) := by
      rw [fabiusReal_eq_extendedFabius_of_le_one F hF harg]

/-- Finite closed form for every natural monomial weight of the signed
extension.  The formula is global and includes order zero. -/
theorem normalizedVolterra_pow_mul_extendedFabius
    (F : BoundedFabius) (hF : IsFabius F) (n p : ℕ) (x : ℝ) :
    normalizedVolterra n 0 (fun t => t ^ p * extendedFabius F t) x =
      ∑ r ∈ range (p + 1),
        (-1 : ℝ) ^ r * p.choose r * (n.ascFactorial r : ℝ) *
          x ^ (p - r) * 2 ^ (n + r).choose 2 *
            extendedFabius F (x / 2 ^ (n + r)) := by
  have hint : IntervalIntegrable (extendedFabius F) volume 0 x :=
    (extendedFabius_contDiff F hF).continuous.intervalIntegrable _ _
  rw [show (fun t => t ^ p * extendedFabius F t) =
      (fun t => t ^ p • extendedFabius F t) by rfl]
  rw [normalizedVolterra_monomial n p 0 x (extendedFabius F) hint]
  apply Finset.sum_congr rfl
  intro r hr
  rw [normalizedVolterra_extendedFabius F hF]
  simp only [smul_eq_mul]
  ring

/-- Finite natural-monomial formula for the bounded Fabius function on its
maximal signed-extension range `x ≤ 1`. -/
theorem normalizedVolterra_pow_mul_fabiusReal_of_le_one
    (F : BoundedFabius) (hF : IsFabius F) (n p : ℕ) {x : ℝ} (hx : x ≤ 1) :
    normalizedVolterra n 0 (fun t => t ^ p * fabiusReal F t) x =
      ∑ r ∈ range (p + 1),
        (-1 : ℝ) ^ r * p.choose r * (n.ascFactorial r : ℝ) *
          x ^ (p - r) * 2 ^ (n + r).choose 2 *
            fabiusReal F (x / 2 ^ (n + r)) := by
  have hint : IntervalIntegrable (fabiusReal F) volume 0 x :=
    hF.contDiff.continuous.intervalIntegrable _ _
  rw [show (fun t => t ^ p * fabiusReal F t) =
      (fun t => t ^ p • fabiusReal F t) by rfl]
  rw [normalizedVolterra_monomial n p 0 x (fabiusReal F) hint]
  apply Finset.sum_congr rfl
  intro r hr
  rw [normalizedVolterra_fabiusReal_of_le_one F hF (n + r) hx]
  simp only [smul_eq_mul]
  ring

end Fabius
