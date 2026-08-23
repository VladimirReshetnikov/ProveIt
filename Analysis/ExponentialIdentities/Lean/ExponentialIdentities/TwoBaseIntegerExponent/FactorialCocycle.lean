import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Mesoscopic factorial cocycles: the finite core

A hypothetical two-base solution `M = 2^x`, `A = 3^x` places the falling factorial
`F_n = (A^n)_{M^n}` in a "birthday" regime governed by `α = log 2 / log 3 ∈ (1/2, 2/3)`:
the pair-collision mode `λ = M^2/A = (4/3)^x` grows while the triple-collision mode
`η = M^3/A^2 = (8/9)^x` decays.  Signed products `∏_j F_{n+j}^{c_j}` are governed by the
shift polynomial `P(T) = ∑ c_j T^j`, through the two identities
`P(E)(ρ^n) = P(ρ) ρ^n` and `P(E)(n ρ^n) = ρ^n (n P(ρ) + ρ P'(ρ))`.

This file formalizes the finite and elementary parts of that analysis:

* the universal window `1/2 < log 2 / log 3 < 2/3` (from `4 > 3` and `8 < 9`) and the
  resulting mode inequalities `M^2/A > 1`, `M^3/A^2 < 1` for every `x > 0`;
* the shift-evaluation identities on geometric and `n`-times-geometric modes;
* the primitive annihilator `P_*(T) = (T - M)^2 (A T - M^2)` kills all three growing modes:
  `P_*(M) = P_*'(M) = P_*(M^2/A) = 0`;
* the carry-free prefix at a structural prime: if `r^c ∣ K ≤ N`, the lowest `c` base-`r`
  digit positions create no carry in `K + (N - K)`, hence
  `v_r (N choose K) ≤ log_r N - c` (Kummer).

The analytic classification (every fixed-shift near-unit is a multiple of `P_*`) and the
prime-window denominator theorem (Huxley and Brun–Titchmarsh inputs) are paper proofs and
are not formalized here.
-/

namespace LeanProofs.TwoBaseIntegerExponent.FactorialCocycle

open Polynomial Finset Real

/-! ### The mesoscopic window -/

theorem log_two_div_log_three_gt_half : (1 : ℝ) / 2 < Real.log 2 / Real.log 3 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [div_lt_div_iff₀ (by norm_num) h3, one_mul]
  have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  linarith

theorem log_two_div_log_three_lt_two_thirds : Real.log 2 / Real.log 3 < (2 : ℝ) / 3 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [div_lt_div_iff₀ h3 (by norm_num)]
  have : Real.log 8 < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  linarith

theorem two_rpow_sq {x : ℝ} : ((2 : ℝ) ^ x) ^ 2 = (4 : ℝ) ^ x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num)]
  norm_num

theorem two_rpow_cube {x : ℝ} : ((2 : ℝ) ^ x) ^ 3 = (8 : ℝ) ^ x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num)]
  norm_num

theorem three_rpow_sq {x : ℝ} : ((3 : ℝ) ^ x) ^ 2 = (9 : ℝ) ^ x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num)]
  norm_num

/-- The pair-collision mode `λ = M^2 / A = (4/3)^x` exceeds one for every `x > 0`. -/
theorem pair_mode_gt_one {x : ℝ} (hx : 0 < x) : 1 < ((2 : ℝ) ^ x) ^ 2 / (3 : ℝ) ^ x := by
  rw [two_rpow_sq, ← Real.div_rpow (by norm_num) (by norm_num)]
  exact Real.one_lt_rpow (by norm_num) hx

/-- The triple-collision mode `η = M^3 / A^2 = (8/9)^x` is below one for every `x > 0`. -/
theorem triple_mode_lt_one {x : ℝ} (hx : 0 < x) :
    ((2 : ℝ) ^ x) ^ 3 / ((3 : ℝ) ^ x) ^ 2 < 1 := by
  rw [two_rpow_cube, three_rpow_sq, ← Real.div_rpow (by norm_num) (by norm_num)]
  exact Real.rpow_lt_one (by norm_num) (by norm_num) hx

/-! ### Shift-polynomial calculus -/

/-- The shift evaluation `P(E) u` at index `n`: `∑_j c_j u_{n+j}`. -/
noncomputable def shiftEval (P : ℝ[X]) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ P.support, P.coeff j * u (n + j)

/-- `P(E)(ρ^n) = P(ρ) ρ^n`. -/
theorem shiftEval_geom (P : ℝ[X]) (ρ : ℝ) (n : ℕ) :
    shiftEval P (fun k => ρ ^ k) n = ρ ^ n * P.eval ρ := by
  unfold shiftEval
  rw [eval_eq_sum, Polynomial.sum_def, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  dsimp only
  rw [pow_add]; ring

/-- `P(E)(n ρ^n) = ρ^n (n P(ρ) + ρ P'(ρ))`. -/
theorem shiftEval_mul_geom (P : ℝ[X]) (ρ : ℝ) (n : ℕ) :
    shiftEval P (fun k => (k : ℝ) * ρ ^ k) n
      = ρ ^ n * ((n : ℝ) * P.eval ρ + ρ * P.derivative.eval ρ) := by
  unfold shiftEval
  rw [eval_eq_sum, derivative_eval, Polynomial.sum_def, Polynomial.sum_def]
  simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp; ring
  · have : ρ ^ (j - 1) * ρ = ρ ^ j := by
      rw [← pow_succ]; congr 1; omega
    push_cast
    rw [pow_add]
    linear_combination (-(P.coeff j * ρ ^ n * (j : ℝ))) * this

/-- Consequence: if `P(ρ) = 0` and `P'(ρ) = 0`, the shift kills both `ρ^n` and `n ρ^n`. -/
theorem shiftEval_eq_zero_of_double_root (P : ℝ[X]) {ρ : ℝ} (h0 : P.eval ρ = 0)
    (h1 : P.derivative.eval ρ = 0) (n : ℕ) :
    shiftEval P (fun k => ρ ^ k) n = 0 ∧ shiftEval P (fun k => (k : ℝ) * ρ ^ k) n = 0 := by
  rw [shiftEval_geom, shiftEval_mul_geom, h0, h1]; simp

/-! ### The primitive annihilator -/

/-- `P_*(T) = (T - M)^2 (A T - M^2)`, the unreduced minimal annihilator. -/
noncomputable def annihilator (M A : ℝ) : ℝ[X] := (X - C M) ^ 2 * (C A * X - C (M ^ 2))

theorem annihilator_eval_M (M A : ℝ) : (annihilator M A).eval M = 0 := by
  simp [annihilator]

theorem annihilator_derivative_eval_M (M A : ℝ) : (annihilator M A).derivative.eval M = 0 := by
  simp [annihilator, derivative_mul, derivative_pow]

theorem annihilator_eval_pair_mode (M A : ℝ) (hA : A ≠ 0) :
    (annihilator M A).eval (M ^ 2 / A) = 0 := by
  simp only [annihilator, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  rw [mul_div_cancel₀ _ hA]; ring

/-- The three growing modes of the factorial cocycle, `n M^n`, `M^n`, and `λ^n` with
`λ = M^2/A`, are all annihilated by `P_*`. -/
theorem annihilator_kills_growing_modes (M A : ℝ) (hA : A ≠ 0) (n : ℕ) :
    shiftEval (annihilator M A) (fun k => (k : ℝ) * M ^ k) n = 0 ∧
    shiftEval (annihilator M A) (fun k => M ^ k) n = 0 ∧
    shiftEval (annihilator M A) (fun k => (M ^ 2 / A) ^ k) n = 0 := by
  obtain ⟨h1, h2⟩ := shiftEval_eq_zero_of_double_root (annihilator M A)
    (annihilator_eval_M M A) (annihilator_derivative_eval_M M A) n
  refine ⟨h2, h1, ?_⟩
  rw [shiftEval_geom, annihilator_eval_pair_mode M A hA, mul_zero]

/-- The coefficient expansion `P_* = -M^4 + M^2(A + 2M) T - (M^2 + 2AM) T^2 + A T^3`. -/
theorem annihilator_expand (M A : ℝ) :
    annihilator M A = C (-(M ^ 4)) + C (M ^ 2 * (A + 2 * M)) * X
      + C (-(M ^ 2 + 2 * A * M)) * X ^ 2 + C A * X ^ 3 := by
  unfold annihilator
  apply Polynomial.funext
  intro t
  simp only [eval_mul, eval_pow, eval_sub, eval_add, eval_X, eval_C]
  ring

/-! ### Carry-free prefix at a structural prime -/

/-- If `r^c ∣ K` and `K ≤ N`, division by `r^c` is exact on the `K` summand:
`⌊N / r^c⌋ = ⌊(N - K) / r^c⌋ + K / r^c` — no carry at the lowest `c` digit positions. -/
theorem floor_div_add_of_dvd {r c K N : ℕ} (hdvd : r ^ c ∣ K) (hKN : K ≤ N) :
    N / r ^ c = (N - K) / r ^ c + K / r ^ c := by
  conv_lhs => rw [← Nat.sub_add_cancel hKN]
  exact Nat.add_div_of_dvd_left hdvd

/-- **Kummer bound with a carry-free prefix.**  For a prime `r` with `r^c ∣ K ≤ N`, the
lowest `c` base-`r` positions create no carry in `K + (N - K)`, so
`v_r (N choose K) ≤ log_r N - c`. -/
theorem padicValNat_choose_le_of_pow_dvd {r : ℕ} [hr : Fact r.Prime] {c K N : ℕ}
    (hdvd : r ^ c ∣ K) (hKN : K ≤ N) :
    padicValNat r (N.choose K) ≤ Nat.log r N - c := by
  rw [padicValNat_choose hKN (Nat.lt_succ_self (Nat.log r N))]
  have hsub : ({i ∈ Finset.Ico 1 (Nat.log r N + 1) | r ^ i ≤ K % r ^ i + (N - K) % r ^ i}
      : Finset ℕ) ⊆ Finset.Ico (c + 1) (Nat.log r N + 1) := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_Ico] at hi
    rw [Finset.mem_Ico]
    refine ⟨?_, hi.1.2⟩
    by_contra hlt
    have hic : r ^ i ∣ K := (Nat.pow_dvd_pow r (by omega : i ≤ c)).trans hdvd
    have hmod : K % r ^ i = 0 := Nat.mod_eq_zero_of_dvd hic
    have hlt' : (N - K) % r ^ i < r ^ i := Nat.mod_lt _ (pow_pos hr.out.pos _)
    rw [hmod, zero_add] at hi
    omega
  calc _ ≤ (Finset.Ico (c + 1) (Nat.log r N + 1)).card := Finset.card_le_card hsub
    _ = Nat.log r N - c := by rw [Nat.card_Ico]; omega

end LeanProofs.TwoBaseIntegerExponent.FactorialCocycle
