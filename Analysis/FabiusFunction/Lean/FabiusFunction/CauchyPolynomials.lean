import FabiusFunction.FallingFactorialSeries
import FabiusFunction.BernoulliStirling
import FabiusFunction.StirlingBasisChange
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Bernoulli polynomials of the second kind (Cauchy polynomials)

The polynomials `b_n(x)` are defined by `t (1+t)^x / log(1+t) = ∑_n b_n(x) t^n/n!`
(`cauchySeries`, `cauchyPoly`).  From the falling-factorial generating function we derive

* `b_{n+1}' = (n+1) (x)_n` (`derivative_cauchyPoly_succ`),
* `b_{n+1}(x+1) - b_{n+1}(x) = (n+1) b_n(x)` (`cauchyPoly_succ_eval_add_one_sub`),
* `b_n(x+y) = ∑_k C(n,k) b_k(x) (y)_{n-k}` (`cauchyPoly_eval_add`),
* `b_n(x) = b_n(0) + ∑_{k=1}^n (n/k) s(n-1,k-1) x^k` (`cauchyPoly_succ_eq`),
* `b_n(0) = ∑_k s(n,k)/(k+1)` (`cauchyPoly_eval_zero`), through the formal integral
  `∫_0^1 p(u) du = ∑_k p_k/(k+1)` on polynomials (`intPoly`) and `∂_x (1+t)^x = log(1+t)(1+t)^x`.

## Main results

* `tOverLog`, `logDivSeries_mul_tOverLog`, `log_mul_tOverLog`, `cauchySeries`, `cauchyPoly`.
* `Dx_cauchySeries`, `descPochhammer_eval_X`, `derivative_cauchyPoly_succ`.
* `egfA_cauchyPoly_eval`, `cauchyPoly_succ_eval_add_one_sub`, `cauchyPoly_eval_add`.
* `eq_C_eval_zero_add_of_derivative_eq`, `cauchyPoly_succ_eq`.
* `intPoly`, `intPoly_derivative`, `mapIntPoly`, `cauchyPoly_eval_zero`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-! ### `t/log(1+t)` and the Cauchy generating function -/

/-- The divided logarithm `log(1 + t) / t` has constant coefficient one. -/
theorem constantCoeff_logDivSeries : constantCoeff (logDivSeries ℚ) = 1 := by
  rw [logDivSeries, constantCoeff_egfA]
  simp

/-- `t/log(1+t)`, the inverse of `log(1+t)/t`. -/
noncomputable def tOverLog : ℚ⟦X⟧ := (logDivSeries ℚ)⁻¹

/-- The divided logarithm and `tOverLog` multiply to one. -/
theorem logDivSeries_mul_tOverLog : logDivSeries ℚ * tOverLog = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_logDivSeries]; exact one_ne_zero)

/-- Multiplying `tOverLog` by the formal logarithm recovers the series variable. -/
theorem log_mul_tOverLog : log ℚ * tOverLog = X := by
  rw [← X_mul_logDivSeries, mul_assoc, logDivSeries_mul_tOverLog, mul_one]

/-- `t/log(1+t)` with constant coefficients in `ℚ[x][[t]]`. -/
noncomputable def tOverLogPoly : (Polynomial ℚ)⟦X⟧ :=
  PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) tOverLog

/-- The polynomial-coefficient lifts of `log(1+t)` and `t/log(1+t)` multiply to `t`. -/
theorem logPoly_mul_tOverLogPoly : logPoly * tOverLogPoly = X := by
  rw [logPoly, tOverLogPoly, ← map_mul, log_mul_tOverLog, PowerSeries.map_X]

/-- The lifted series `tOverLogPoly` is constant with respect to `Dx`. -/
theorem Dx_tOverLogPoly : Dx tOverLogPoly = 0 := Dx_map_C _

/-- The generating function `t (1+t)^x / log(1+t)`. -/
noncomputable def cauchySeries : (Polynomial ℚ)⟦X⟧ := fallingPoly * tOverLogPoly

/-- The Cauchy polynomials `b_n(x) = n! [t^n] t(1+t)^x/log(1+t)`. -/
noncomputable def cauchyPoly (n : ℕ) : Polynomial ℚ := (n.factorial : ℚ) • coeff n cauchySeries

/-- Coefficient normalization relating the Cauchy generating series to `cauchyPoly`. -/
theorem coeff_cauchySeries (n : ℕ) :
    coeff n cauchySeries = (1 / n.factorial : ℚ) • cauchyPoly n := by
  rw [cauchyPoly, smul_smul, one_div_mul_cancel (by positivity), one_smul]

/-- `∂_x [t(1+t)^x/log(1+t)] = t (1+t)^x`. -/
theorem Dx_cauchySeries : Dx cauchySeries = X * fallingPoly := by
  rw [cauchySeries, Dx_mul, Dx_tOverLogPoly, mul_zero, add_zero, Dx_fallingPoly]
  calc logPoly * fallingPoly * tOverLogPoly = logPoly * tOverLogPoly * fallingPoly := by ring
    _ = X * fallingPoly := by rw [logPoly_mul_tOverLogPoly]

/-- The falling factorial over `ℚ[x]` evaluated at `x` is the falling factorial over `ℚ`. -/
theorem descPochhammer_eval_X (n : ℕ) :
    (descPochhammer (Polynomial ℚ) n).eval (Polynomial.X : Polynomial ℚ) = descPochhammer ℚ n := by
  rw [← descPochhammer_map (Polynomial.C : ℚ →+* Polynomial ℚ), Polynomial.eval_map,
    Polynomial.eval₂_C_X]

/-- **The derivative:** `b_{n+1}'(x) = (n+1) (x)_n`. -/
theorem derivative_cauchyPoly_succ (n : ℕ) :
    Polynomial.derivative (cauchyPoly (n + 1)) =
      ((n + 1 : ℕ) : Polynomial ℚ) * descPochhammer ℚ n := by
  have h := congrArg (coeff (n + 1)) Dx_cauchySeries
  rw [coeff_Dx, coeff_cauchySeries, coeff_succ_X_mul, fallingPoly, fallingSeries, coeff_egfA,
    Polynomial.derivative_smul, descPochhammer_eval_X, Polynomial.algebraMap_eq] at h
  have h2 := congrArg (fun p => ((n + 1).factorial : ℚ) • p) h
  rw [smul_smul, mul_one_div_cancel (by positivity), one_smul] at h2
  rw [h2, Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul,
    ← map_natCast Polynomial.C (n + 1)]
  congr 2
  rw [Nat.factorial_succ]
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

/-! ### Evaluation generating functions -/

/-- The EGF of `n ↦ b_n(a)` is `(1+t)^a · t/log(1+t)`. -/
theorem egfA_cauchyPoly_eval (a : ℚ) :
    egfA ℚ (fun n => (cauchyPoly n).eval a) = fallingSeries ℚ a * tOverLog := by
  have h1 : PowerSeries.map (Polynomial.evalRingHom a) fallingPoly = fallingSeries ℚ a := by
    ext n
    rw [coeff_map, fallingPoly, fallingSeries, coeff_egfA, fallingSeries, coeff_egfA,
      descPochhammer_eval_X, Polynomial.algebraMap_eq, Polynomial.coe_evalRingHom,
      Polynomial.eval_mul, Polynomial.eval_C, Algebra.algebraMap_self, RingHom.id_apply]
  have h2 : PowerSeries.map (Polynomial.evalRingHom a) tOverLogPoly = tOverLog := by
    ext n
    rw [coeff_map, tOverLogPoly, coeff_map, Polynomial.coe_evalRingHom, Polynomial.eval_C]
  have h3 : PowerSeries.map (Polynomial.evalRingHom a) cauchySeries =
      fallingSeries ℚ a * tOverLog := by
    rw [cauchySeries, map_mul, h1, h2]
  rw [← h3]
  ext n
  rw [coeff_egfA, coeff_map, coeff_cauchySeries, Polynomial.coe_evalRingHom, Polynomial.eval_smul,
    smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]

/-- **The difference equation:** `b_{n+1}(a+1) - b_{n+1}(a) = (n+1) b_n(a)`. -/
theorem cauchyPoly_succ_eval_add_one_sub (n : ℕ) (a : ℚ) :
    (cauchyPoly (n + 1)).eval (a + 1) - (cauchyPoly (n + 1)).eval a =
      (n + 1) * (cauchyPoly n).eval a := by
  have h : egfA ℚ (fun m => (cauchyPoly m).eval (a + 1)) -
      egfA ℚ (fun m => (cauchyPoly m).eval a) = X * egfA ℚ (fun m => (cauchyPoly m).eval a) := by
    rw [egfA_cauchyPoly_eval, egfA_cauchyPoly_eval, fallingSeries_add_one]
    ring
  have hc := congrArg (coeff (n + 1)) h
  rw [map_sub, coeff_egfA, coeff_egfA, coeff_succ_X_mul, coeff_egfA, Algebra.algebraMap_self,
    RingHom.id_apply, RingHom.id_apply, ← mul_sub] at hc
  have hn : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
  have hn' : (n.factorial : ℚ) ≠ 0 := by positivity
  calc (cauchyPoly (n + 1)).eval (a + 1) - (cauchyPoly (n + 1)).eval a
      = ((n + 1).factorial : ℚ) * (1 / (n + 1).factorial *
          ((cauchyPoly (n + 1)).eval (a + 1) - (cauchyPoly (n + 1)).eval a)) := by
        field_simp
    _ = ((n + 1).factorial : ℚ) * (1 / n.factorial * (cauchyPoly n).eval a) := by rw [hc]
    _ = (n + 1) * (cauchyPoly n).eval a := by
        rw [Nat.factorial_succ]
        push_cast
        field_simp

/-- **The addition formula:** `b_n(a+c) = ∑_k C(n,k) b_k(a) (c)_{n-k}`. -/
theorem cauchyPoly_eval_add (n : ℕ) (a c : ℚ) :
    (cauchyPoly n).eval (a + c) =
      ∑ k ∈ range (n + 1),
        (n.choose k : ℚ) * ((cauchyPoly k).eval a * (descPochhammer ℚ (n - k)).eval c) := by
  have h : egfA ℚ (fun m => (cauchyPoly m).eval (a + c)) =
      egfA ℚ (Bell.binomialConv (fun k => (cauchyPoly k).eval a)
        (fun k => (descPochhammer ℚ k).eval c)) := by
    rw [← egfA_mul, egfA_cauchyPoly_eval, egfA_cauchyPoly_eval, ← fallingSeries_mul]
    show fallingSeries ℚ a * fallingSeries ℚ c * tOverLog =
      fallingSeries ℚ a * tOverLog * fallingSeries ℚ c
    ring
  have h' := congrFun (seq_eq_of_egfA_eq ℚ h) n
  rw [Bell.binomialConv_eq_sum_range] at h'
  exact h'

/-! ### Formal integration and the explicit formula -/

/-- A polynomial is determined by its derivative and its value at `0`:
if `p' = ∑_{j ≤ N} c_j x^j` then `p = p(0) + ∑_{j ≤ N} c_j x^{j+1}/(j+1)`. -/
theorem eq_C_eval_zero_add_of_derivative_eq (p : Polynomial ℚ) (c : ℕ → ℚ) (N : ℕ)
    (hd : Polynomial.derivative p = ∑ j ∈ range (N + 1), Polynomial.C (c j) * Polynomial.X ^ j) :
    p = Polynomial.C (p.eval 0) +
      ∑ j ∈ range (N + 1), Polynomial.C (c j / (j + 1)) * Polynomial.X ^ (j + 1) := by
  ext m
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  cases m with
  | zero =>
    simp [Polynomial.coeff_zero_eq_eval_zero]
  | succ m =>
    have hq := congrArg (fun q => Polynomial.coeff q m) hd
    simp only [Polynomial.coeff_derivative, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range] at hq
    simp only [Nat.succ_ne_zero, if_false, zero_add, add_left_inj, Finset.sum_ite_eq,
      Finset.mem_range]
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    split_ifs at hq ⊢ with h
    · rw [eq_div_iff hm]
      exact_mod_cast hq
    · exact (mul_eq_zero.mp hq).resolve_right (by exact_mod_cast hm)

/-- **The explicit formula:** `b_{n+1}(x) = b_{n+1}(0) + ∑_{j ≤ n} (n+1)/(j+1) s(n,j) x^{j+1}`. -/
theorem cauchyPoly_succ_eq (n : ℕ) :
    cauchyPoly (n + 1) = Polynomial.C ((cauchyPoly (n + 1)).eval 0) +
      ∑ j ∈ range (n + 1),
        Polynomial.C (((n + 1 : ℕ) : ℚ) * (signedStirlingFirst n j : ℚ) / (j + 1)) *
          Polynomial.X ^ (j + 1) := by
  refine eq_C_eval_zero_add_of_derivative_eq _ (fun j => ((n + 1 : ℕ) : ℚ) * (signedStirlingFirst n j : ℚ)) n ?_
  rw [derivative_cauchyPoly_succ, descPochhammer_eq_sum_monomial_signedStirlingFirst, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, ← mul_assoc, ← map_natCast Polynomial.C]

/-! ### The formal integral `∫_0^1` and the value at `0` -/

/-- The formal integral `∫_0^1 p(u) du = ∑_k p_k/(k+1)` on `ℚ[u]`, as a linear functional. -/
noncomputable def intPoly : Polynomial ℚ →ₗ[ℚ] ℚ where
  toFun p := p.sum fun k a => a / (k + 1)
  map_add' p q :=
    Polynomial.sum_add_index p q _ (fun _ => zero_div _) (fun _ _ _ => add_div _ _ _)
  map_smul' c p := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Polynomial.sum_smul_index _ _ _ (fun _ => zero_div _), Polynomial.sum_def,
      Polynomial.sum_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The formal integral of a monomial is `a / (k + 1)`. -/
theorem intPoly_monomial (k : ℕ) (a : ℚ) : intPoly (Polynomial.monomial k a) = a / (k + 1) := by
  show (Polynomial.monomial k a).sum (fun k a => a / (k + 1 : ℚ)) = a / (k + 1)
  exact Polynomial.sum_monomial_index a _ (zero_div _)

/-- **The fundamental theorem for the formal integral:** `∫_0^1 p' = p(1) - p(0)`. -/
theorem intPoly_derivative (p : Polynomial ℚ) :
    intPoly (Polynomial.derivative p) = p.eval 1 - p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.eval_add, Polynomial.eval_add]; ring
  | monomial k a =>
    rw [Polynomial.derivative_monomial, intPoly_monomial, Polynomial.eval_monomial,
      Polynomial.eval_monomial, one_pow, mul_one]
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel, zero_pow (Nat.succ_ne_zero k), mul_zero, sub_zero]
      have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp

/-- The formal integral applied coefficientwise to a series in `ℚ[x][[t]]`. -/
noncomputable def mapIntPoly (f : (Polynomial ℚ)⟦X⟧) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => intPoly (coeff n f)

/-- Coefficients of `mapIntPoly f` are formal integrals of the coefficients of `f`. -/
theorem coeff_mapIntPoly (f : (Polynomial ℚ)⟦X⟧) (n : ℕ) :
    coeff n (mapIntPoly f) = intPoly (coeff n f) := coeff_mk _ _

/-- Coefficientwise formal integration pulls out a scalar rational power series. -/
theorem mapIntPoly_map_C_mul (g : ℚ⟦X⟧) (f : (Polynomial ℚ)⟦X⟧) :
    mapIntPoly (PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) g * f) = g * mapIntPoly f := by
  ext n
  rw [coeff_mapIntPoly, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coeff_map, coeff_mapIntPoly, ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

/-- `∫_0^1 ∂_x (1+t)^x dx = (1+t) - 1 = t`. -/
theorem mapIntPoly_Dx_fallingPoly : mapIntPoly (Dx fallingPoly) = X := by
  ext n
  rw [coeff_mapIntPoly, coeff_Dx, intPoly_derivative, fallingPoly, fallingSeries, coeff_egfA,
    descPochhammer_eval_X, Polynomial.algebraMap_eq, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_C]
  have h1 := congrArg (coeff n) (fallingSeries_one ℚ)
  have h0 := congrArg (coeff n) (fallingSeries_zero ℚ)
  rw [fallingSeries, coeff_egfA, Algebra.algebraMap_self, RingHom.id_apply] at h1 h0
  rw [h1, h0, map_add, coeff_one]
  split_ifs <;> simp

/-- `∫_0^1 (1+t)^x dx = t/log(1+t)`. -/
theorem mapIntPoly_fallingPoly : mapIntPoly fallingPoly = tOverLog := by
  have h := mapIntPoly_Dx_fallingPoly
  rw [Dx_fallingPoly, logPoly, mapIntPoly_map_C_mul, ← X_mul_logDivSeries, mul_assoc] at h
  have h2 : X * (logDivSeries ℚ * mapIntPoly fallingPoly - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  have h3 := sub_eq_zero.mp (eq_zero_of_X_mul_eq_zero ℚ h2)
  rw [tOverLog, PowerSeries.eq_inv_iff_mul_eq_one (by rw [constantCoeff_logDivSeries]; exact one_ne_zero), mul_comm]
  exact h3

/-- **The value at `0`:** `b_n(0) = ∑_k s(n,k)/(k+1)`. -/
theorem cauchyPoly_eval_zero (n : ℕ) :
    (cauchyPoly n).eval 0 = ∑ k ∈ range (n + 1), (signedStirlingFirst n k : ℚ) / (k + 1) := by
  have hE := congrArg (coeff n) (egfA_cauchyPoly_eval 0)
  rw [fallingSeries_zero, one_mul, ← mapIntPoly_fallingPoly, coeff_egfA, coeff_mapIntPoly,
    fallingPoly, fallingSeries, coeff_egfA, descPochhammer_eval_X, Polynomial.algebraMap_eq,
    ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply,
    descPochhammer_eq_sum_monomial_signedStirlingFirst, map_sum] at hE
  simp only [intPoly_monomial] at hE
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  exact mul_left_cancel₀ (one_div_ne_zero hn) hE

end Fabius
