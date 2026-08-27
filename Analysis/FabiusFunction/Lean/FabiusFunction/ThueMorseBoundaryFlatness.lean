import FabiusFunction.ThueMorseValuation
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Boundary flatness of the lacunary product

The atlas's function `𝓔(t) = ∏_{j≥0} (1 - e^(-2^j·t))` — the
Thue–Morse generating product evaluated at `e^(-t)` — is
super-polynomially flat as `t ↓ 0`.  We prove an *effective two-sided*
version of the boxed logarithmic asymptotic: for every level `m`,

* upper: `𝓔(t) ≤ 2^(m(m-1)/2)·t^m` (`lacunaryExpProduct_le`), so
  `𝓔(t) = O(t^A)` for every `A` — the flatness that drives the Mellin
  continuation;
* lower: `2^(m(m-1)/2)·(t/2)^m·𝓔(1/2) ≤ 𝓔(t)` whenever
  `1/2 ≤ 2^m·t ≤ 2` (`le_lacunaryExpProduct`).

Both follow from the **self-similarity**
`𝓔(t) = (∏_{j<m}(1-e^(-2^j t)))·𝓔(2^m·t)`
(`lacunaryExpProduct_eq_prod_mul`), positivity, monotonicity, and the
elementary sandwich `x/2 ≤ 1 - e^(-x) ≤ x` on `[0,1]`
(`half_le_one_sub_exp_neg`, `one_sub_exp_neg_le`), all reusable.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-- `1 - e^(-x) ≤ x` for `x ≥ 0`. -/
theorem one_sub_exp_neg_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- `x/2 ≤ 1 - e^(-x)` on `[0,1]`: from `e^x ≥ 1+x` one gets
`e^(-x) ≤ 1/(1+x)`, and `1 - 1/(1+x) = x/(1+x) ≥ x/2`. -/
theorem half_le_one_sub_exp_neg (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have hexp : 1 + x ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  have h2 : Real.exp (-x) * (1 + x) ≤ 1 := by
    calc Real.exp (-x) * (1 + x) ≤ Real.exp (-x) * Real.exp x := by
          exact mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-x), mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - x)]

/-- Each factor of the lacunary product is positive for `t > 0`. -/
theorem one_sub_exp_neg_two_pow_pos (t : ℝ) (ht : 0 < t) (j : ℕ) :
    0 < 1 - Real.exp (-(2 ^ j * t)) := by
  have hx : (0 : ℝ) < 2 ^ j * t := by positivity
  have := Real.exp_lt_one_iff.mpr (by linarith : -(2 ^ j * t) < 0)
  linarith

/-- Each factor is at most one. -/
theorem one_sub_exp_neg_two_pow_le_one (t : ℝ) (j : ℕ) :
    1 - Real.exp (-(2 ^ j * t)) ≤ 1 := by
  have := Real.exp_pos (-(2 ^ j * t))
  linarith

/-- The lacunary exponentials are summable for `t > 0` (dominated by a
geometric series, since `2^j ≥ j + 1`). -/
theorem summable_exp_neg_two_pow (t : ℝ) (ht : 0 < t) :
    Summable (fun j : ℕ => Real.exp (-(2 ^ j * t))) := by
  have hr1 : Real.exp (-t) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hr0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hgeom : Summable (fun j : ℕ => Real.exp (-t) ^ (j + 1)) := by
    have h := summable_geometric_of_lt_one hr0 hr1
    simpa [pow_succ, mul_comm] using h.mul_left (Real.exp (-t))
  refine Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le)
    (fun j => ?_) hgeom
  have hexp : Real.exp (-(2 ^ j * t)) = Real.exp (-t) ^ (2 ^ j : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  exact pow_le_pow_of_le_one hr0 hr1.le
    (by have := Nat.lt_two_pow_self (n := j); omega)

/-- The factor logarithms are summable for `t > 0`. -/
theorem summable_log_one_sub_exp (t : ℝ) (ht : 0 < t) :
    Summable (fun j : ℕ => Real.log (1 - Real.exp (-(2 ^ j * t)))) := by
  have h := Real.summable_log_one_add_of_summable
    (summable_exp_neg_two_pow t ht).neg
  refine h.congr fun j => ?_
  rw [← sub_eq_add_neg]

/-- **The lacunary boundary product** `𝓔(t) = ∏_{j≥0}(1 - e^(-2^j·t))`
— the Thue–Morse generating product at `e^(-t)`. -/
noncomputable def lacunaryExpProduct (t : ℝ) : ℝ :=
  ∏' j : ℕ, (1 - Real.exp (-(2 ^ j * t)))

/-- The product is the exponential of the log series. -/
theorem lacunaryExpProduct_eq_exp (t : ℝ) (ht : 0 < t) :
    lacunaryExpProduct t =
      Real.exp (∑' j : ℕ, Real.log (1 - Real.exp (-(2 ^ j * t)))) :=
  (Real.rexp_tsum_eq_tprod (fun j => one_sub_exp_neg_two_pow_pos t ht j)
    (summable_log_one_sub_exp t ht)).symm

/-- Positivity: `𝓔(t) > 0` for `t > 0`. -/
theorem lacunaryExpProduct_pos (t : ℝ) (ht : 0 < t) :
    0 < lacunaryExpProduct t := by
  rw [lacunaryExpProduct_eq_exp t ht]
  exact Real.exp_pos _

/-- `𝓔(t) ≤ 1`. -/
theorem lacunaryExpProduct_le_one (t : ℝ) (ht : 0 < t) :
    lacunaryExpProduct t ≤ 1 := by
  rw [lacunaryExpProduct_eq_exp t ht]
  have hsum : (∑' j : ℕ, Real.log (1 - Real.exp (-(2 ^ j * t)))) ≤ 0 :=
    tsum_nonpos fun j =>
      Real.log_nonpos (one_sub_exp_neg_two_pow_pos t ht j).le
        (one_sub_exp_neg_two_pow_le_one t j)
  calc Real.exp (∑' j : ℕ, Real.log (1 - Real.exp (-(2 ^ j * t))))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr hsum
    _ = 1 := Real.exp_zero

/-- **Self-similarity**: peeling the first `m` factors rescales the
argument, `𝓔(t) = (∏_{j<m}(1-e^(-2^j·t)))·𝓔(2^m·t)`. -/
theorem lacunaryExpProduct_eq_prod_mul (t : ℝ) (ht : 0 < t) (m : ℕ) :
    lacunaryExpProduct t =
      (∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t)))) *
        lacunaryExpProduct (2 ^ m * t) := by
  have ht' : 0 < 2 ^ m * t := by positivity
  have hsum := summable_log_one_sub_exp t ht
  have hsplit := hsum.sum_add_tsum_nat_add m
  rw [lacunaryExpProduct_eq_exp t ht, ← hsplit, Real.exp_add,
    Real.exp_sum]
  congr 1
  · exact Finset.prod_congr rfl fun j _ =>
      Real.exp_log (one_sub_exp_neg_two_pow_pos t ht j)
  · rw [lacunaryExpProduct_eq_exp _ ht']
    congr 1
    refine tsum_congr fun j => ?_
    congr 2
    rw [pow_add]
    ring_nf

/-- Monotonicity in the argument. -/
theorem lacunaryExpProduct_mono {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    lacunaryExpProduct t ≤ lacunaryExpProduct s := by
  have hs : 0 < s := lt_of_lt_of_le ht hts
  rw [lacunaryExpProduct_eq_exp t ht, lacunaryExpProduct_eq_exp s hs]
  apply Real.exp_le_exp.mpr
  refine (summable_log_one_sub_exp t ht).tsum_le_tsum
    (fun j => ?_) (summable_log_one_sub_exp s hs)
  apply Real.log_le_log (one_sub_exp_neg_two_pow_pos t ht j)
  have : Real.exp (-(2 ^ j * s)) ≤ Real.exp (-(2 ^ j * t)) := by
    apply Real.exp_le_exp.mpr
    have h2 : (0 : ℝ) < 2 ^ j := by positivity
    nlinarith
  linarith

/-- The finite head is bounded by the pure power
`2^(m(m-1)/2)·t^m`. -/
theorem prod_one_sub_exp_le (t : ℝ) (ht : 0 < t) (m : ℕ) :
    ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))) ≤
      2 ^ (m * (m - 1) / 2) * t ^ m := by
  have hle : ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))) ≤
      ∏ j ∈ range m, (2 ^ j * t) := by
    refine Finset.prod_le_prod (fun j _ =>
      (one_sub_exp_neg_two_pow_pos t ht j).le) (fun j _ => ?_)
    exact one_sub_exp_neg_le (2 ^ j * t)
  refine hle.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, Finset.sum_range_id, Finset.card_range]

/-- **Effective super-polynomial flatness** (upper half of the boxed
asymptotic): `𝓔(t) ≤ 2^(m(m-1)/2)·t^m` for every level `m` and every
`t > 0`. -/
theorem lacunaryExpProduct_le (t : ℝ) (ht : 0 < t) (m : ℕ) :
    lacunaryExpProduct t ≤ 2 ^ (m * (m - 1) / 2) * t ^ m := by
  have ht' : 0 < 2 ^ m * t := by positivity
  rw [lacunaryExpProduct_eq_prod_mul t ht m]
  calc (∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t)))) *
        lacunaryExpProduct (2 ^ m * t)
      ≤ (∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t)))) * 1 := by
        apply mul_le_mul_of_nonneg_left
          (lacunaryExpProduct_le_one _ ht')
        exact Finset.prod_nonneg fun j _ =>
          (one_sub_exp_neg_two_pow_pos t ht j).le
    _ = ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))) := mul_one _
    _ ≤ 2 ^ (m * (m - 1) / 2) * t ^ m := prod_one_sub_exp_le t ht m

/-- **Effective lower bound** (lower half of the boxed asymptotic): at
the matching dyadic level — `1/2 ≤ 2^m·t ≤ 2` — the product is at
least `2^(m(m-1)/2)·(t/2)^m·𝓔(1/2)`. -/
theorem le_lacunaryExpProduct (t : ℝ) (ht : 0 < t) (m : ℕ)
    (hup : 2 ^ m * t ≤ 2) (hlow : 1 / 2 ≤ 2 ^ m * t) :
    2 ^ (m * (m - 1) / 2) * (t / 2) ^ m * lacunaryExpProduct (1 / 2) ≤
      lacunaryExpProduct t := by
  have ht' : 0 < 2 ^ m * t := by positivity
  rw [lacunaryExpProduct_eq_prod_mul t ht m]
  have htail : lacunaryExpProduct (1 / 2) ≤
      lacunaryExpProduct (2 ^ m * t) :=
    lacunaryExpProduct_mono (by norm_num) hlow
  have hhead : 2 ^ (m * (m - 1) / 2) * (t / 2) ^ m ≤
      ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))) := by
    have hfac : ∀ j ∈ range m, 2 ^ j * t / 2 ≤
        1 - Real.exp (-(2 ^ j * t)) := by
      intro j hj
      have hjm := Finset.mem_range.mp hj
      have hx0 : (0 : ℝ) ≤ 2 ^ j * t := by positivity
      have hx1 : 2 ^ j * t ≤ 1 := by
        have hpow : (2 : ℝ) ^ j * 2 ≤ 2 ^ m := by
          have : (2 : ℝ) ^ (j + 1) ≤ 2 ^ m :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          calc (2 : ℝ) ^ j * 2 = 2 ^ (j + 1) := by rw [pow_succ]
            _ ≤ 2 ^ m := this
        nlinarith
      exact half_le_one_sub_exp_neg _ hx0 hx1
    calc 2 ^ (m * (m - 1) / 2) * (t / 2) ^ m
        = ∏ j ∈ range m, (2 ^ j * t / 2) := by
          rw [show (fun j : ℕ => (2:ℝ) ^ j * t / 2) =
            (fun j : ℕ => (2:ℝ) ^ j * (t / 2)) from by
              funext j; ring]
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
            Finset.card_range]
      _ ≤ ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))) := by
          refine Finset.prod_le_prod (fun j _ => by positivity) hfac
  calc 2 ^ (m * (m - 1) / 2) * (t / 2) ^ m * lacunaryExpProduct (1 / 2)
      ≤ (∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t)))) *
          lacunaryExpProduct (2 ^ m * t) := by
        apply mul_le_mul hhead htail
          (lacunaryExpProduct_pos _ (by norm_num)).le
        exact Finset.prod_nonneg fun j _ =>
          (one_sub_exp_neg_two_pow_pos t ht j).le
    _ = _ := rfl

end Fabius
