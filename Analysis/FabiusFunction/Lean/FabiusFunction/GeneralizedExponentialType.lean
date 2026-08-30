import FabiusFunction.GeneralizedRvachevProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# `Φ_a` has exponential type at most `2π R_a`

The exponents volume defines the support radius by
`R_a = (1/2) A_a(1/2) = (1/2) ∑_h a_h 2^{-h}`.  The corpus has this
number (`NewtonBasisGeneratingFunction` computes its Newton-weight
specialization) but does not identify it as the support radius of a
formalized probability law; that identification would require the
volume's support theorem for the associated random variable.

Half of that is analytic and needs no probability at all.  In the
`e^{-2πixt}` convention, Paley–Wiener associates support in `[-R, R]`
with exponential type at most `2π R`.  In the normalization
`sinc(π z / 2^h)` used here, this is
`2π R_a = π A_a(1/2)`.  That growth bound is proved directly from
the product:

`‖Φ_a(z)‖ ≤ exp (π ‖z‖ A_a(1/2)) = exp (2π ‖z‖ R_a)`
for every `z : ℂ`.

Together with the separately proved entirety of `Φ_a`, this gives
order at most `1` and type at most `2π R_a`.  What is *not* proved is
the converse — that the type is not smaller, and that the law is
supported on `[-R_a, R_a]` — which does need the probabilistic side.

The estimate rests on one sharp inequality, and sharpness matters:
any constant `C > 1` in `‖sinc w‖ ≤ C e^{‖w‖}` would compound to
`C^{∑ a_h}` across the factors and diverge.  The bound with constant
`1` comes from the sine series compared termwise against the
hyperbolic sine,

`‖sin w‖ ≤ sinh ‖w‖ ≤ ‖w‖ e^{‖w‖}`,

the second step being `1 - 2t ≤ e^{-2t}` — Mathlib's
`Real.add_one_le_exp` — rearranged.

* `Fabius.sinh_le_mul_exp` — `sinh t ≤ t e^t` for `t ≥ 0`;
* `Fabius.norm_sin_le_sinh_norm` — `‖sin w‖ ≤ sinh ‖w‖`;
* `Fabius.norm_complexSinc_le_exp_norm` — **the sharp factor bound**
  `‖sinc w‖ ≤ e^{‖w‖}`;
* `Fabius.prod_norm_generalizedSincFactor_le` — the finite stage;
* `Fabius.norm_generalizedRvachevProduct_le_exp` — **the type
  bound**.
-/

set_option autoImplicit false

open Filter Topology

namespace Fabius

/-! ## The sharp factor bound -/

/-- `sinh t ≤ t · exp t` for `t ≥ 0`.

Multiplying `1 - 2t ≤ e^{-2t}` (`Real.add_one_le_exp`) by `e^{2t} > 0`
gives `e^{2t} - 1 ≤ 2t e^{2t}`, which is the claim after halving and
dividing by `e^t`. -/
theorem sinh_le_mul_exp {t : ℝ} (ht : 0 ≤ t) :
    Real.sinh t ≤ t * Real.exp t := by
  have hE : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hkey : 1 + -(2 * t) ≤ Real.exp (-(2 * t)) :=
    Real.add_one_le_exp _ |>.trans_eq' (by ring)
  have hinv : Real.exp (-(2 * t)) * Real.exp (2 * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsq : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [← Real.exp_add]
    ring_nf
  have hpos : (0 : ℝ) < Real.exp (2 * t) := Real.exp_pos _
  rw [Real.sinh_eq, Real.exp_neg]
  have hmul : (1 + -(2 * t)) * Real.exp (2 * t) ≤ 1 := by
    calc (1 + -(2 * t)) * Real.exp (2 * t)
        ≤ Real.exp (-(2 * t)) * Real.exp (2 * t) :=
          mul_le_mul_of_nonneg_right hkey hpos.le
      _ = 1 := hinv
  rw [hsq] at hmul
  have hne : Real.exp t ≠ 0 := ne_of_gt hE
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  field_simp
  nlinarith [hE, hmul, sq_nonneg (Real.exp t)]

/-- `‖sin w‖ ≤ sinh ‖w‖`: the sine series bounded termwise by the
hyperbolic sine series, whose terms are the norms of the sine's. -/
theorem norm_sin_le_sinh_norm (w : ℂ) :
    ‖Complex.sin w‖ ≤ Real.sinh ‖w‖ := by
  refine (Complex.hasSum_sin w).norm_le_of_bounded
    (Real.hasSum_sinh ‖w‖) fun n => ?_
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_natCast]

/-- **The factor bound, with constant one.**  `‖sinc w‖ ≤ e^{‖w‖}`.

The constant matters: anything larger compounds to `C^{∑ a_h}` across
the factors of `Φ_a` and diverges whenever the weight has infinite
total mass. -/
theorem norm_complexSinc_le_exp_norm (w : ℂ) :
    ‖complexSinc w‖ ≤ Real.exp ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [complexSinc]
  · have hpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    rw [complexSinc, if_neg hw, norm_div, div_le_iff₀ hpos]
    calc ‖Complex.sin w‖ ≤ Real.sinh ‖w‖ := norm_sin_le_sinh_norm w
      _ ≤ ‖w‖ * Real.exp ‖w‖ := sinh_le_mul_exp hpos.le
      _ = Real.exp ‖w‖ * ‖w‖ := by ring

/-! ## The type bound -/

/-- Every finite product of factor norms is bounded by
`exp (π ‖z‖ A_a(1/2))`, equivalently `exp (2π ‖z‖ R_a)`: the
exponents add, and the partial weight sum is below the total. -/
theorem prod_norm_generalizedSincFactor_le (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (z : ℂ)
    (s : Finset ℕ) :
    ∏ h ∈ s, ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h‖
      ≤ Real.exp (Real.pi * ‖z‖ * ∑' h : ℕ, (a h : ℝ) / 2 ^ h) := by
  have hterm : ∀ h ∈ s,
      ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h‖
        ≤ Real.exp (Real.pi * ‖z‖ * ((a h : ℝ) / 2 ^ h)) := by
    intro h _
    have harg : ‖(Real.pi : ℂ) * z / (2 : ℂ) ^ h‖
        = Real.pi * ‖z‖ / 2 ^ h := by
      rw [norm_div, norm_mul, norm_pow]
      simp [Real.pi_nonneg, abs_of_nonneg Real.pi_nonneg]
    rw [norm_pow]
    calc ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h)‖ ^ a h
        ≤ (Real.exp ‖(Real.pi : ℂ) * z / (2 : ℂ) ^ h‖) ^ a h :=
          pow_le_pow_left₀ (norm_nonneg _)
            (norm_complexSinc_le_exp_norm _) _
      _ = Real.exp ((a h : ℝ) * ‖(Real.pi : ℂ) * z / (2 : ℂ) ^ h‖) := by
          rw [← Real.exp_nat_mul]
      _ = Real.exp (Real.pi * ‖z‖ * ((a h : ℝ) / 2 ^ h)) := by
          rw [harg]
          congr 1
          ring
  refine (Finset.prod_le_prod (fun h _ => norm_nonneg _) hterm).trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact ha.sum_le_tsum s fun h _ => by positivity

/-- **`Φ_a` is of exponential type at most `2π R_a`, equivalently
`π A_a(1/2)`.**

`‖Φ_a(z)‖ ≤ exp (π ‖z‖ · ∑_h a_h 2^{-h})`.

Here the volume's support-radius notation is
`R_a = (1/2) ∑_h a_h 2^{-h}`.  Together with the separately proved
entirety of `Φ_a`, the estimate gives order at most one with the
Paley–Wiener constant predicted by that radius.  The converse half,
that the law really is supported there, is not addressed. -/
theorem norm_generalizedRvachevProduct_le_exp (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (z : ℂ) :
    ‖generalizedRvachevProduct a z‖
      ≤ Real.exp (Real.pi * ‖z‖ * ∑' h : ℕ, (a h : ℝ) / 2 ^ h) := by
  have hprod : HasProd
      (fun h : ℕ => complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h)
      (generalizedRvachevProduct a z) := by
    rw [generalizedRvachevProduct]
    exact (generalizedSincFactors_multipliable a ha z).hasProd
  refine le_of_tendsto hprod.norm ?_
  exact Eventually.of_forall
    (prod_norm_generalizedSincFactor_le a ha z)

end Fabius
