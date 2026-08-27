import FabiusFunction.FourierProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The baseline decay `‖Φ(x)‖ ≤ 1/(π|x|)`

The audits' trivial-tier decay, kernel-checked: the modulus of the
sinc product is globally at most `1` on the real axis (all factors
are `|sinc| ≤ 1`), and peeling the leading factor from every partial
product gives

`‖Φ(x)‖ ≤ 1/(π|x|)` for every real `x ≠ 0` —

the `κ ≥ 1` baseline against which the whole decay-exponent spectrum
is measured.

* `norm_complexSinc_ofReal_le_one` — `|sinc| ≤ 1` on the reals.
* `norm_rvachevFourierProduct_le_one` — `‖Φ‖ ≤ 1` on the reals.
* `norm_complexSinc_pi_mul_le` — the leading-factor bound.
* `norm_rvachevFourierProduct_le_inv` — **the baseline decay**.
-/

set_option autoImplicit false

open Filter Topology Real

namespace Fabius

/-- Real-argument sinc has modulus at most one. -/
theorem norm_complexSinc_ofReal_le_one (r : ℝ) :
    ‖complexSinc ((r : ℝ) : ℂ)‖ ≤ 1 := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [complexSinc]
  · have hrC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
    rw [complexSinc, if_neg hrC,
      show Complex.sin ((r : ℝ) : ℂ) = ((Real.sin r : ℝ) : ℂ) from
        (Complex.ofReal_sin r).symm,
      show ((Real.sin r : ℝ) : ℂ) / ((r : ℝ) : ℂ) =
        ((Real.sin r / r : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_div]
    rw [div_le_one (abs_pos.mpr hr)]
    exact Real.abs_sin_le_abs

/-- **Global bound on the real axis**: `‖Φ(x)‖ ≤ 1`. -/
theorem norm_rvachevFourierProduct_le_one (x : ℝ) :
    ‖rvachevFourierProduct (x : ℂ)‖ ≤ 1 := by
  have hprod : HasProd
      (fun n : ℕ => complexSinc (Real.pi * (x:ℂ) / 2 ^ n))
      (rvachevFourierProduct (x : ℂ)) :=
    (sincFactors_multipliable _).hasProd
  have hnormProd := hprod.map
    (⟨⟨fun z : ℂ => ‖z‖, norm_one⟩, norm_mul⟩ : ℂ →* ℝ)
    continuous_norm
  have hn1 : HasProd
      (fun n : ℕ => ‖complexSinc (Real.pi * (x:ℂ) / 2 ^ n)‖)
      ‖rvachevFourierProduct (x : ℂ)‖ := hnormProd
  have hfle : ∀ n : ℕ,
      ‖complexSinc (Real.pi * (x:ℂ) / 2 ^ n)‖ ≤ 1 := by
    intro n
    rw [show (Real.pi : ℂ) * (x:ℂ) / 2 ^ n =
      ((π * x / 2 ^ n : ℝ) : ℂ) by push_cast; ring]
    exact norm_complexSinc_ofReal_le_one _
  refine le_of_tendsto hn1 (Filter.Eventually.of_forall fun s => ?_)
  exact Finset.prod_le_one (fun i _ => norm_nonneg _)
    (fun i _ => hfle i)

/-- The leading factor obeys the `1/(π|x|)` bound. -/
theorem norm_complexSinc_pi_mul_le {x : ℝ} (hx : x ≠ 0) :
    ‖complexSinc ((Real.pi : ℂ) * (x:ℂ))‖ ≤ 1 / (π * |x|) := by
  have hπx : (0:ℝ) < π * |x| :=
    mul_pos Real.pi_pos (abs_pos.mpr hx)
  have hne : ((π * x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero Real.pi_ne_zero hx
  rw [show (Real.pi : ℂ) * (x:ℂ) = ((π * x : ℝ) : ℂ) by
      push_cast; ring,
    complexSinc, if_neg hne,
    show Complex.sin ((π * x : ℝ) : ℂ) =
      ((Real.sin (π * x) : ℝ) : ℂ) from
      (Complex.ofReal_sin _).symm,
    show ((Real.sin (π * x) : ℝ) : ℂ) / ((π * x : ℝ) : ℂ) =
      ((Real.sin (π * x) / (π * x) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_div]
  have habs : |π * x| = π * |x| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [habs, div_le_div_iff₀ hπx hπx]
  have hs : |Real.sin (π * x)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have := mul_le_mul_of_nonneg_right hs hπx.le
  linarith

/-- **The baseline decay** (`κ ≥ 1` tier): for real `x ≠ 0`,
`‖Φ(x)‖ ≤ 1/(π|x|)` — peel the leading factor from every partial
product (eventually `0 ∈ s`) and bound the rest by `1`. -/
theorem norm_rvachevFourierProduct_le_inv {x : ℝ} (hx : x ≠ 0) :
    ‖rvachevFourierProduct (x : ℂ)‖ ≤ 1 / (π * |x|) := by
  have hπx : (0:ℝ) < π * |x| :=
    mul_pos Real.pi_pos (abs_pos.mpr hx)
  have hprod : HasProd
      (fun n : ℕ => complexSinc (Real.pi * (x:ℂ) / 2 ^ n))
      (rvachevFourierProduct (x : ℂ)) :=
    (sincFactors_multipliable _).hasProd
  have hnormProd := hprod.map
    (⟨⟨fun z : ℂ => ‖z‖, norm_one⟩, norm_mul⟩ : ℂ →* ℝ)
    continuous_norm
  have hn1 : HasProd
      (fun n : ℕ => ‖complexSinc (Real.pi * (x:ℂ) / 2 ^ n)‖)
      ‖rvachevFourierProduct (x : ℂ)‖ := hnormProd
  have hfle : ∀ n : ℕ,
      ‖complexSinc (Real.pi * (x:ℂ) / 2 ^ n)‖ ≤ 1 := by
    intro n
    rw [show (Real.pi : ℂ) * (x:ℂ) / 2 ^ n =
      ((π * x / 2 ^ n : ℝ) : ℂ) by push_cast; ring]
    exact norm_complexSinc_ofReal_le_one _
  have hf0 : ‖complexSinc (Real.pi * (x:ℂ) / 2 ^ (0:ℕ))‖ ≤
      1 / (π * |x|) := by
    rw [pow_zero, div_one]
    exact norm_complexSinc_pi_mul_le hx
  refine le_of_tendsto hn1 ?_
  filter_upwards [Filter.eventually_ge_atTop ({0} : Finset ℕ)]
    with s hs
  have h0s : (0:ℕ) ∈ s := hs (Finset.mem_singleton_self 0)
  rw [← Finset.mul_prod_erase s _ h0s]
  have hrest : ∏ i ∈ s.erase 0,
      ‖complexSinc (Real.pi * (x:ℂ) / 2 ^ i)‖ ≤ 1 :=
    Finset.prod_le_one (fun i _ => norm_nonneg _)
      (fun i _ => hfle i)
  calc ‖complexSinc (Real.pi * (x:ℂ) / 2 ^ (0:ℕ))‖ *
      ∏ i ∈ s.erase 0, ‖complexSinc (Real.pi * (x:ℂ) / 2 ^ i)‖ ≤
      (1 / (π * |x|)) * 1 :=
        mul_le_mul hf0 hrest
          (Finset.prod_nonneg (fun i _ => norm_nonneg _))
          (one_div_pos.mpr hπx).le
    _ = 1 / (π * |x|) := mul_one _

end Fabius
