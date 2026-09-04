import FabiusFunction.BasicBernoulliLog
import FabiusFunction.LambertWGapBijection
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Bernoulli series for the real Lambert branch gap

On the common real domain of the two Lambert branches, write
`Delta = branchGap x = W0(x) - W-1(x)`.  The exact gap formulas identify
`W0(x)` with `-Delta / (exp Delta - 1)` and `W-1(x)` with `W0(x) - Delta`.
This module evaluates the Bernoulli exponential generating series on the
open disk needed by those formulas and proves that its complex convergence
radius is exactly `2*pi`:

`sum_n B_n z^n / n! = z / (exp z - 1)`, for `z ≠ 0` and `|z| < 2*pi`.

Indeed, the series is summable for complex `z` exactly when `‖z‖ < 2*pi`.
At and outside the boundary, its positive even terms do not tend to zero.

The value at `z = 0` is deliberately excluded from the quotient statement:
the series has removable value `1`, whereas division in Lean totalizes
`0 / (exp 0 - 1)` to `0`.  Likewise the Lambert wrapper remains on the
strict two-branch domain and assumes `branchGap x < 2*pi`.

The convergence proof reuses the even-zeta majorant behind
`BasicBernoulliLog`.  The evaluation itself is coefficientwise: Mathlib's
formal identity `bernoulliPowerSeries_mul_exp_sub_one` is transported through
an absolutely convergent Cauchy product.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Fabius

noncomputable section

private theorem bernoulli_even_term_eq_logCoeff (z : ℝ) (r : ℕ) :
    (bernoulli (2 * (r + 1)) : ℝ) * z ^ (2 * (r + 1)) /
        ((2 * (r + 1)).factorial : ℝ) =
      (2 * ((r : ℝ) + 1)) *
        ((bernoulliLogCoeff r : ℝ) * z ^ (2 * (r + 1))) := by
  rw [ofReal_bernoulliLogCoeff]
  have hr : (2 : ℝ) * ((r : ℝ) + 1) ≠ 0 := by positivity
  have hf : (((2 * (r + 1)).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

private theorem norm_bernoulli_egf_term_le (z : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ‖(bernoulli n : ℝ) * z ^ n / (n.factorial : ℝ)‖ ≤
      (n : ℝ) * (Real.pi ^ 2 / 6) * (|z| / (2 * Real.pi)) ^ n := by
  rcases Nat.even_or_odd' n with ⟨r, rfl | rfl⟩
  · have hr : r ≠ 0 := by omega
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    rw [bernoulli_even_term_eq_logCoeff]
    have hbound := norm_bernoulliLogTerm_le ((z : ℝ) : ℂ) s
    have hbound_real :
        ‖(bernoulliLogCoeff s : ℝ) * z ^ (2 * (s + 1))‖ ≤
          Real.pi ^ 2 / 6 * (|z| / (2 * Real.pi)) ^ (2 * (s + 1)) := by
      simpa only [norm_mul, norm_pow, Complex.norm_ratCast, Complex.norm_real,
        Real.norm_eq_abs] using hbound
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    have hfactor : (0 : ℝ) ≤ 2 * ((s : ℝ) + 1) := by positivity
    rw [norm_mul, Real.norm_of_nonneg hfactor]
    have hmul := mul_le_mul_of_nonneg_left hbound_real hfactor
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.succ_eq_add_one,
      mul_assoc] using hmul
  · have hr : r ≠ 0 := by omega
    have hodd : Odd (2 * r + 1) := odd_two_mul_add_one r
    have hgt : 1 < 2 * r + 1 := by omega
    rw [bernoulli_eq_zero_of_odd hodd hgt]
    norm_num
    positivity

/-- The Bernoulli exponential generating series converges absolutely for
every real `z` with `|z| < 2*pi`. -/
theorem summable_norm_bernoulli_mul_pow_div_factorial {z : ℝ}
    (hz : |z| < 2 * Real.pi) :
    Summable fun n : ℕ =>
      ‖(bernoulli n : ℝ) * z ^ n / (n.factorial : ℝ)‖ := by
  have hpi : 0 < 2 * Real.pi := by positivity
  let q : ℝ := |z| / (2 * Real.pi)
  have hq0 : 0 ≤ q := div_nonneg (abs_nonneg z) hpi.le
  have hq1 : q < 1 := (div_lt_one hpi).2 hz
  have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hmajorant : Summable fun n : ℕ =>
      (n : ℝ) * (Real.pi ^ 2 / 6) * q ^ n := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm
    refine (h.mul_right (Real.pi ^ 2 / 6)).congr fun n => ?_
    simp only [pow_one]
    ring
  refine Summable.of_norm_bounded_eventually_nat hmajorant ?_
  filter_upwards [Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩] with n hn
  simp only [norm_norm]
  simpa only [q] using norm_bernoulli_egf_term_le z hn

private theorem one_le_evenZeta_succ (r : ℕ) :
    (1 : ℝ) ≤ evenZeta (r + 1) := by
  have hzero :
      (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * (r + 1))) 0 = 1 := by
    norm_num
  have hle :
      (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * (r + 1))) 0 ≤
        evenZeta (r + 1) :=
    Summable.le_tsum (summable_one_div_add_one_pow (by omega)) 0
      (fun n _ => by positivity)
  rwa [hzero] at hle

private theorem norm_bernoulli_complex_egf_term_eq_real (z : ℂ) (n : ℕ) :
    ‖(bernoulli n : ℂ) * z ^ n / (n.factorial : ℂ)‖ =
      ‖(bernoulli n : ℝ) * ‖z‖ ^ n / (n.factorial : ℝ)‖ := by
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_ratCast,
    Complex.norm_natCast, Real.norm_eq_abs, abs_norm]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (n.factorial : ℝ) by positivity)]

private theorem norm_bernoulli_even_egf_term (z : ℂ) (r : ℕ) :
    ‖(bernoulli (2 * (r + 1)) : ℂ) * z ^ (2 * (r + 1)) /
        ((2 * (r + 1)).factorial : ℂ)‖ =
      2 * evenZeta (r + 1) *
        (‖z‖ / (2 * Real.pi)) ^ (2 * (r + 1)) := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hfactor_pos :
      0 < ((r : ℝ) + 1) * (2 * Real.pi) ^ (2 * (r + 1)) := by
    positivity
  have hsign : |(-1 : ℝ) ^ r| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have hzeta :
      |(bernoulliLogCoeff r : ℝ)| *
          (((r : ℝ) + 1) * (2 * Real.pi) ^ (2 * (r + 1))) =
        evenZeta (r + 1) := by
    have habs :
        |evenZeta (r + 1)| =
          |(bernoulliLogCoeff r : ℝ)| *
            (((r : ℝ) + 1) * (2 * Real.pi) ^ (2 * (r + 1))) := by
      rw [evenZeta_eq_bernoulliLogCoeff r, abs_mul, abs_mul, hsign, one_mul,
        abs_of_pos hfactor_pos]
    rw [← habs]
    exact abs_of_pos (evenZeta_pos (by omega))
  calc
    ‖(bernoulli (2 * (r + 1)) : ℂ) * z ^ (2 * (r + 1)) /
        ((2 * (r + 1)).factorial : ℂ)‖ =
        ‖(bernoulli (2 * (r + 1)) : ℝ) * ‖z‖ ^ (2 * (r + 1)) /
          ((2 * (r + 1)).factorial : ℝ)‖ := by
      exact norm_bernoulli_complex_egf_term_eq_real z (2 * (r + 1))
    _ = ‖(2 * ((r : ℝ) + 1)) *
        ((bernoulliLogCoeff r : ℝ) * ‖z‖ ^ (2 * (r + 1)))‖ := by
      rw [bernoulli_even_term_eq_logCoeff]
    _ = 2 * ((r : ℝ) + 1) * |(bernoulliLogCoeff r : ℝ)| *
        ‖z‖ ^ (2 * (r + 1)) := by
      rw [norm_mul, Real.norm_of_nonneg (by positivity), norm_mul,
        Real.norm_eq_abs, norm_pow, Real.norm_eq_abs, abs_norm]
      ring
    _ = 2 *
        (|(bernoulliLogCoeff r : ℝ)| *
          (((r : ℝ) + 1) * (2 * Real.pi) ^ (2 * (r + 1)))) *
        (‖z‖ / (2 * Real.pi)) ^ (2 * (r + 1)) := by
      rw [div_pow]
      field_simp [hpi]
    _ = 2 * evenZeta (r + 1) *
        (‖z‖ / (2 * Real.pi)) ^ (2 * (r + 1)) := by
      rw [hzeta]

/-- The complex Bernoulli exponential generating series has exact convergence
radius `2*pi`: it is summable exactly on the open disk `‖z‖ < 2*pi`, and in
particular diverges at every point of its boundary circle. -/
theorem summable_bernoulli_mul_pow_div_factorial_iff (z : ℂ) :
    Summable (fun n : ℕ =>
      (bernoulli n : ℂ) * z ^ n / (n.factorial : ℂ)) ↔
      ‖z‖ < 2 * Real.pi := by
  rw [← summable_norm_iff (E := ℂ)]
  constructor
  · intro hsum
    by_contra! hz
    have hinj : Function.Injective (fun r : ℕ => 2 * (r + 1)) := by
      intro a b hab
      exact Nat.add_right_cancel
        (Nat.mul_left_cancel (by omega : 0 < 2) hab)
    have ht := (hsum.comp_injective hinj).tendsto_atTop_zero
    change Filter.Tendsto (fun r : ℕ =>
        ‖(bernoulli (2 * (r + 1)) : ℂ) * z ^ (2 * (r + 1)) /
          ((2 * (r + 1)).factorial : ℂ)‖) Filter.atTop (nhds 0) at ht
    have hsmall : ∀ᶠ r : ℕ in Filter.atTop,
        ‖(bernoulli (2 * (r + 1)) : ℂ) * z ^ (2 * (r + 1)) /
          ((2 * (r + 1)).factorial : ℂ)‖ < 1 :=
      (tendsto_order.1 ht).2 1 zero_lt_one
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
    have hq : 1 ≤ ‖z‖ / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      simpa using hz
    have hlower :
        (2 : ℝ) ≤
          ‖(bernoulli (2 * (N + 1)) : ℂ) * z ^ (2 * (N + 1)) /
            ((2 * (N + 1)).factorial : ℂ)‖ := by
      rw [norm_bernoulli_even_egf_term]
      calc
        (2 : ℝ) = 2 * 1 * 1 := by ring
        _ ≤ 2 * evenZeta (N + 1) *
            (‖z‖ / (2 * Real.pi)) ^ (2 * (N + 1)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (one_le_evenZeta_succ N) (by norm_num))
            (one_le_pow₀ hq) (by norm_num)
            (mul_nonneg (by norm_num) (evenZeta_pos (by omega)).le)
    linarith [hN N le_rfl]
  · intro hz
    have hzreal : |‖z‖| < 2 * Real.pi := by
      simpa only [abs_norm] using hz
    have hreal := summable_norm_bernoulli_mul_pow_div_factorial hzreal
    exact hreal.congr fun n =>
      (norm_bernoulli_complex_egf_term_eq_real z n).symm

/-- For nonzero real `z` in the open disk of radius `2*pi`, the Bernoulli
exponential generating series has sum `z / (exp z - 1)`.  The nonzero
hypothesis keeps the removable value at the origin explicit. -/
theorem hasSum_bernoulli_mul_pow_div_factorial {z : ℝ} (hz0 : z ≠ 0)
    (hz : |z| < 2 * Real.pi) :
    HasSum (fun n : ℕ => (bernoulli n : ℝ) * z ^ n / (n.factorial : ℝ))
      (z / (Real.exp z - 1)) := by
  let b : ℕ → ℝ := fun n => (bernoulli n : ℝ) / (n.factorial : ℝ)
  let c : ℕ → ℝ := fun n =>
    PowerSeries.coeff n (PowerSeries.exp ℝ - 1)
  let f : ℕ → ℝ := fun n => b n * z ^ n
  let g : ℕ → ℝ := fun n => c n * z ^ n
  have hf_norm : Summable fun n => ‖f n‖ := by
    refine (summable_norm_bernoulli_mul_pow_div_factorial hz).congr fun n => ?_
    congr 1
    simp only [f, b]
    ring
  have hg_eq (n : ℕ) : g n = z ^ n / (n.factorial : ℝ) - if n = 0 then 1 else 0 := by
    by_cases hn : n = 0
    · subst n
      simp [g, c]
    · simp [g, c, hn]
      ring
  have hg : Summable g := by
    have hdelta : Summable (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) :=
      (hasSum_ite_eq 0 (1 : ℝ)).summable
    exact ((NormedSpace.expSeries_div_summable z).sub hdelta).congr
      (fun n => (hg_eq n).symm)
  have hg_norm : Summable fun n => ‖g n‖ := hg.norm
  have hgf : (∑' n, g n) = Real.exp z - 1 := by
    calc
      (∑' n, g n) =
          ∑' n : ℕ, (z ^ n / (n.factorial : ℝ) - if n = 0 then 1 else 0) :=
        tsum_congr hg_eq
      _ = (∑' n : ℕ, z ^ n / (n.factorial : ℝ)) -
          ∑' n : ℕ, if n = 0 then 1 else 0 :=
        (NormedSpace.expSeries_div_summable z).tsum_sub
          (hasSum_ite_eq 0 (1 : ℝ)).summable
      _ = NormedSpace.exp z - 1 := by
        rw [(NormedSpace.expSeries_div_hasSum_exp z).tsum_eq,
          (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq]
      _ = Real.exp z - 1 := by rw [Real.exp_eq_exp_ℝ]
  have hcoeff (n : ℕ) :
      ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 =
        PowerSeries.coeff n PowerSeries.X * z ^ n := by
    calc
      ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 =
          (∑ ij ∈ Finset.antidiagonal n, b ij.1 * c ij.2) * z ^ n := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro ij hij
            rw [Finset.mem_antidiagonal] at hij
            simp only [f, g]
            rw [← hij, pow_add]
            ring
      _ = PowerSeries.coeff n
            (bernoulliPowerSeries ℝ * (PowerSeries.exp ℝ - 1)) * z ^ n := by
          rw [PowerSeries.coeff_mul]
          apply congrArg (fun y : ℝ => y * z ^ n)
          apply Finset.sum_congr rfl
          intro ij _hij
          simp [b, c, bernoulliPowerSeries]
      _ = PowerSeries.coeff n PowerSeries.X * z ^ n := by
          rw [bernoulliPowerSeries_mul_exp_sub_one]
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    hf_norm hg_norm
  have hconv : (∑' n, f n) * (Real.exp z - 1) = z := by
    rw [← hgf, hprod, tsum_congr hcoeff]
    calc
      (∑' n : ℕ, PowerSeries.coeff n PowerSeries.X * z ^ n) =
          ∑' n : ℕ, if n = 1 then z else 0 := by
        apply tsum_congr
        intro n
        by_cases hn : n = 1
        · subst n
          simp
        · simp [PowerSeries.coeff_X, hn]
      _ = z := (hasSum_ite_eq 1 z).tsum_eq
  have hden : Real.exp z - 1 ≠ 0 := sub_ne_zero.mpr
    (by simpa using Real.exp_injective.ne hz0)
  have hsum : (∑' n, f n) = z / (Real.exp z - 1) :=
    (eq_div_iff hden).2 hconv
  rw [← hsum]
  refine hf_norm.of_norm.hasSum.congr_fun fun n => ?_
  simp only [f, b]
  ring

/-- On the strict common real domain, if the positive branch gap is below
`2*pi`, both Lambert branches are the Bernoulli series printed in the guide:
`W0 = -sum B_n Delta^n/n!` and
`W-1 = -Delta - sum B_n Delta^n/n!`. -/
theorem principalLambertW_lowerLambertW_eq_bernoulliSeries {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) (hgap : branchGap x < 2 * Real.pi) :
    principalLambertW x =
        -∑' n : ℕ, (bernoulli n : ℝ) * branchGap x ^ n / (n.factorial : ℝ) ∧
      lowerLambertW x = -branchGap x -
        ∑' n : ℕ, (bernoulli n : ℝ) * branchGap x ^ n / (n.factorial : ℝ) := by
  have hgap0 : 0 < branchGap x := by
    simpa only [branchGap] using principalLambertW_sub_lowerLambertW_pos hx
  have habs : |branchGap x| < 2 * Real.pi := by
    rwa [abs_of_pos hgap0]
  have hsum := (hasSum_bernoulli_mul_pow_div_factorial hgap0.ne' habs).tsum_eq
  have hprincipal := principalLambertW_eq_neg_gap_div hx
  have hfirst : principalLambertW x =
      -∑' n : ℕ, (bernoulli n : ℝ) * branchGap x ^ n / (n.factorial : ℝ) := by
    calc
      principalLambertW x = -branchGap x / (Real.exp (branchGap x) - 1) := hprincipal
      _ = -(branchGap x / (Real.exp (branchGap x) - 1)) := by ring
      _ = -∑' n : ℕ,
          (bernoulli n : ℝ) * branchGap x ^ n / (n.factorial : ℝ) := by rw [hsum]
  have hfirst' : principalLambertW x =
      -∑' n : ℕ, (bernoulli n : ℝ) *
        (principalLambertW x - lowerLambertW x) ^ n / (n.factorial : ℝ) := by
    simpa only [branchGap] using hfirst
  constructor
  · exact hfirst
  · simp only [branchGap]
    linarith [hfirst']

end

end Fabius
