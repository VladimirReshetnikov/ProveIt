import FabiusFunction.FrullaniIntegral
import FabiusFunction.ThueMorseBasicLemmas
import FabiusFunction.ReciprocalGammaJets
import FabiusFunction.ThueMorseEntireContinuation
import FabiusFunction.ThueMorseMasterProduct

/-!
# The derivative bridge `log G(a,b) = D'(0,b) - D'(0,a)`

The atlas's corollary `cor:G-Dirichlet`, in full: the logarithm of the
master product is the difference of derivatives *at `s = 0`* of the
entire continuations of the shifted Dirichlet series.

The proof here is Fubini-free and uses no uniform summation-by-parts:

1. **Frullani per term.**  Each term of the master log-series is a
   Frullani integral:
   `ε(n)·log((n+a)/(n+b)) = ε(n)·∫₀^∞ (e^(-(n+b)t) - e^(-(n+a)t))/t dt`.
2. **Dyadic partial sums are finite products.**  Summing `n < 2^m`
   and factoring `e^(-nt)` collapses the signed sum to
   `∏_{j<m}(1 - e^(-2^j t))` — the *finite* lacunary product, which
   lies in `[0,1]`.  That collapse is
   `sum_range_two_pow_thueMorseSign_exp` (`ThueMorseInfiniteProduct`),
   and its convergence is `multipliable_one_sub_exp_neg_two_pow`
   (`ThueMorseBoundaryFlatness`).  A single dominated-convergence pass
   (dominator `|a-b|·e^(-min t)`) then evaluates the limit:
   `L(a,b) = ∫₀^∞ ((e^(-bt) - e^(-at))/t)·𝓔(t) dt`.
3. **The Γ-factor differentiates to `1` at `0`.**  From
   `Γ(s)⁻¹ = s·Γ(s+1)⁻¹` (an identity of entire functions), the
   product rule gives `d/ds Γ(s)⁻¹·M(s)|₀ = M(0)` — the Mellin
   integral at `s = 0`, which converges because boundary flatness
   kills the `1/t`.  Subtracting the two parameters recovers the
   integral of step 2.

* `mpLimit_eq_integral` — **the closed integral form of `log G`**.
* `hasDerivAt_Gamma_inv_zero` — `(1/Γ)'(0) = 1`, re-exported from
  `ReciprocalGammaJets`, which proves the corresponding formula at every
  nonpositive integer.
* `hasDerivAt_dirichletMellinContinuation_zero` — the derivative of
  the continuation at `0` is the Mellin value `M(0)`.
* `mpLimit_eq_deriv_sub` — **the derivative bridge**
  (`cor:G-Dirichlet`).
-/

set_option autoImplicit false

open Finset Filter MeasureTheory Set Complex Topology

namespace Fabius

/-- **Dyadic partial sums of the master log-series as integrals**:
termwise Frullani plus the finite product identity
`sum_range_two_pow_thueMorseSign_exp`. -/
private theorem mpLog_pow_eq_integral (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (m : ℕ) :
    mpLog a b (2 ^ m) =
      ∫ t in Ioi (0 : ℝ),
        (Real.exp (-(b * t)) - Real.exp (-(a * t))) / t *
          ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))) := by
  have hterm : ∀ n : ℕ,
      (thueMorseSign n : ℝ) *
        Real.log (((n : ℝ) + a) / ((n : ℝ) + b)) =
      ∫ t in Ioi (0 : ℝ), (thueMorseSign n : ℝ) *
        ((Real.exp (-(((n : ℝ) + b) * t)) -
          Real.exp (-(((n : ℝ) + a) * t))) / t) := by
    intro n
    rw [MeasureTheory.integral_const_mul,
      frullani_exp (by positivity) (by positivity)]
  have hint : ∀ n ∈ range (2 ^ m), Integrable
      (fun t => (thueMorseSign n : ℝ) *
        ((Real.exp (-(((n : ℝ) + b) * t)) -
          Real.exp (-(((n : ℝ) + a) * t))) / t))
      (volume.restrict (Ioi 0)) := fun n _ =>
    (frullani_integrableOn (by positivity) (by positivity)).const_mul _
  rw [mpLog, Finset.sum_congr rfl fun n _ => hterm n,
    ← MeasureTheory.integral_finsetSum _ hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hsplit : ∀ (n : ℕ) (c : ℝ),
      Real.exp (-(((n : ℝ) + c) * t)) =
      Real.exp (-((n : ℝ) * t)) * Real.exp (-(c * t)) := by
    intro n c
    rw [← Real.exp_add]
    congr 1
    ring
  calc ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℝ) *
        ((Real.exp (-(((n : ℝ) + b) * t)) -
          Real.exp (-(((n : ℝ) + a) * t))) / t)
      = (Real.exp (-(b * t)) - Real.exp (-(a * t))) / t *
          ∑ n ∈ range (2 ^ m),
            (thueMorseSign n : ℝ) * Real.exp (-((n : ℝ) * t)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hsplit n b, hsplit n a]
        ring
    _ = _ := by rw [sum_range_two_pow_thueMorseSign_exp t m]

/-- **The closed integral form of the master limit**
(`cor:G-Dirichlet`, integral step):
`L(a,b) = ∫₀^∞ ((e^(-bt) - e^(-at))/t)·𝓔(t) dt`.  The conditionally
convergent series is exchanged with the integral by dominated
convergence alone, because its dyadic partial sums are the finite
lacunary products, trapped in `[0,1]`. -/
theorem mpLimit_eq_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    mpLimit a b =
      ∫ t in Ioi (0 : ℝ),
        (Real.exp (-(b * t)) - Real.exp (-(a * t))) / t *
          lacunaryExpProduct t := by
  have hpow : Tendsto (fun m : ℕ => 2 ^ m) atTop atTop :=
    tendsto_two_pow_atTop
  have h1 : Tendsto (fun m => mpLog a b (2 ^ m)) atTop
      (𝓝 (mpLimit a b)) := (tendsto_mpLimit a b ha hb).comp hpow
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun (m : ℕ) (t : ℝ) =>
      (Real.exp (-(b * t)) - Real.exp (-(a * t))) / t *
        ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))))
    (f := fun t =>
      (Real.exp (-(b * t)) - Real.exp (-(a * t))) / t *
        lacunaryExpProduct t)
    (μ := volume.restrict (Ioi 0))
    (fun t => |a - b| * Real.exp (-min b a * t)) ?_ ?_ ?_ ?_
  · exact tendsto_nhds_unique h1
      (Tendsto.congr
        (fun m => (mpLog_pow_eq_integral a b ha hb m).symm) hDCT)
  · intro m
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (frullani_continuousOn b a).mul ?_
    exact (continuous_finsetProd _ fun j _ =>
      continuous_const.sub (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg)).continuousOn
  · exact (exp_neg_integrableOn_Ioi 0 (lt_min hb ha)).const_mul _
  · intro m
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hfac : ∀ j ∈ range m,
        (0 : ℝ) ≤ 1 - Real.exp (-(2 ^ j * t)) := by
      intro j _
      have : Real.exp (-(2 ^ j * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      linarith
    have hP0 : (0 : ℝ) ≤
        ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))) :=
      Finset.prod_nonneg hfac
    have hP1 : ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))) ≤ 1 :=
      Finset.prod_le_one hfac fun j _ =>
        sub_le_self 1 (Real.exp_pos _).le
    have habs : |(Real.exp (-(b * t)) - Real.exp (-(a * t))) / t| ≤
        |a - b| * Real.exp (-min b a * t) := by
      rw [show -min b a * t = -(min b a * t) by ring]
      exact frullani_integrand_abs_le b a t ht0
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hP0]
    calc |(Real.exp (-(b * t)) - Real.exp (-(a * t))) / t| *
          ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t)))
        ≤ |a - b| * Real.exp (-min b a * t) * 1 :=
          mul_le_mul habs hP1 hP0 (by positivity)
      _ = |a - b| * Real.exp (-min b a * t) := mul_one _
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hmult := multipliable_one_sub_exp_neg_two_pow t ht0
    exact (hmult.hasProd.tendsto_prod_nat).const_mul _

/-- The Mellin kernel divided by `t` is integrable on `(0,∞)`:
boundary flatness gives `𝓔(t) ≤ t`, so `e^(-at)` dominates. -/
private theorem integrableOn_kernel_div (a : ℝ) (ha : 0 < a) :
    IntegrableOn
      (fun t => Real.exp (-(a * t)) * lacunaryExpProduct t / t)
      (Ioi (0 : ℝ)) := by
  have hdom : IntegrableOn (fun t => Real.exp (-a * t))
      (Ioi (0 : ℝ)) := exp_neg_integrableOn_Ioi 0 ha
  refine Integrable.mono hdom ?_ ?_
  · have h1 : AEStronglyMeasurable (mellinKernel a)
        (volume.restrict (Ioi 0)) :=
      (mellinKernel_locallyIntegrable a).aestronglyMeasurable
    have h2 : AEStronglyMeasurable
        (fun t => Real.exp (-(a * t)) * lacunaryExpProduct t)
        (volume.restrict (Ioi 0)) := by
      refine (Complex.continuous_re.comp_aestronglyMeasurable
        h1).congr (Filter.Eventually.of_forall fun t => ?_)
      simp only [mellinKernel, Complex.ofReal_re]
    have h4 : AEStronglyMeasurable (fun t : ℝ => t⁻¹)
        (volume.restrict (Ioi 0)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.mono continuousOn_inv₀ fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx
      simpa using hx0.ne'
    refine (h2.mul h4).congr
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]
    rw [← div_eq_mul_inv]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hE0 : 0 < lacunaryExpProduct t := lacunaryExpProduct_pos t ht0
    have hEt : lacunaryExpProduct t ≤ t := by
      have h := lacunaryExpProduct_le t ht0 1
      simpa using h
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (div_pos (mul_pos (Real.exp_pos _) hE0) ht0),
      abs_of_pos (Real.exp_pos _),
      show -a * t = -(a * t) by ring]
    have hq : lacunaryExpProduct t / t ≤ 1 := (div_le_one ht0).mpr hEt
    calc Real.exp (-(a * t)) * lacunaryExpProduct t / t
        = Real.exp (-(a * t)) * (lacunaryExpProduct t / t) := by ring
      _ ≤ Real.exp (-(a * t)) * 1 :=
          mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
      _ = Real.exp (-(a * t)) := mul_one _

/-- The Mellin transform of the kernel at `s = 0` is the real
integral `∫₀^∞ e^(-at)·𝓔(t)/t dt`.  Like `mellin_mellinKernel_ofReal`,
of which it is the `σ = 0` case, this is a cast identity only and holds
for every real `a`; that the integral genuinely converges for `a > 0` —
boundary flatness absorbing the `1/t` — is `integrableOn_kernel_div`. -/
private theorem mellin_mellinKernel_zero (a : ℝ) :
    mellin (mellinKernel a) 0 =
      ((∫ t in Ioi (0 : ℝ),
        Real.exp (-(a * t)) * lacunaryExpProduct t / t : ℝ) : ℂ) := by
  have h := mellin_mellinKernel_ofReal a 0
  rw [Complex.ofReal_zero] at h
  rw [h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [show (0 : ℝ) - 1 = -1 by ring, Real.rpow_neg_one]
  ring

/-- **The derivative of the entire continuation at `s = 0`** is the
Mellin value `M(0)`: in `d/ds [Γ(s)⁻¹·M(s)]` the product rule leaves
`(1/Γ)'(0)·M(0) = M(0)`, since `Γ(0)⁻¹ = 0`.  (The *value* at `0` is
`0`; see `dirichletMellinContinuation_zero`.) -/
theorem hasDerivAt_dirichletMellinContinuation_zero (a : ℝ)
    (ha : 0 < a) :
    HasDerivAt (dirichletMellinContinuation a)
      (mellin (mellinKernel a) 0) 0 := by
  show HasDerivAt
    (fun s : ℂ => (Complex.Gamma s)⁻¹ * mellin (mellinKernel a) s)
    (mellin (mellinKernel a) 0) 0
  have hd := hasDerivAt_Gamma_inv_zero.mul
    (mellin_mellinKernel_differentiable a ha 0).hasDerivAt
  simpa [Pi.mul_def, Complex.Gamma_zero] using hd

/-- **The derivative bridge** (`cor:G-Dirichlet`):
`log G(a,b) = D'(0,b) - D'(0,a)`, where `D(·,c)` is realized by its
entire continuation `s ↦ Γ(s)⁻¹·∫₀^∞ t^(s-1)e^(-ct)𝓔(t) dt`. -/
theorem mpLimit_eq_deriv_sub (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((mpLimit a b : ℝ) : ℂ) =
      deriv (dirichletMellinContinuation b) 0 -
        deriv (dirichletMellinContinuation a) 0 := by
  rw [(hasDerivAt_dirichletMellinContinuation_zero b hb).deriv,
    (hasDerivAt_dirichletMellinContinuation_zero a ha).deriv,
    mellin_mellinKernel_zero b, mellin_mellinKernel_zero a,
    ← Complex.ofReal_sub]
  congr 1
  rw [← MeasureTheory.integral_sub (integrableOn_kernel_div b hb)
    (integrableOn_kernel_div a ha), mpLimit_eq_integral a b ha hb]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

end Fabius
