import FabiusFunction.BoseFinitePartIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The mean of the one-periodic negative-Laplace correction

The correction `R(t) = negativeLaplacePeriodicCorrection t` built in
`FabiusFunction.NegativeLaplace` is exactly one-periodic, so the sharp Fabius
asymptotic carries its mean over a period as an additive constant.  This
module evaluates that mean in closed form,

`∫_0^1 R(t) dt = gammaZetaConstant / log 2 - log 2 / 12`,

where `gammaZetaConstant = γ² / 2 + γ₁ - π² / 12` is the Euler--Stieltjes
combination occurring, with the opposite sign, as the finite part of
`Γ(s) ζ(1+s)` at the origin, realized as a convergent split integral in
`FabiusFunction.BoseFinitePartIntegral`.

The proof is the substitution `x = 2 ^ t` combined with a dyadic regrouping.
Under that substitution an integral of a kernel `K (2 ^ t)` in `t` becomes a
`1 / log 2` multiple of the integral of `K x / x` in `x`.  Consequently, up
to that same factor, the `n`-th summand of `negativeLaplaceLog (2 ^ t)`,
integrated over one period, is the integral of `boseFinitePartSmallKernel`
over the dyadic block `(1/2^(n+1), 1/2^n]`, and the `n`-th summand of
`negativeLaplaceForwardTail (2 ^ t)` is the integral of
`boseFinitePartLargeKernel` over `[2^n, 2^(n+1))`.  Summing the blocks
reassembles the split finite-part integral over `(0, ∞)`.  The remaining
elementary piece `log 2 / 2 * (t ^ 2 - t)` of `R` contributes `- log 2 / 12`.

## Main results

* `negativeLaplacePeriodicMean_eq` — the closed form for the mean.  This is
  what `FabiusFunction.FabiusSharpConstant` converts into the constant term
  of the sharp asymptotic.
* `intervalIntegral_negativeLaplacePeriodicCorrection_unit` and
  `intervalIntegral_negativeLaplacePsi_unit` — the same value over every
  translated unit interval, and zero for the normalized correction.
* `intervalIntegral_negativeLaplaceLog_two_rpow`,
  `intervalIntegral_negativeLaplaceForwardTail_two_rpow`, and their sum
  `intervalIntegral_negativeLaplaceLog_add_tail_two_rpow` — the two halves of
  the period integral, and the finite-part integral they add up to.
* `smallDyadicInterval`, `largeDyadicInterval`, together with their union,
  disjointness, and `HasSum` countable-additivity lemmas — the dyadic
  partitions of `(0,1]` and `[1,∞)`.  `FabiusFunction.PeriodicFourier` reuses
  them unchanged for the Fourier coefficients, which is why they are public.
* `negativeLaplacePeriodicCorrection_eq_components` — the three-term
  decomposition of `R` along which the mean computation splits.

The remaining declarations are the `Function.Periodic` repackagings
`negativeLaplacePeriodicCorrection_periodic`, `negativeLaplacePsi_periodic`,
and the change-of-variable, continuity, and dominated-convergence steps
feeding those results.

Conventions.  `negativeLaplacePsi = R - negativeLaplacePeriodicMean` is the
zero-mean normalization fixed in `FabiusFunction.PeriodicCorrection`, so the
vanishing unit-interval integral is exactly that normalization.
`smallDyadicInterval` is half-open on the left and `largeDyadicInterval` on
the right; the endpoint mismatches this creates with the interval integrals
are absorbed by almost-everywhere set congruence.  Every identity here is an
exact evaluation, not an estimate.
-/

set_option autoImplicit false

open scoped BigOperators Topology Interval
open Set Filter MeasureTheory Asymptotics

namespace Fabius

/-- The exact negative-Laplace correction is one-periodic. -/
theorem negativeLaplacePeriodicCorrection_periodic :
    Function.Periodic negativeLaplacePeriodicCorrection 1 :=
  negativeLaplacePeriodicCorrection_add_one

/-- The zero-mean negative-Laplace correction is one-periodic. -/
theorem negativeLaplacePsi_periodic :
    Function.Periodic negativeLaplacePsi 1 :=
  negativeLaplacePsi_add_one

/-- Change of variables `x = 2 ^ t` for `negativeLaplaceKernel`: for all
real `a` and `b`, `log 2` times the `t`-integral over `[a, b]` is the
`x`-integral of `boseFinitePartSmallKernel` over `[2 ^ a, 2 ^ b]`.  The
extra `1 / x` in `boseFinitePartSmallKernel` is exactly the Jacobian
`dx = log 2 * x dt`.  This is the substitution behind
`intervalIntegral_negativeLaplaceTerm_two_rpow`. -/
lemma intervalIntegral_negativeLaplaceKernel_two_rpow
    (a b : ℝ) :
    Real.log 2 * (∫ t : ℝ in a..b,
      negativeLaplaceKernel ((2 : ℝ) ^ t)) =
      ∫ x : ℝ in (2 : ℝ) ^ a..(2 : ℝ) ^ b,
        boseFinitePartSmallKernel x := by
  let f : ℝ → ℝ := fun t => (2 : ℝ) ^ t
  let f' : ℝ → ℝ := fun t => Real.log 2 * (2 : ℝ) ^ t
  have hf : ∀ t ∈ [[a, b]], HasDerivAt f (f' t) t := by
    intro t ht
    simpa [f, f'] using (hasDerivAt_id t).const_rpow (by norm_num : (0 : ℝ) < 2)
  have hf' : ContinuousOn f' [[a, b]] := by
    exact (continuous_const.mul (Real.continuous_const_rpow (by norm_num))).continuousOn
  have hg : ContinuousOn boseFinitePartSmallKernel (f '' [[a, b]]) := by
    apply continuousOn_boseFinitePartSmallKernel.mono
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hsub := intervalIntegral.integral_comp_mul_deriv' hf hf' hg
  dsimp [f, f'] at hsub
  rw [show (fun t : ℝ =>
      boseFinitePartSmallKernel ((2 : ℝ) ^ t) *
        (Real.log 2 * (2 : ℝ) ^ t)) =
      fun t : ℝ => Real.log 2 * negativeLaplaceKernel ((2 : ℝ) ^ t) by
    funext t
    unfold boseFinitePartSmallKernel
    have hp : (2 : ℝ) ^ t ≠ 0 :=
      (Real.rpow_pos_of_pos (by norm_num) _).ne'
    field_simp [hp]
  ] at hsub
  rw [intervalIntegral.integral_const_mul] at hsub
  exact hsub

/-- Change of variables `x = 2 ^ t` for `boseLogKernel`: for all real `a`
and `b`, `log 2` times the `t`-integral over `[a, b]` is the `x`-integral
of `boseFinitePartLargeKernel` over `[2 ^ a, 2 ^ b]`, the extra `1 / x`
again being the Jacobian.  This is the substitution behind
`intervalIntegral_negativeLaplaceForwardTerm_two_rpow`. -/
lemma intervalIntegral_boseLogKernel_two_rpow
    (a b : ℝ) :
    Real.log 2 * (∫ t : ℝ in a..b, boseLogKernel ((2 : ℝ) ^ t)) =
      ∫ x : ℝ in (2 : ℝ) ^ a..(2 : ℝ) ^ b,
        boseFinitePartLargeKernel x := by
  let f : ℝ → ℝ := fun t => (2 : ℝ) ^ t
  let f' : ℝ → ℝ := fun t => Real.log 2 * (2 : ℝ) ^ t
  have hf : ∀ t ∈ [[a, b]], HasDerivAt f (f' t) t := by
    intro t ht
    simpa [f, f'] using (hasDerivAt_id t).const_rpow (by norm_num : (0 : ℝ) < 2)
  have hf' : ContinuousOn f' [[a, b]] := by
    exact (continuous_const.mul (Real.continuous_const_rpow (by norm_num))).continuousOn
  have hg : ContinuousOn boseFinitePartLargeKernel (f '' [[a, b]]) := by
    apply continuousOn_boseFinitePartLargeKernel.mono
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hsub := intervalIntegral.integral_comp_mul_deriv' hf hf' hg
  dsimp [f, f'] at hsub
  rw [show (fun t : ℝ =>
      boseFinitePartLargeKernel ((2 : ℝ) ^ t) *
        (Real.log 2 * (2 : ℝ) ^ t)) =
      fun t : ℝ => Real.log 2 * boseLogKernel ((2 : ℝ) ^ t) by
    funext t
    unfold boseFinitePartLargeKernel
    have hp : (2 : ℝ) ^ t ≠ 0 :=
      (Real.rpow_pos_of_pos (by norm_num) _).ne'
    field_simp [hp]
  ] at hsub
  rw [intervalIntegral.integral_const_mul] at hsub
  exact hsub

/-- The `n`-th small dyadic block `(1 / 2 ^ (n + 1), 1 / 2 ^ n]`, written
with inverses of natural powers of `2`.  The left endpoint is excluded
and the right endpoint included; indexed by `n : ℕ`, so the blocks tile
`(0, 1]`.  `FabiusFunction.PeriodicFourier` reuses it unchanged. -/
def smallDyadicInterval (n : ℕ) : Set ℝ :=
  Ioc (((2 : ℝ) ^ (n + 1))⁻¹) (((2 : ℝ) ^ n)⁻¹)

/-- The `n`-th large dyadic block `[2 ^ n, 2 ^ (n + 1))`, the opposite
half-open convention from `smallDyadicInterval`: left endpoint included,
right endpoint excluded.  Indexed by `n : ℕ`, so the blocks tile
`[1, ∞)`.  `FabiusFunction.PeriodicFourier` reuses it unchanged. -/
def largeDyadicInterval (n : ℕ) : Set ℝ :=
  Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1))

/-- The small dyadic blocks cover `(0, 1]` exactly. -/
lemma iUnion_smallDyadicInterval :
    (⋃ n : ℕ, smallDyadicInterval n) = Ioc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨n, hn⟩
    change ((2 : ℝ) ^ (n + 1))⁻¹ < x ∧ x ≤ ((2 : ℝ) ^ n)⁻¹ at hn
    constructor
    · exact (inv_pos.mpr (by positivity)).trans hn.1
    · exact hn.2.trans ((inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num)))
  · intro x hx
    have hx0 : 0 < x := hx.1
    have hy : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr hx.2
    obtain ⟨n, hnlow, hnup⟩ := exists_nat_pow_near hy (by norm_num : (1 : ℝ) < 2)
    simp only [mem_iUnion]
    refine ⟨n, ?_⟩
    change ((2 : ℝ) ^ (n + 1))⁻¹ < x ∧ x ≤ ((2 : ℝ) ^ n)⁻¹
    constructor
    · exact (inv_lt_comm₀ (by positivity) hx0).mpr (by simpa using hnup)
    · exact (le_inv_comm₀ hx0 (by positivity)).mpr (by simpa using hnlow)

/-- The small dyadic blocks are pairwise disjoint. -/
lemma pairwise_disjoint_smallDyadicInterval :
    Pairwise (Function.onFun Disjoint smallDyadicInterval) := by
  have hdis : ∀ {n m : ℕ}, n < m →
      Disjoint (smallDyadicInterval n) (smallDyadicInterval m) := by
    intro n m hlt
    rw [Set.disjoint_left]
    intro x hxn hxm
    change ((2 : ℝ) ^ (n + 1))⁻¹ < x ∧ x ≤ ((2 : ℝ) ^ n)⁻¹ at hxn
    change ((2 : ℝ) ^ (m + 1))⁻¹ < x ∧ x ≤ ((2 : ℝ) ^ m)⁻¹ at hxm
    have hpow : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hinv : ((2 : ℝ) ^ m)⁻¹ ≤ ((2 : ℝ) ^ (n + 1))⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr hpow
    linarith
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hdis hlt
  · exact (hdis hgt).symm

/-- The large dyadic blocks cover `[1, ∞)` exactly. -/
lemma iUnion_largeDyadicInterval :
    (⋃ n : ℕ, largeDyadicInterval n) = Ici (1 : ℝ) := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨n, hn⟩
    change (2 : ℝ) ^ n ≤ x ∧ x < (2 : ℝ) ^ (n + 1) at hn
    exact (one_le_pow₀ (by norm_num)).trans hn.1
  · intro x hx
    have hx1 : 1 ≤ x := hx
    obtain ⟨n, hnlow, hnup⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
    simp only [mem_iUnion]
    exact ⟨n, hnlow, hnup⟩

/-- The large dyadic blocks are pairwise disjoint. -/
lemma pairwise_disjoint_largeDyadicInterval :
    Pairwise (Function.onFun Disjoint largeDyadicInterval) := by
  have hdis : ∀ {n m : ℕ}, n < m →
      Disjoint (largeDyadicInterval n) (largeDyadicInterval m) := by
    intro n m hlt
    rw [Set.disjoint_left]
    intro x hxn hxm
    change (2 : ℝ) ^ n ≤ x ∧ x < (2 : ℝ) ^ (n + 1) at hxn
    change (2 : ℝ) ^ m ≤ x ∧ x < (2 : ℝ) ^ (m + 1) at hxm
    have hpow : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hdis hlt
  · exact (hdis hgt).symm

/-- Countable additivity of `∫_{(0, 1]} boseFinitePartSmallKernel` along
the small dyadic blocks: the block integrals are summable with that
integral as their sum.  Uses the integrability of the kernel on `(0, 1]`
established in `FabiusFunction.BoseFinitePartIntegral`. -/
lemma hasSum_integral_smallDyadicInterval :
    HasSum (fun n : ℕ => ∫ x : ℝ in smallDyadicInterval n,
      boseFinitePartSmallKernel x)
      (∫ x : ℝ in Ioc 0 1, boseFinitePartSmallKernel x) := by
  have h := hasSum_integral_iUnion
    (f := boseFinitePartSmallKernel) (s := smallDyadicInterval)
    (fun n => measurableSet_Ioc) pairwise_disjoint_smallDyadicInterval
    (by simpa [iUnion_smallDyadicInterval] using integrableOn_boseFinitePartSmallKernel)
  simpa [iUnion_smallDyadicInterval] using h

/-- Countable additivity of `∫_{(1, ∞)} boseFinitePartLargeKernel` along
the large dyadic blocks, stated with the blocks written as
`Ioc (2 ^ n) (2 ^ (n + 1))` rather than `largeDyadicInterval n`; the
endpoint swap and the `Ioi 1` versus `Ici 1` mismatch are absorbed by
almost-everywhere set congruence. -/
lemma hasSum_integral_largeDyadicInterval :
    HasSum (fun n : ℕ => ∫ x : ℝ in Ioc ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)),
      boseFinitePartLargeKernel x)
      (∫ x : ℝ in Ioi 1, boseFinitePartLargeKernel x) := by
  have hIntIci : IntegrableOn boseFinitePartLargeKernel (Ici 1) :=
    IntegrableOn.congr_set_ae integrableOn_boseFinitePartLargeKernel
      Ioi_ae_eq_Ici.symm
  have h := hasSum_integral_iUnion
    (f := boseFinitePartLargeKernel) (s := largeDyadicInterval)
    (fun n => measurableSet_Ico) pairwise_disjoint_largeDyadicInterval
    (by simpa [iUnion_largeDyadicInterval] using hIntIci)
  have h' := h.congr_fun (fun n => by
    exact setIntegral_congr_set Ico_ae_eq_Ioc.symm)
  rw [iUnion_largeDyadicInterval] at h'
  rw [setIntegral_congr_set Ioi_ae_eq_Ici]
  exact h'

/-- The `n`-th summand of `negativeLaplaceLog (2 ^ t)`, integrated over
the period `[0, 1]` and scaled by `log 2`, is the integral of
`boseFinitePartSmallKernel` over `smallDyadicInterval n`.  The argument
`2 ^ t / 2 ^ (n + 1)` sweeps that block as `t` runs over `[0, 1]`. -/
lemma intervalIntegral_negativeLaplaceTerm_two_rpow (n : ℕ) :
    Real.log 2 * (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceTerm ((2 : ℝ) ^ t) n) =
      ∫ x : ℝ in smallDyadicInterval n, boseFinitePartSmallKernel x := by
  have heq : ∀ t : ℝ, negativeLaplaceTerm ((2 : ℝ) ^ t) n =
      negativeLaplaceKernel ((2 : ℝ) ^ (t - ((n + 1 : ℕ) : ℝ))) := by
    intro t
    unfold negativeLaplaceTerm
    congr 1
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  rw [intervalIntegral.integral_congr (fun t ht => heq t)]
  rw [intervalIntegral.integral_comp_sub_right
    (fun u : ℝ => negativeLaplaceKernel ((2 : ℝ) ^ u)) ((n + 1 : ℕ) : ℝ)]
  rw [show (0 : ℝ) - ((n + 1 : ℕ) : ℝ) = -((n + 1 : ℕ) : ℝ) by ring]
  rw [show (1 : ℝ) - ((n + 1 : ℕ) : ℝ) = -((n : ℕ) : ℝ) by
    push_cast
    ring]
  have hchange := intervalIntegral_negativeLaplaceKernel_two_rpow
    (-((n + 1 : ℕ) : ℝ)) (-((n : ℕ) : ℝ))
  have hbounds : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num) (by omega))
  rw [smallDyadicInterval, ← intervalIntegral.integral_of_le hbounds]
  have hlo : (2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) =
      ((2 : ℝ) ^ (n + 1))⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have hhi : (2 : ℝ) ^ (-((n : ℕ) : ℝ)) = ((2 : ℝ) ^ n)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [hlo, hhi] at hchange
  exact hchange

/-- The `n`-th summand of `negativeLaplaceForwardTail (2 ^ t)`,
integrated over the period `[0, 1]` and scaled by `log 2`, is the
integral of `boseFinitePartLargeKernel` over `(2 ^ n, 2 ^ (n + 1)]`.  The
argument `2 ^ t * 2 ^ n` sweeps that block as `t` runs over `[0, 1]`. -/
lemma intervalIntegral_negativeLaplaceForwardTerm_two_rpow (n : ℕ) :
    Real.log 2 * (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n) =
      ∫ x : ℝ in Ioc ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)),
        boseFinitePartLargeKernel x := by
  have heq : ∀ t : ℝ, negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n =
      boseLogKernel ((2 : ℝ) ^ (t + (n : ℝ))) := by
    intro t
    unfold negativeLaplaceForwardTerm boseLogKernel
    congr 3
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  rw [intervalIntegral.integral_congr (fun t ht => heq t)]
  rw [intervalIntegral.integral_comp_add_right
    (fun u : ℝ => boseLogKernel ((2 : ℝ) ^ u)) (n : ℝ)]
  rw [show (0 : ℝ) + (n : ℝ) = (n : ℝ) by ring]
  rw [show (1 : ℝ) + (n : ℝ) = (n : ℝ) + 1 by ring]
  have hchange := intervalIntegral_boseLogKernel_two_rpow (n : ℝ) (n + 1 : ℝ)
  have hbounds : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [← intervalIntegral.integral_of_le hbounds]
  have hlo : (2 : ℝ) ^ (n : ℝ) = (2 : ℝ) ^ n := by
    rw [Real.rpow_natCast]
  have hhi : (2 : ℝ) ^ ((n : ℝ) + 1) = (2 : ℝ) ^ (n + 1) := by
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rw [hlo, hhi] at hchange
  exact hchange

/-- Each summand `t ↦ negativeLaplaceTerm (2 ^ t) n` is continuous on all
of `ℝ`, since `2 ^ t` is positive everywhere.  Supplies the strong
measurability hypothesis of the dominated-convergence step below, and is
reused for the Fourier coefficients in `FabiusFunction.PeriodicFourier`. -/
lemma continuous_negativeLaplaceTerm_two_rpow (n : ℕ) :
    Continuous (fun t : ℝ => negativeLaplaceTerm ((2 : ℝ) ^ t) n) := by
  let s : ℝ → ℝ := fun t => (2 : ℝ) ^ t / (2 : ℝ) ^ (n + 1)
  have hs : Continuous s := by
    dsimp [s]
    fun_prop (disch := positivity)
  have hspos : ∀ t, 0 < s t := by
    intro t
    dsimp [s]
    positivity
  have hnum : Continuous (fun t => 1 - Real.exp (-(s t))) :=
    continuous_const.sub (Real.continuous_exp.comp hs.neg)
  have hnumpos : ∀ t, 0 < 1 - Real.exp (-(s t)) := by
    intro t
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (hspos t))
  unfold negativeLaplaceTerm negativeLaplaceKernel
  change Continuous (fun t => Real.log ((1 - Real.exp (-(s t))) / s t))
  exact (hnum.div hs (fun t => (hspos t).ne')).log
    (fun t => div_ne_zero (hnumpos t).ne' (hspos t).ne')

/-- Term-by-term integration of `negativeLaplaceLog (2 ^ t)` over one
period: the summand integrals are summable with the period integral of
the whole series as their sum.  Proved by dominated convergence with the
geometric bound `1 / 2 ^ n`, available because `2 ^ t ≤ 2` on `[0, 1]`. -/
lemma hasSum_intervalIntegral_negativeLaplaceTerm_two_rpow :
    HasSum (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceTerm ((2 : ℝ) ^ t) n)
      (∫ t : ℝ in (0 : ℝ)..1, negativeLaplaceLog ((2 : ℝ) ^ t)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n : ℕ => fun _ : ℝ => 1 / (2 : ℝ) ^ n)
  · intro n
    exact (continuous_negativeLaplaceTerm_two_rpow n).aestronglyMeasurable
  · intro n
    filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht1 : t ≤ 1 := ht.2
    rw [Real.norm_eq_abs]
    refine (abs_negativeLaplaceTerm_le ((2 : ℝ) ^ t)
      (Real.rpow_pos_of_pos (by norm_num) _) n).trans ?_
    have hs : (2 : ℝ) ^ t ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) ht1
    calc
      (2 : ℝ) ^ t / 2 / 2 ^ n ≤ 2 / 2 / 2 ^ n := by gcongr
      _ = 1 / 2 ^ n := by ring
  · filter_upwards with t ht
    have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    simpa [one_div, inv_pow] using hgeom
  · simpa using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ =>
        ∑' n : ℕ, 1 / (2 : ℝ) ^ n) volume 0 1)
  · filter_upwards with t ht
    simpa [negativeLaplaceLog] using (summable_negativeLaplaceTerm ((2 : ℝ) ^ t)
      (Real.rpow_pos_of_pos (by norm_num) _)).hasSum

/-- Each summand `t ↦ negativeLaplaceForwardTerm (2 ^ t) n` is continuous
on all of `ℝ`.  Supplies the strong measurability hypothesis of the
dominated-convergence step below, and is reused for the Fourier
coefficients in `FabiusFunction.PeriodicFourier`. -/
lemma continuous_negativeLaplaceForwardTerm_two_rpow (n : ℕ) :
    Continuous (fun t : ℝ => negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n) := by
  let s : ℝ → ℝ := fun t => (2 : ℝ) ^ t * (2 : ℝ) ^ n
  have hs : Continuous s := by
    dsimp [s]
    exact (Real.continuous_const_rpow (by norm_num)).mul continuous_const
  have hspos : ∀ t, 0 < s t := by
    intro t
    dsimp [s]
    positivity
  have hnum : Continuous (fun t => 1 - Real.exp (-(s t))) :=
    continuous_const.sub (Real.continuous_exp.comp hs.neg)
  have hnumpos : ∀ t, 0 < 1 - Real.exp (-(s t)) := by
    intro t
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (hspos t))
  unfold negativeLaplaceForwardTerm
  change Continuous (fun t => Real.log (1 - Real.exp (-(s t))))
  exact hnum.log (fun t => (hnumpos t).ne')

/-- Term-by-term integration of `negativeLaplaceForwardTail (2 ^ t)` over
one period: the summand integrals are summable with the period integral
of the whole tail as their sum.  Proved by dominated convergence with the
geometric bound `exp (-1) ^ (n + 1) / (1 - exp (-1))`, available because
`2 ^ t ≥ 1` on `[0, 1]`. -/
lemma hasSum_intervalIntegral_negativeLaplaceForwardTerm_two_rpow :
    HasSum (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n)
      (∫ t : ℝ in (0 : ℝ)..1, negativeLaplaceForwardTail ((2 : ℝ) ^ t)) := by
  let r : ℝ := Real.exp (-1)
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by
    dsimp [r]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hmajor : Summable (fun n : ℕ => r ^ (n + 1) / (1 - r)) := by
    have hgeom : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr0 hr1
    refine (hgeom.mul_left (r / (1 - r))).congr ?_
    intro n
    rw [pow_succ']
    ring
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n : ℕ => fun _ : ℝ => r ^ (n + 1) / (1 - r))
  · intro n
    exact (continuous_negativeLaplaceForwardTerm_two_rpow n).aestronglyMeasurable
  · intro n
    filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have hs1 : 1 ≤ (2 : ℝ) ^ t := Real.one_le_rpow (by norm_num) ht0
    rw [Real.norm_eq_abs]
    refine (abs_negativeLaplaceForwardTerm_le ((2 : ℝ) ^ t)
      (Real.rpow_pos_of_pos (by norm_num) _) n).trans ?_
    have hexp : Real.exp (-((2 : ℝ) ^ t)) ≤ r := by
      dsimp [r]
      exact Real.exp_le_exp.mpr (by linarith)
    have hnum : Real.exp (-((2 : ℝ) ^ t)) ^ (n + 1) ≤ r ^ (n + 1) :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hexp _
    have hden : 0 < 1 - r := sub_pos.mpr hr1
    have hden' : 1 - r ≤ 1 - Real.exp (-((2 : ℝ) ^ t)) :=
      sub_le_sub_left hexp 1
    exact (div_le_div_of_nonneg_left
      (pow_nonneg (Real.exp_nonneg _) _) hden hden').trans
        (div_le_div_of_nonneg_right hnum hden.le)
  · filter_upwards with t ht
    exact hmajor
  · simpa using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ =>
        ∑' n : ℕ, r ^ (n + 1) / (1 - r)) volume 0 1)
  · filter_upwards with t ht
    simpa [negativeLaplaceForwardTail] using
      (summable_negativeLaplaceForwardTerm ((2 : ℝ) ^ t)
      (Real.rpow_pos_of_pos (by norm_num) _)).hasSum

/-- One half of the period integral, reduced to the finite-part integral:
the mean of `negativeLaplaceLog (2 ^ t)` over `[0, 1]` is the small-`x`
piece `∫_{(0, 1]} boseFinitePartSmallKernel`, divided by `log 2`.
Obtained by matching the two `HasSum` statements above block by block. -/
theorem intervalIntegral_negativeLaplaceLog_two_rpow :
    (∫ t : ℝ in (0 : ℝ)..1, negativeLaplaceLog ((2 : ℝ) ^ t)) =
      (∫ x : ℝ in Ioc 0 1, boseFinitePartSmallKernel x) / Real.log 2 := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hdy := hasSum_integral_smallDyadicInterval.div_const (Real.log 2)
  have hdy' : HasSum (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceTerm ((2 : ℝ) ^ t) n)
      ((∫ x : ℝ in Ioc 0 1, boseFinitePartSmallKernel x) / Real.log 2) := by
    apply hdy.congr_fun
    intro n
    have hn := intervalIntegral_negativeLaplaceTerm_two_rpow n
    rw [eq_div_iff hlog2]
    calc
      (∫ t : ℝ in (0 : ℝ)..1,
          negativeLaplaceTerm ((2 : ℝ) ^ t) n) * Real.log 2 =
          Real.log 2 * (∫ t : ℝ in (0 : ℝ)..1,
            negativeLaplaceTerm ((2 : ℝ) ^ t) n) := by ring
      _ = ∫ x : ℝ in smallDyadicInterval n,
          boseFinitePartSmallKernel x := hn
  exact hasSum_intervalIntegral_negativeLaplaceTerm_two_rpow.unique hdy'

/-- The other half, likewise reduced: the mean of
`negativeLaplaceForwardTail (2 ^ t)` over `[0, 1]` is the large-`x` piece
`∫_{(1, ∞)} boseFinitePartLargeKernel` of the split finite-part integral,
divided by `log 2`. -/
theorem intervalIntegral_negativeLaplaceForwardTail_two_rpow :
    (∫ t : ℝ in (0 : ℝ)..1, negativeLaplaceForwardTail ((2 : ℝ) ^ t)) =
      (∫ x : ℝ in Ioi 1, boseFinitePartLargeKernel x) / Real.log 2 := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hdy := hasSum_integral_largeDyadicInterval.div_const (Real.log 2)
  have hdy' : HasSum (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n)
      ((∫ x : ℝ in Ioi 1, boseFinitePartLargeKernel x) / Real.log 2) := by
    apply hdy.congr_fun
    intro n
    have hn := intervalIntegral_negativeLaplaceForwardTerm_two_rpow n
    rw [eq_div_iff hlog2]
    calc
      (∫ t : ℝ in (0 : ℝ)..1,
          negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n) * Real.log 2 =
          Real.log 2 * (∫ t : ℝ in (0 : ℝ)..1,
            negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n) := by ring
      _ = ∫ x : ℝ in Ioc ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)),
          boseFinitePartLargeKernel x := hn
  exact hasSum_intervalIntegral_negativeLaplaceForwardTerm_two_rpow.unique hdy'

/-- `t ↦ negativeLaplaceLog (2 ^ t)` is continuous on all of `ℝ`, since
`2 ^ t` stays in the positive half-line where `negativeLaplaceLog` is
continuous.  Used for interval integrability when the period integral is
split. -/
lemma continuous_negativeLaplaceLog_two_rpow :
    Continuous (fun t : ℝ => negativeLaplaceLog ((2 : ℝ) ^ t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  change ContinuousAt (negativeLaplaceLog ∘ fun u : ℝ => (2 : ℝ) ^ u) t
  exact (continuousAt_negativeLaplaceLog _
    (Real.rpow_pos_of_pos (by norm_num) _)).comp
      (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).continuousAt

/-- `t ↦ negativeLaplaceForwardTail (2 ^ t)` is continuous on all of `ℝ`,
for the same reason.  Used for interval integrability when the period
integral is split. -/
lemma continuous_negativeLaplaceForwardTail_two_rpow :
    Continuous (fun t : ℝ => negativeLaplaceForwardTail ((2 : ℝ) ^ t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  change ContinuousAt (negativeLaplaceForwardTail ∘ fun u : ℝ => (2 : ℝ) ^ u) t
  exact (continuousAt_negativeLaplaceForwardTail _
    (Real.rpow_pos_of_pos (by norm_num) _)).comp
      (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).continuousAt

/-- The two transcendental halves add up over one period to
`gammaZetaConstant / log 2`: the dyadic blocks reassemble the split
finite-part integral of `FabiusFunction.BoseFinitePartIntegral`.  This is
the only non-elementary input to `negativeLaplacePeriodicMean_eq`. -/
theorem intervalIntegral_negativeLaplaceLog_add_tail_two_rpow :
    (∫ t : ℝ in (0 : ℝ)..1,
      (negativeLaplaceLog ((2 : ℝ) ^ t) +
        negativeLaplaceForwardTail ((2 : ℝ) ^ t))) =
      gammaZetaConstant / Real.log 2 := by
  rw [intervalIntegral.integral_add
    (continuous_negativeLaplaceLog_two_rpow.intervalIntegrable 0 1)
    (continuous_negativeLaplaceForwardTail_two_rpow.intervalIntegrable 0 1)]
  rw [intervalIntegral_negativeLaplaceLog_two_rpow,
    intervalIntegral_negativeLaplaceForwardTail_two_rpow]
  rw [← add_div]
  rw [boseFinitePartIntegral_eq_gammaZetaConstant]

/-- The three-term decomposition of the periodic correction: the
small-argument series `negativeLaplaceLog (2 ^ t)`, the elementary
quadratic `log 2 / 2 * (t ^ 2 - t)`, and the forward tail
`negativeLaplaceForwardTail (2 ^ t)`.  The mean computation splits along
it, as do the regularity arguments in `FabiusFunction.PeriodicRegularity`
and `FabiusFunction.PeriodicSmooth`. -/
lemma negativeLaplacePeriodicCorrection_eq_components (t : ℝ) :
    negativeLaplacePeriodicCorrection t =
      negativeLaplaceLog ((2 : ℝ) ^ t) +
        Real.log 2 / 2 * (t ^ 2 - t) +
          negativeLaplaceForwardTail ((2 : ℝ) ^ t) := by
  rw [negativeLaplacePeriodicCorrection, negativeLaplaceMultiplicativeCorrection]
  rw [Real.logb_rpow (by norm_num) (by norm_num)]

/-- The exact mean of the one-periodic correction. -/
theorem negativeLaplacePeriodicMean_eq :
    negativeLaplacePeriodicMean =
      gammaZetaConstant / Real.log 2 - Real.log 2 / 12 := by
  rw [negativeLaplacePeriodicMean]
  rw [intervalIntegral.integral_congr
    (fun t ht => negativeLaplacePeriodicCorrection_eq_components t)]
  rw [show (fun t : ℝ =>
      negativeLaplaceLog ((2 : ℝ) ^ t) +
        Real.log 2 / 2 * (t ^ 2 - t) +
          negativeLaplaceForwardTail ((2 : ℝ) ^ t)) =
      fun t : ℝ =>
        (negativeLaplaceLog ((2 : ℝ) ^ t) +
          negativeLaplaceForwardTail ((2 : ℝ) ^ t)) +
            Real.log 2 / 2 * (t ^ 2 - t) by
    funext t
    ring]
  have hsplit : (∫ t : ℝ in (0 : ℝ)..1,
      (negativeLaplaceLog ((2 : ℝ) ^ t) +
        negativeLaplaceForwardTail ((2 : ℝ) ^ t)) +
          Real.log 2 / 2 * (t ^ 2 - t)) =
      (∫ t : ℝ in (0 : ℝ)..1,
        negativeLaplaceLog ((2 : ℝ) ^ t) +
          negativeLaplaceForwardTail ((2 : ℝ) ^ t)) +
        ∫ t : ℝ in (0 : ℝ)..1, Real.log 2 / 2 * (t ^ 2 - t) := by
    exact intervalIntegral.integral_add
      ((continuous_negativeLaplaceLog_two_rpow.add
        continuous_negativeLaplaceForwardTail_two_rpow).intervalIntegrable 0 1)
      ((continuous_const.mul
        ((continuous_id.pow 2).sub continuous_id)).intervalIntegrable 0 1)
  rw [hsplit]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral_negativeLaplaceLog_add_tail_two_rpow]
  have hpoly : (∫ t : ℝ in (0 : ℝ)..1, t ^ 2 - t) = -1 / 6 := by
    norm_num
  rw [hpoly]
  ring

/-- Every translated unit interval has the computed correction mean. -/
theorem intervalIntegral_negativeLaplacePeriodicCorrection_unit (t : ℝ) :
    (∫ x : ℝ in t..t + 1, negativeLaplacePeriodicCorrection x) =
      gammaZetaConstant / Real.log 2 - Real.log 2 / 12 := by
  calc
    (∫ x : ℝ in t..t + 1, negativeLaplacePeriodicCorrection x) =
        ∫ x : ℝ in (0 : ℝ)..0 + 1, negativeLaplacePeriodicCorrection x :=
      negativeLaplacePeriodicCorrection_periodic.intervalIntegral_add_eq t 0
    _ = negativeLaplacePeriodicMean := by
      simp only [zero_add]
      rfl
    _ = gammaZetaConstant / Real.log 2 - Real.log 2 / 12 :=
      negativeLaplacePeriodicMean_eq

/-- The normalized correction integrates to zero on every translated unit interval. -/
theorem intervalIntegral_negativeLaplacePsi_unit (t : ℝ) :
    (∫ x : ℝ in t..t + 1, negativeLaplacePsi x) = 0 := by
  calc
    (∫ x : ℝ in t..t + 1, negativeLaplacePsi x) =
        ∫ x : ℝ in (0 : ℝ)..0 + 1, negativeLaplacePsi x :=
      negativeLaplacePsi_periodic.intervalIntegral_add_eq t 0
    _ = 0 := by
      simpa only [zero_add] using integral_negativeLaplacePsi_zero

end Fabius
