import Lib.General.NumberTheory.ImaginaryQuadraticField

/-!
# Quadratic twists, polar functions and logarithmic derivatives of Dirichlet L-functions

This part shows that the twist of a Dirichlet character by the Legendre symbol of an odd prime not
dividing the modulus is not principal. It defines `New.IsPolar`, the condition that a Laplace-type
transform of an error term continues meromorphically with at most simple poles in the right
half-plane. It also expresses `∑ χ(n) Λ(n) n^{-s}` through the logarithmic derivative of
`New.entireL χ` and identifies the residues of that logarithmic derivative with the orders of the
zeros of `New.entireL χ`.

## Main definitions and results

* `New.quadTwist_ne_one`: the twist of a character modulo `N` by the Legendre symbol `(·/d)`, for an
  odd prime `d` prime to `N`, is not principal.
* `New.IsPolar`: `E` is measurable, `|E v| ≤ C e^v` for `v ≥ 0`, and `∫₀^∞ E(v) e^{(1-s)v} dv`
  continues to a meromorphic function of `s` with at most simple poles of residue `r ρ` in
  `re ρ > 0`.
* `New.LSeriesHasSum_mul_vonMangoldt`: `∑ χ(n) Λ(n) n^{-s}` in terms of the logarithmic derivative
  of `New.entireL χ`.
* `New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt`: the residues of that logarithmic
  derivative are the orders of the zeros of `New.entireL χ`.

Notions from other files:
* `New.entireL`: The entire function equal to L(s, χ) if χ is not principal, and to the continuation
  of (s − 1)L(s, χ) if χ is principal.

## Relation to the literature

Known; see `Lib.Analytic.Landau` for sources.
-/

open ArithmeticFunction DirichletCharacter Complex Set Filter MeasureTheory Metric ProbabilityTheory
  Nat Topology ComplexOrder AnalyticOnNhd Real

namespace New

variable {N : ℕ} (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]

/-! ### The quadratic twist of a character -/

/-- The twist of `χ` by the Legendre symbol takes the value `χ(n) (n/d)` at an integer `n`. -/
lemma quadTwist_apply (n : ℤ) : quadTwist χ d n = χ n * legendreSym d n := by
  -- Both sides vanish unless `n` is prime to `N` and to `d`; then the change of level keeps values.
  rw [show (legendreSym d n : ℂ) = (chiK d).ringHomComp (algebraMap ℤ ℂ) n from rfl]
  by_cases h_cop : IsCoprime n (N * d : ℕ)
  · rw [quadTwist, MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ h_cop,
      changeLevel_eq_cast_of_dvd' _ _ h_cop]
  · rw [(apply_eq_zero_iff (quadTwist χ d) n).2 h_cop, zero_eq_mul, apply_eq_zero_iff,
      apply_eq_zero_iff]
    rwa [Nat.cast_mul, IsCoprime.mul_right_iff, not_and_or] at h_cop

/-- For a Dirichlet character `χ` mod `N` and an odd prime `d` coprime to `N`, the twist of `χ` by
the Legendre symbol `(·/d)`, a character mod `N * d`, is not principal. -/
lemma quadTwist_ne_one (hd : d ≠ 2) (hN : N.Coprime d) : quadTwist χ d ≠ 1 := by
  -- Take a non-residue `a` mod `d`, and `n` with `n ≡ 1` mod `N` and `n ≡ a` mod `d`. The twist is
  -- `-1` at `n`, while a value `x` of the trivial character satisfies `x * x = x`.
  intro h_one
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod d) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨n, (hn_N : n ≡ 1 [MOD N]), (hn_d : n ≡ a.val [MOD d])⟩ := chineseRemainder hN 1 a.val
  have hn_one : (n : ZMod N) = 1 := by simpa [← ZMod.natCast_eq_natCast_iff] using hn_N
  have hn_a : (n : ZMod d) = a := by simpa [← ZMod.natCast_eq_natCast_iff] using hn_d
  have h_val : quadTwist χ d n = -1 := by
    simpa [hn_one, legendreSym, hn_a, ha] using quadTwist_apply χ d n
  have h_sq : quadTwist χ d n * quadTwist χ d n = quadTwist χ d n := by
    simp [← MulChar.mul_apply, h_one]
  norm_num [h_val] at h_sq

/-! ### Polar functions and Laplace integrals -/

/-- `E` is measurable, `|E v| ≤ C e^v` for all `v ≥ 0`, and its transform
`∫₀^∞ E(v) e^{(1-s)v} dv` continues from `re s > 2` to a meromorphic function on `ℂ` whose poles in
`re s > 0` are at most simple; for `re ρ > 0`, `r ρ` is the residue at `ρ`, and `0` where there is
no pole. For `E(v) = R(e^v)` the transform is `∫₁^∞ R(y) y^{-s} dy`. -/
def IsPolar (E : ℝ → ℝ) (r : ℂ → ℂ) : Prop :=
  Measurable E ∧
  ∃ (C : ℝ) (Φ : ℂ → ℂ),
    Meromorphic Φ ∧
    -- (a) exponential growth
    (∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) ∧
    -- (b) `Φ` is the transform of `E` far to the right
    (∀ s : ℂ, 2 < re s → Φ s = ∫ v : ℝ in Ioi 0, E v * Complex.exp ((1 - s) * v)) ∧
    -- (c) at most simple poles in `re ρ > 0`, with residues `r ρ`
    ∀ ρ : ℂ, 0 < re ρ → Tendsto (fun z ↦ (z - ρ) * Φ z) (𝓝[≠] ρ) (𝓝 (r ρ))

variable {E : ℝ → ℝ} [NeZero N] {s : ℂ}

/-- If `E` is measurable and `|E v| ≤ C e^v` for `v ≥ 0`, the transform
`∫₀^∞ E(v) e^{(1-s)v} dv` converges for `re s > 2`. -/
lemma integrableOn_laplace_of_abs_le {C : ℝ} (hE : Measurable E)
    (hE_growth : ∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) (hs : 2 < s.re) :
    IntegrableOn (fun v : ℝ ↦ E v * Complex.exp ((1 - s) * v)) (Ioi 0) := by
  -- The integrand is bounded by `C * exp ((2 - re s) * v)`, whose exponent is negative.
  refine ((integrableOn_exp_mul_Ioi (sub_neg.2 hs) 0).const_mul C).mono' (by fun_prop)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun v hv ↦ ?_)
  calc
    ‖E v * cexp ((1 - s) * v)‖ = |E v| * ((1 - s.re) * v).exp := by simp [norm_exp]
    _ ≤ C * v.exp * ((1 - s.re) * v).exp := by grw [hE_growth v hv.le]
    _ = C * ((2 - s.re) * v).exp := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf

/-- For `re s > 0`, the Laplace transform of `t ^ k` at `s` is `k! / s ^ (k + 1)`. -/
lemma laplace_pow {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ∫ t : ℝ in Ioi 0, t ^ k * Complex.exp (-s * t) = k ! / s ^ (k + 1) := by
  -- Differentiate `∫₀^∞ exp (z t) dt = -1 / z` (for `re z < 0`) `k` times under the integral sign,
  -- reading the integral as a moment generating function, and put `z = -s`.
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hs_neg : (-s).re < 0 := neg_neg_of_pos hs
  have h_int : (-s).re ∈ interior (integrableExpSet id μ) :=
    interior_maximal (fun a ha ↦ integrableOn_exp_mul_Ioi ha 0) isOpen_Iio hs_neg
  have h_eq : EqOn (complexMGF id μ) (fun z ↦ -z⁻¹) {z | z.re < 0} :=
    fun z hz ↦ (integral_exp_mul_complex_Ioi hz 0).trans (by simp [neg_div])
  rw [show ∫ t : ℝ in Ioi 0, t ^ k * Complex.exp (-s * t) = iteratedDeriv k (complexMGF id μ) (-s)
      from (iteratedDeriv_complexMGF h_int k).symm,
    h_eq.iteratedDeriv_of_isOpen (isOpen_re_lt 0) k hs_neg]
  simp [iteratedDeriv_eq_iterate, zpow_sub₀ (neg_ne_zero.2 (ne_zero_of_re_pos hs)), neg_pow s,
    field, pow_succ]

/-! ### The logarithmic derivative of a Dirichlet L-function -/

@[fun_prop]
lemma analyticAt_entireL (s : ℂ) : AnalyticAt ℂ (entireL χ) s := by
  refine Differentiable.analyticAt ?_ s
  rw [entireL]
  split_ifs with hχ
  exacts [differentiable_LFunctionTrivChar₁ N, differentiable_LFunction hχ]

/-- `entireL χ` has no zero in `re s ≥ 1`. -/
lemma entireL_ne_zero (hs : 1 ≤ s.re) : entireL χ s ≠ 0 := by
  rw [entireL]
  split_ifs with hχ
  · obtain rfl | hs_ne := eq_or_ne s 1
    · exact LFunctionTrivChar₁_apply_one_ne_zero N
    · rw [LFunctionTrivChar₁, Function.update_of_ne hs_ne]
      exact mul_ne_zero (sub_ne_zero.2 hs_ne) (LFunction_ne_zero_of_one_le_re 1 (.inr hs_ne) hs)
  · exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

/-- For `re s > 1`, the series `∑ χ(n) Λ(n) n^{-s}` has the sum `-L'/L(s, χ)`, written through
`entireL χ`, which is `L(s, χ)`, or `(s - 1) L(s, χ)` for principal `χ`. The term `1 / (s - 1)` is
present only for `χ = 1`. -/
lemma LSeriesHasSum_mul_vonMangoldt (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ χ n * Λ n) s
      ((if χ = 1 then 1 else 0) / (s - 1) - logDeriv (entireL χ) s) := by
  refine LSeriesHasSum_iff.2 ⟨χ.LSeriesSummable_twist_vonMangoldt hs, ?_⟩
  -- The series is `-L' / L`; for `χ = 1` the factor `s - 1` of `entireL` adds `1 / (s - 1)` to the
  -- logarithmic derivative.
  have hs_ne : s ≠ 1 := ne_of_apply_ne re hs.ne'
  have h_series : LSeries (fun n : ℕ ↦ χ n * Λ n) s = -deriv χ.LFunction s / χ.LFunction s := by
    rw [χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs]
    exact χ.LSeries_twist_vonMangoldt_eq hs
  have hL_ne : χ.LFunction s ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inr hs_ne) hs.le
  rw [h_series, entireL, logDeriv_apply]
  obtain rfl | hχ := eq_or_ne χ 1
  · rw [ite_eq_left rfl, ite_eq_left rfl, deriv_LFunctionTrivChar₁_apply_of_ne_one N hs_ne,
      LFunctionTrivChar₁, Function.update_of_ne hs_ne, LFunctionTrivChar]
    field_simp [sub_ne_zero.2 hs_ne]
    ring
  · simp [hχ, neg_div]

/-- A function continuous at `s` has residue zero there. -/
lemma tendsto_sub_mul_of_continuousAt {f : ℂ → ℂ} (hf : ContinuousAt f s) :
    Tendsto (fun z : ℂ ↦ (z - s) * f z) (𝓝[≠] s) (𝓝 0) := by
  simpa using ((tendsto_id.sub_const s).mul hf).mono_left nhdsWithin_le_nhds

lemma analyticOrderAt_entireL_ne_top (s : ℂ) : analyticOrderAt (entireL χ) s ≠ ⊤ := by
  -- An entire function of infinite order at a point is zero, but `entireL χ 1 ≠ 0`.
  exact fun h_top ↦ entireL_ne_zero χ le_rfl
    (congrFun ((analyticOrderAt_eq_top_iff_eq_zero s (by fun_prop)).1 h_top) 1)

lemma analyticOrderNatAt_entireL_eq_zero_iff (s : ℂ) :
    analyticOrderNatAt (entireL χ) s = 0 ↔ entireL χ s ≠ 0 := by
  rw [← (analyticAt_entireL χ s).analyticOrderAt_eq_zero,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_entireL_ne_top χ s), Nat.cast_eq_zero]

/-- The logarithmic derivative of `entireL χ`, which is `L(s, χ)`, or `(s - 1) L(s, χ)` for
principal `χ`, has at most a simple pole at `s`. Its residue is the order of vanishing of
`entireL χ` at `s`. -/
lemma tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt (s : ℂ) :
    Tendsto (fun z : ℂ ↦ (z - s) * logDeriv (entireL χ) z) (𝓝[≠] s)
      (𝓝 (analyticOrderNatAt (entireL χ) s : ℂ)) := by
  -- Near `s` the function `entireL χ` is `(z - s) ^ n • g z` with `g s ≠ 0`.
  set n : ℕ := analyticOrderNatAt (entireL χ) s
  obtain ⟨g, hg, hg_ne, h_eq⟩ :
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ g s ≠ 0 ∧ entireL χ =ᶠ[𝓝 s] fun z ↦ (z - s) ^ n • g z :=
    (analyticAt_entireL χ s).analyticOrderAt_ne_top.1 (analyticOrderAt_entireL_ne_top χ s)
  -- The logarithmic derivative is `n / (z - s) + g' / g`, and `g' / g` is continuous at `s`.
  have h_lim : Tendsto (fun z : ℂ ↦ n + (z - s) * logDeriv g z) (𝓝[≠] s) (𝓝 (n : ℂ)) := by
    have h_cont : ContinuousAt (logDeriv g) s := (hg.deriv.div hg hg_ne).continuousAt
    simpa using (tendsto_sub_mul_of_continuousAt h_cont).const_add (n : ℂ)
  refine h_lim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds h_eq.deriv, nhdsWithin_le_nhds h_eq,
    nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg_ne),
    nhdsWithin_le_nhds hg.eventually_analyticAt, self_mem_nhdsWithin]
    with z hz_deriv hz hgz hg_an (hzs : z ≠ s)
  symm
  calc
    (z - s) * logDeriv (entireL χ) z = (z - s) * logDeriv (fun w : ℂ ↦ (w - s) ^ n * g w) z := by
      simp only [logDeriv_apply, hz, hz_deriv, smul_eq_mul]
    _ = (z - s) * (n / (z - s) + logDeriv g z) := by
      have h_mul : logDeriv (fun w : ℂ ↦ (w - s) ^ n * g w) z =
          logDeriv (fun w : ℂ ↦ (w - s) ^ n) z + logDeriv g z :=
        logDeriv_mul z (pow_ne_zero n (sub_ne_zero.2 hzs)) hgz (by fun_prop) hg_an.differentiableAt
      rw [h_mul, logDeriv_fun_pow (by fun_prop)]
      simp [logDeriv_apply, div_eq_mul_inv]
    _ = n + (z - s) * logDeriv g z := by field_simp [sub_ne_zero.2 hzs]

end New
