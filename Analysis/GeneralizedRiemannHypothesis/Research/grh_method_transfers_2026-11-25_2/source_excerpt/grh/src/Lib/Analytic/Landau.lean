import Lib.Analytic.EntireLFunction

/-!
# Landau's lemma

This part proves Landau's lemma: the moment generating function of a measure is not analytic at
its abscissa of convergence. It applies the lemma to transforms satisfying `New.IsPolar`. Assume
a one-sided bound on the error term `E`, and assume that the residues `r x` at real `x > β` have
non-negative real part. Then the part concludes that there is no pole to the right of `β`.
Together with `Lib.Analytic.EntireLFunction`, these are the analytic tools for passing from a
one-sided bound on an error term to the absence of zeros of L-functions.

## Main definitions and results

* `New.exists_Ioi_subset_integrableExpSet_of_analyticAt`: Landau's lemma; the Laplace transform of
  a measure is not analytic at its abscissa of convergence.
* `New.IsPolar.landau`: let `β > 0`. If `E v ≤ e^{(β-1)v}` for all large `v` and `re (r x) ≥ 0`
  for real `x > β`, then `r ρ = 0` for `re ρ > β`.

Notions from other files:
* `New.IsPolar` (from `Lib.Analytic.EntireLFunction`): `E` is measurable, `|E v| ≤ C e^v` for
  `v ≥ 0`, and `∫₀^∞ E(v) e^{(1-s)v} dv` continues meromorphically with at most simple poles of
  residue `r ρ` in `re ρ > 0`.

## Relation to the literature

Known result: Landau's lemma on Dirichlet integrals of one sign. It is applied to transforms with
simple poles whose residues at real points have non-negative real part: no pole lies to the right
of the abscissa given by the one-sided bound. Source: Montgomery and Vaughan, Multiplicative
Number Theory I, 2007, Lemma 15.1 (Widder, The Laplace Transform, 1941, II Thm 5b).
-/

open ArithmeticFunction DirichletCharacter Complex Set Filter MeasureTheory Metric ProbabilityTheory
  Nat Topology ComplexOrder AnalyticOnNhd Real

namespace New

variable {N : ℕ} (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]

variable {E : ℝ → ℝ} [NeZero N] {s : ℂ}

/-! ### Landau's lemma -/

/-- Let `X ≤ 0` be measurable and let `g` be equal near a real `z` to the moment generating function
`s ↦ ∫ exp (s X) ∂μ`, which converges near `z`. If the Taylor series of `g` at `z` converges at a
real `σ ≤ z`, then the moment generating function converges at `σ`. -/
lemma mem_integrableExpSet_of_summable_taylor {μ : Measure ℝ} {X : ℝ → ℝ} (hX : Measurable X)
    (hX_nonpos : ∀ y : ℝ, X y ≤ 0) {z σ : ℝ} (hz : z ∈ interior (integrableExpSet X μ)) {g : ℂ → ℂ}
    (hg_eq : g =ᶠ[𝓝 (z : ℂ)] complexMGF X μ) (hσ_le : σ ≤ z)
    (hg : Summable fun k : ℕ ↦ (k ! : ℂ)⁻¹ • (σ - z : ℂ) ^ k • iteratedDeriv k g z) :
    σ ∈ integrableExpSet X μ := by
  -- Expand `exp (σ X) = exp ((σ - z) X) exp (z X)` in the exponential series of the first factor.
  let term (k : ℕ) (y : ℝ) : ℝ := ((σ - z) * X y) ^ k / k ! * (z * X y).exp
  have term_nonneg (k : ℕ) (y : ℝ) : 0 ≤ term k y := by
    positivity [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hσ_le) (hX_nonpos y)]
  have tsum_term (y : ℝ) : ∑' k : ℕ, term k y = Real.exp (σ * X y) := by
    simp [term, tsum_mul_right, (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq,
      ← Real.exp_eq_exp_ℝ, sub_mul, Real.exp_sub]
  -- The integral of the `k`-th term is the `k`-th term of the Taylor series of `g` at `z`.
  let taylor (k : ℕ) : ℝ := ((k ! : ℂ)⁻¹ • (σ - z : ℂ) ^ k • iteratedDeriv k g z).re
  have lintegral_term (k : ℕ) : ∫⁻ y : ℝ, ‖term k y‖ₑ ∂μ = ENNReal.ofReal (taylor k) := by
    have term_eq : term k =
        fun y : ℝ ↦ (k ! : ℝ)⁻¹ * ((σ - z) ^ k * (X y ^ k * Real.exp (z * X y))) :=
      funext fun y ↦ by simp [term, mul_pow, field]
    have integrable : Integrable (term k) μ := by
      simpa only [term_eq] using
        ((integrable_pow_mul_exp_of_mem_interior_integrableExpSet hz k).const_mul _).const_mul _
    have taylor_eq : taylor k = ∫ y : ℝ, term k y ∂μ := by
      simp_rw [taylor, hg_eq.iteratedDeriv_eq, iteratedDeriv_complexMGF (z := z) hz, term_eq,
        integral_const_mul, smul_eq_mul, ← ofReal_natCast]
      norm_cast
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm integrable,
      Real.norm_of_nonneg (term_nonneg _ _), taylor_eq]
  change Integrable (fun y : ℝ ↦ (σ * X y).exp) μ
  refine ⟨by fun_prop, ?_⟩
  calc
    ∫⁻ y, ‖(σ * X y).exp‖ₑ ∂μ = ∫⁻ y, ‖∑' k, term k y‖ₑ ∂μ := by simp only [tsum_term]
    _ ≤ ∫⁻ y, ∑' k, ‖term k y‖ₑ ∂μ := lintegral_mono fun y ↦ enorm_tsum_le_tsum_enorm
    _ = ∑' k, .ofReal (taylor k) := by rw [lintegral_tsum (by fun_prop), tsum_congr lintegral_term]
    _ < ⊤ := (hasSum_re hg.hasSum).summable.tsum_ofReal_lt_top

/-- Let `E` satisfy `|E v| ≤ C e^v` for `v ≥ 0`, and let `β > 0`. If `E v ≤ e^{(β-1)v}` for large
`v`, then `E(v) e^v ≤ K e^{βv}` for some `K` and all `v > 0`. -/
lemma exists_mul_exp_le {C β : ℝ} (hE_growth : ∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) (hβ : 0 < β)
    (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ Real.exp ((β - 1) * v)) :
    ∃ K : ℝ, ∀ v : ℝ, 0 < v → E v * Real.exp v ≤ K * Real.exp (β * v) := by
  obtain ⟨Y, hY⟩ := hE_le.exists_forall_of_atTop
  -- `K ≥ 1` serves for `v ≥ Y`, and `K ≥ |C| e^{2Y}` for `v ≤ Y`.
  refine ⟨max 1 (|C| * Y.exp ^ 2), fun v hv ↦ ?_⟩
  obtain hYv | hvY := le_total Y v
  · calc
      E v * v.exp ≤ Real.exp ((β - 1) * v) * v.exp := by grw [hY v hYv]
      _ = Real.exp (β * v) := by rw [← Real.exp_add, sub_one_mul, sub_add_cancel]
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  · calc
      E v * v.exp ≤ |C| * v.exp * v.exp := by
        grw [le_abs_self (E v), hE_growth v hv.le, le_abs_self C]
      _ ≤ max 1 (|C| * Y.exp ^ 2) := by grw [mul_assoc, ← sq, hvY, ← le_max_right]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))

/-- Let `E` be measurable with `|E v| ≤ C e^v` for `v ≥ 0`, and let `β > 0`. If `E v ≤ e^{(β-1)v}`
for large `v`, then there are a measure `μ` and a real `K` such that, for `re s > β + 2`, the
integral `∫ e^{-s|v|} ∂μ` converges to `K / (s - β) - ∫₀^∞ E(v) e^{(1-s)v} dv`. -/
lemma exists_measure_laplace_eq {C β : ℝ} (hE : Measurable E)
    (hE_growth : ∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) (hβ : 0 < β)
    (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ Real.exp ((β - 1) * v)) :
    ∃ (μ : Measure ℝ) (K : ℝ), ∀ s : ℂ, β + 2 < s.re →
      s.re ∈ integrableExpSet (fun v : ℝ ↦ -|v|) μ ∧
      complexMGF (fun v : ℝ ↦ -|v|) μ s =
        K / (s - β) - ∫ v : ℝ in Ioi 0, E v * cexp ((1 - s) * v) := by
  -- The measure has the density `K e^{βv} - E(v) e^v ≥ 0` on `v > 0`.
  obtain ⟨K, hK⟩ := exists_mul_exp_le hE_growth hβ hE_le
  let density (v : ℝ) : ℝ := K * Real.exp (β * v) - E v * Real.exp v
  let μ : Measure ℝ := (volume.restrict (Ioi 0)).withDensity fun v ↦ (density v).toNNReal
  refine ⟨μ, K, fun s hs ↦ ?_⟩
  have hsβ : (β - s).re < 0 := by grind [sub_re, ofReal_re]
  have int_exp : Integrable (fun v : ℝ ↦ K * cexp ((β - s) * v)) (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_complex_Ioi hsβ 0).const_mul K
  have int_E := integrableOn_laplace_of_abs_le hE hE_growth (s := s) (by linarith)
  have integrand_eq :
      (fun v : ℝ ↦ K * cexp ((β - s) * v) - E v * cexp ((1 - s) * v)) =ᵐ[volume.restrict (Ioi 0)]
        fun v : ℝ ↦ (density v).toNNReal • cexp (s * (-|v| : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : 0 < v)
    rw [NNReal.smul_def, Real.coe_toNNReal (density v) (sub_nonneg.2 (hK v hv))]
    simp [density, abs_of_pos hv, sub_mul, Complex.exp_sub, Complex.exp_neg, field]
  have int_μ : Integrable (fun v : ℝ ↦ cexp (s * (-|v| : ℝ))) μ :=
    (integrable_withDensity_iff_integrable_smul (by fun_prop)).2
      ((int_exp.sub int_E).congr integrand_eq)
  refine ⟨int_μ.norm.congr (by simp [norm_exp]), ?_⟩
  calc
    complexMGF (fun v : ℝ ↦ -|v|) μ s
        = ∫ v : ℝ in Ioi 0, (density v).toNNReal • cexp (s * (-|v| : ℝ)) :=
      integral_withDensity_eq_integral_smul (by fun_prop) _
    _ = ∫ v : ℝ in Ioi 0, (K * cexp ((β - s) * v) - E v * cexp ((1 - s) * v)) :=
      (integral_congr_ae integrand_eq).symm
    _ = _ := by
      rw [integral_sub int_exp int_E, integral_const_mul, integral_exp_mul_complex_Ioi hsβ,
        ← neg_sub s, neg_div_neg_eq]
      simp [div_eq_mul_inv]

/-- Identity theorem: two functions meromorphic on `re z > a` that agree far to the right agree
on a punctured neighbourhood of every point of the half-plane. -/
lemma eventuallyEq_of_eq_far_right {f g : ℂ → ℂ} {a b : ℝ} (hf : MeromorphicOn f {z : ℂ | a < z.re})
    (hg : MeromorphicOn g {z : ℂ | a < z.re}) (hfg : ∀ z : ℂ, b < z.re → f z = g z) {ρ : ℂ}
    (hρ : a < ρ.re) :
    f =ᶠ[𝓝[≠] ρ] g := by
  -- `f - g` has infinite order at a point `s₀` to the right of `a` and `b`, hence at `ρ`.
  obtain ⟨s₀, has₀, hbs₀⟩ : ∃ s₀ : ℝ, a < s₀ ∧ b < s₀ := by simpa using exists_gt (max a b)
  have order_s₀ : meromorphicOrderAt (f - g) s₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr <| eventually_nhdsWithin_of_eventually_nhds <|
      mem_of_superset ((isOpen_re_gt b).mem_nhds hbs₀) fun z hz ↦ sub_eq_zero.mpr (hfg z hz)
  exact eventuallyEq_iff_sub.mpr <| meromorphicOrderAt_eq_top_iff.mp <| by_contra fun hne ↦
    (hf.sub hg).meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt a).isPreconnected hρ has₀ hne order_s₀

/-- **Landau's lemma.** Let `X ≤ 0` be measurable and let the moment generating function
`s ↦ ∫ exp (s X) ∂μ` converge to the right of `a`. If it agrees near the real points `x > a` close
to `a` with a function `g` that is analytic at `a`, then it converges on a larger half-line. So it
is not analytic at its abscissa of convergence. -/
lemma exists_Ioi_subset_integrableExpSet_of_analyticAt {μ : Measure ℝ} {X : ℝ → ℝ}
    (hX : Measurable X) (hX_nonpos : ∀ y : ℝ, X y ≤ 0) {a : ℝ}
    (ha : Ioi a ⊆ interior (integrableExpSet X μ)) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g a)
    (hg_eq : ∀ᶠ x : ℝ in 𝓝[>] a, g =ᶠ[𝓝 (x : ℂ)] complexMGF X μ) :
    ∃ b : ℝ, b < a ∧ Ioi b ⊆ integrableExpSet X μ := by
  obtain ⟨ε, hε, hg_ball⟩ := hg.exists_ball_analyticOnNhd
  -- The Taylor series at a real `z ∈ (a, a + ε / 2)` converges at every `σ ∈ (z - ε / 2, a]`.
  obtain ⟨z, hgz, haz, hz⟩ :=
    (hg_eq.and (Ioo_mem_nhdsGT (by linarith : a < a + ε / 2))).exists
  refine ⟨z - ε / 2, by linarith, fun σ (hσ : z - ε / 2 < σ) ↦ ?_⟩
  obtain hσa | haσ := le_or_gt σ a
  · have hza : dist (z : ℂ) a < ε / 2 := by grind [isometry_ofReal.dist_eq, Real.dist_eq]
    have hσz : dist (σ : ℂ) z < ε / 2 := by grind [isometry_ofReal.dist_eq, Real.dist_eq]
    exact mem_integrableExpSet_of_summable_taylor hX hX_nonpos (ha haz) hgz (hσa.trans haz.le)
      (hasSum_taylorSeries_on_ball (hg_ball.mono (ball_half_subset _ hza)).differentiableOn
        (mem_ball.2 hσz)).summable
  · exact interior_subset (ha haσ)

/-- Let `X ≤ 0` be measurable and let the moment generating function `s ↦ ∫ exp (s X) ∂μ` converge
to the right of `a`. Let `Ψ` be meromorphic at `a`, equal to it on a punctured neighbourhood of
every real `x > a`, and with at most a simple pole at `a`: `(z - a) Ψ z → c` with `re c ≤ 0`. Then
the moment generating function converges on a larger half-line. -/
lemma exists_Ioi_subset_integrableExpSet {μ : Measure ℝ} {X : ℝ → ℝ} (hX : Measurable X)
    (hX_nonpos : ∀ y : ℝ, X y ≤ 0) {a : ℝ} (ha : Ioi a ⊆ interior (integrableExpSet X μ))
    {Ψ : ℂ → ℂ} (hΨ : MeromorphicAt Ψ a)
    (hΨ_eq : ∀ x : ℝ, a < x → Ψ =ᶠ[𝓝[≠] (x : ℂ)] complexMGF X μ) {c : ℂ} (hc : c.re ≤ 0)
    (hΨ_res : Tendsto (fun z : ℂ ↦ (z - a) * Ψ z) (𝓝[≠] a) (𝓝 c)) :
    ∃ b : ℝ, b < a ∧ Ioi b ⊆ integrableExpSet X μ := by
  have tendsto_real : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] a) (𝓝[≠] a) :=
    ((hasDerivAt_id' a).ofReal_comp.tendsto_nhdsNE one_ne_zero).mono_left (nhdsGT_le_nhdsNE a)
  have eq_near : ∀ᶠ x : ℝ in 𝓝[>] a, Ψ =ᶠ[𝓝 (x : ℂ)] complexMGF X μ := by
    filter_upwards [tendsto_real.eventually hΨ.eventually_analyticAt, self_mem_nhdsWithin]
      with x hΨx hx using (hΨx.frequently_eq_iff_eventually_eq (analyticAt_complexMGF (ha hx))).mp
        (hΨ_eq x hx).frequently
  -- A residue of negative real part would make `Ψ(x) ≥ 0` tend to `-∞`: as `(x - a) Ψ(x) ≥ 0` for
  -- real `x > a` near `a`, we have `c ≥ 0`, and with `hc` this gives `c = 0`.
  have c_nonneg : 0 ≤ c := by
    refine ge_of_tendsto (hΨ_res.comp tendsto_real) ?_
    filter_upwards [eq_near, self_mem_nhdsWithin] with x hΨx (hx : a < x)
    simp [hΨx.self_of_nhds, complexMGF_ofReal, mul_nonneg, hx.le, mgf_nonneg]
  obtain rfl : c = 0 := Complex.ext (le_antisymm hc c_nonneg.1) c_nonneg.2.symm
  -- So there is no pole: `G(z) = (z - a) Ψ(z)` is analytic at `a`, and so is `g = G / (z - a)`,
  -- which is `Ψ` off `a`. Landau's lemma applies to `g`.
  let G (z : ℂ) : ℂ := (z - a) * Ψ z
  obtain ⟨p, hp⟩ : AnalyticAt ℂ G a :=
    MeromorphicAt.analyticAt (by fun_prop) (by simpa [continuousAt_iff_punctured_nhds, G])
  refine exists_Ioi_subset_integrableExpSet_of_analyticAt hX hX_nonpos ha
    hp.has_fpower_series_dslope_fslope.analyticAt ?_
  filter_upwards [eq_near, self_mem_nhdsWithin] with x hΨx (hx : a < x) using
    ((eqOn_dslope_sub_smul Ψ a).eventuallyEq_of_mem
      (isOpen_ne.mem_nhds (ofReal_injective.ne hx.ne'))).trans hΨx

/-- **No pole to the right of `β`**, by Landau's lemma and the sign of the residues at real points.
Suppose `IsPolar E r`: `|E v| ≤ C e^v` for `v ≥ 0` and the transform
`∫₀^∞ E(v) e^{(1-s)v} dv` has a meromorphic continuation with at most simple poles of residue `r ρ`
in `re ρ > 0`. Let `β > 0`. If `E(v) ≤ e^{(β-1)v}` for all large `v` and the residues at real points
right of `β` have real part `≥ 0`, then there is no pole in `re s > β`, that is, `r ρ = 0`. -/
lemma IsPolar.landau {r : ℂ → ℂ} (h : IsPolar E r) {β : ℝ} (hβ : 0 < β)
    (hr : ∀ x : ℝ, β < x → 0 ≤ (r x).re) (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ Real.exp ((β - 1) * v))
    {ρ : ℂ} (hρ : β < ρ.re) :
    r ρ = 0 := by
  -- `Ψ(s) = K / (s - β) - Φ(s)` continues the Laplace transform `F` of a measure. Let `a` be the
  -- larger of `β` and the abscissa of convergence of `F`; `Ψ` has no pole in `re s > a`. If
  -- `β < a`, the sign of the residue at `a` makes `F` converge to the left of `a`, which is absurd.
  obtain ⟨hE, C, Φ, hΦ, hE_growth, Φ_eq, Φ_res⟩ := h
  obtain ⟨μ, K, hμ⟩ : ∃ (μ : Measure ℝ) (K : ℝ), ∀ s : ℂ, β + 2 < s.re →
      s.re ∈ integrableExpSet (fun v : ℝ ↦ -|v|) μ ∧ complexMGF (fun v : ℝ ↦ -|v|) μ s =
        K / (s - β) - ∫ v : ℝ in Ioi 0, E v * cexp ((1 - s) * v) :=
    exists_measure_laplace_eq hE hE_growth hβ hE_le
  -- `S` is the set of real points where `F` converges.
  let S : Set ℝ := integrableExpSet (fun v ↦ -|v|) μ
  let F : ℂ → ℂ := complexMGF (fun v ↦ -|v|) μ
  let Ψ (s : ℂ) : ℂ := K / (s - β) - Φ s
  have far_right (s : ℂ) (hs : β + 2 < s.re) : Ψ s = F s := by
    simp [Ψ, F, hμ s hs, Φ_eq s (by linarith)]
  have Ψ_res (ρ : ℂ) (hρ : β < ρ.re) : Tendsto (fun z ↦ (z - ρ) * Ψ z) (𝓝[≠] ρ) (𝓝 (-r ρ)) := by
    have hK : ContinuousAt (fun s : ℂ ↦ K / (s - β)) ρ := by
      fun_prop (disch := exact sub_ne_zero.2 fun h_eq ↦ by simp [h_eq] at hρ)
    simpa [Ψ, mul_sub] using (tendsto_sub_mul_of_continuousAt hK).sub (Φ_res ρ (hβ.trans hρ))
  have bdd : BddAbove Sᶜ := ⟨β + 2, fun x hx ↦ le_of_not_gt fun hlt ↦ hx (hμ x hlt).1⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, IsLUB (insert β Sᶜ) a := Real.exists_isLUB (by simp) (bdd.insert β)
  have Ioi_subset : Ioi a ⊆ interior S := interior_maximal
    (fun x hx ↦ of_not_not fun hxS ↦ hx.not_ge (ha.1 (mem_insert_of_mem β hxS))) isOpen_Ioi
  have F_analytic {ρ : ℂ} (hρ : a < ρ.re) : AnalyticAt ℂ F ρ :=
    analyticAt_complexMGF (Ioi_subset hρ)
  have Ψ_eq {ρ : ℂ} (hρ : a < ρ.re) : Ψ =ᶠ[𝓝[≠] ρ] F := eventuallyEq_of_eq_far_right
    (fun z _ ↦ by fun_prop) (fun z hz ↦ (F_analytic hz).meromorphicAt) far_right hρ
  obtain rfl | hβa : β = a ∨ β < a := (ha.1 (mem_insert β Sᶜ)).eq_or_lt
  · -- The residue `-r ρ` of `Ψ` is that of the analytic function `F`.
    simpa using tendsto_nhds_unique ((Ψ_res ρ hρ).congr' (Ψ_eq hρ).mul_left)
      (tendsto_sub_mul_of_continuousAt (F_analytic hρ).continuousAt)
  · have res_nonpos : (-r a).re ≤ 0 := by simpa using hr a hβa
    obtain ⟨b, hba, hb⟩ : ∃ b : ℝ, b < a ∧ Ioi b ⊆ S :=
      exists_Ioi_subset_integrableExpSet (by fun_prop) (by simp) Ioi_subset (Ψ := Ψ) (by fun_prop)
        (fun x hx ↦ Ψ_eq hx) res_nonpos (Ψ_res a hβa)
    -- By the choice of `a`, some `σ ∉ S` lies to the right of `β` and `b`.
    obtain ⟨σ, hσ, hσ_gt, -⟩ : ∃ σ ∈ insert β Sᶜ, max β b < σ ∧ σ ≤ a :=
      ha.exists_between (max_lt hβa hba)
    obtain ⟨hβσ, hbσ⟩ : β < σ ∧ b < σ := max_lt_iff.mp hσ_gt
    exact absurd (hb hbσ) (hσ.resolve_left hβσ.ne')

end New
