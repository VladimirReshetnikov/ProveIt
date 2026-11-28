import Lib.General.Analysis.HolomorphicIntegrals
import Lib.Shimura.ComplexTheta.AppellHumbertData

/-!
# Theta functions on complex tori: dimension formula, base points, multipliers

This file treats Appell–Humbert data `(B, χ)` with positive Riemann form `E` for a full lattice
`L` in a finite-dimensional complex space `V`. It proves the convergence of theta series and the
existence of a nonzero theta function. It proves that the square of the dimension of the space of
theta functions equals the index of `L` in its dual lattice, and that the twisted translations by
the dual lattice act irreducibly. It shows that multiples of a positive type have no base point.
It also defines the canonical multiplier and the normalised translations.

## Main definitions and results

* `New.IsAppellHumbert.finrank_sq_eq_relIndex`: for Appell–Humbert data with positive `E`,
  `(dim thetaSpace)² = [dual : L]`, the dimension is positive, and the twisted translations by the
  dual lattice span all endomorphisms of the space of theta functions; so the space is irreducible
  (`New.IsAppellHumbert.thetaSpace_le_of_thetaShift_mem`, `New.IsAppellHumbert.schur_lemma`).
* `New.IsAppellHumbert.exists_mem_thetaSpace_nsmul_apply_ne_zero`: for Appell–Humbert data with
  positive `E` and `n ≥ 2` the theta functions of type `(n B, χ ^ n)` have no common zero.
* `New.ThetaTori.canonicalMultiplier`, `New.ThetaTori.normalizedShift`: a canonical multiplier
  `exp (πi E(b x, x))` for a linear map `b`, and the twisted translations divided by it, which, for
  Appell–Humbert data and `b` with `E (b u) w = E u w - E u (b w)`, obey a Heisenberg law
  (`New.IsAppellHumbert.normalizedShift_normalizedShift`).

Notions from other files:
* `New.RealComplexForm.thetaSpace`: the entire `f` with
  `f (z + l) = χ l * exp (B l z + B l l / 2) * f z` for `l ∈ L`.
* `New.RealComplexForm.thetaShift`: translation by `a` twisted by `exp (-(B a z + B a a / 2))`.
* `New.RealComplexForm.dualLattice`: the `v` in `V` with `E(v, l)` an integer for all `l` in `L`.

## Relation to the literature

Frobenius' dimension formula and irreducibility of the theta group. Here the statement is
basis-free, with the square of the dimension equal to the index of the lattice in its dual. It is
proved together with irreducibility from a theta kernel on the torus without a symplectic basis, and
the orthogonality relation and the absence of base points follow. Source: G. Frobenius, Über die
Grundlagen der Theorie der Jacobischen Functionen, Crelle 97 (1884); Birkenhake–Lange, Complex
Abelian Varieties, 3.2.7, 4.1.5, 6.4; survey of proofs in D. Bump, A. Pekker, Proc. AMS 130 (2002)
3473–3481.

See also `Lib.Shimura.Uniformisation.AppellHumbert`.
-/

noncomputable section

namespace New

open FourierTransform Complex Module MeasureTheory QuotientAddGroup Fintype Quotient
  LinearMap.BilinForm Submodule Finset ComplexConjugate IsZLattice

variable {V : Type} [FinComplexSpace V]
  {L : Submodule ℤ V} [IsFullRankLattice L] {B : ThetaTori.LatticeForm L}
  {χ f : V → ℂ} [hB : IsAppellHumbert B χ] [hp : IsPosRiemann B] (hf : f ∈ B.thetaSpace χ)

include hB hf

omit hp

omit hf

/-! ### Convergence of theta series -/

/-- Normal convergence of theta series, for Appell–Humbert data (B, χ) (instance `hB`). Let `T c`,
for `c` in a finite-dimensional complex space `P`, be real-linear maps of `V`, analytic in `c`
near `b`, with `Re (B x (T b x)) > 0` for `x ≠ 0`. The series over `l ∈ L` with terms
`term q l = exp (exponent q l) / χ l`, where
`exponent q l = ξ (u + T c l) - B l z - B l (T c l) / 2` at `q = (c, ξ, u, z)`, converges at
`c = b` for every `p = (ξ, u, z)`, and its sum is analytic in `q` at `(b, p)`. -/
lemma IsAppellHumbert.summable_and_analyticAt_tsum {P : Type*} {b : P} [FinComplexSpace P]
    {T : P → V →L[ℝ] V} (hT : ∀ᶠ c : P in nhds b, ∀ x : V, AnalyticAt ℂ (fun c' : P ↦ T c' x) c)
    (hpos : ∀ x ≠ (0 : V), 0 < (B x (T b x)).re) (p : StrongDual ℂ V × V × V) :
    let exponent : P × StrongDual ℂ V × V × V → V → ℂ :=
      fun (c, ξ, u, z) (l : V) ↦ ξ (u + T c l) - B l z - B l (T c l) / 2
    let term (q : P × StrongDual ℂ V × V × V) (l : L) : ℂ := (exponent q l).exp / χ l
    Summable (term (b, p)) ∧ AnalyticAt ℂ (fun q : P × StrongDual ℂ V × V × V ↦ tsum (term q))
      (b, p) := by
  -- Near `(b, p)` the terms are bounded by a constant times `exp (-‖l‖)`, which is summable
  -- over the lattice; then differentiate under the sum.
  intro exponent term
  have T_cont : ContinuousAt T b :=
    continuousAt_clm_apply.2 fun x ↦ (hT.self_of_nhds x).continuousAt
  -- A homogenised bound on the unit sphere of `ℝ × V`, with a small extra parameter `ε`: here
  -- `r = (ε, c, ξ, u, z)`, so `r.2.1 = c` and `r.2.2 = (ξ, u, z)`, and `y = (s, x)`. At `ε = 0` it
  -- says `-Re (B x (T b x)) / 2 < s ^ 2`, true as `(s, x) ≠ 0`; it persists nearby.
  have on_sphere :
      ∀ᶠ r : ℝ × P × StrongDual ℂ V × V × V in nhds (0, b, p), ∀ y ∈ Metric.sphere (0 : ℝ × V) 1,
        (exponent (r.2.1, (y.1 * r.1) • r.2.2) y.2).re + y.1 * r.1 * ‖y.2‖ < y.1 ^ 2 := by
    refine (isCompact_sphere 0 1).eventually_forall_of_forall_eventually fun (s, x) hx ↦
      ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) ?_
    -- At `r = (0, b, p)` the left side is `-Re (B x (T b x)) / 2`: negative if `x ≠ 0`, and zero
    -- if `x = 0`, when `s ≠ 0` as `(s, x)` lies on the sphere.
    have h_base : -((B x (T b x)).re / 2) < s ^ 2 := by
      rcases eq_or_ne x 0 with rfl | hx_ne
      · have hs_ne : s ≠ 0 := fun hs ↦ by simp [hs] at hx
        simpa using sq_pos_of_ne_zero hs_ne
      · linarith [hpos x hx_ne, sq_nonneg s]
    simpa [exponent] using h_base
  obtain ⟨scale, h_scale_pos, near⟩ :
      ∃ scale > (0 : ℝ), ∀ᶠ q : P × StrongDual ℂ V × V × V in nhds (b, p),
      ∀ y ∈ Metric.sphere (0 : ℝ × V) 1,
        (exponent (q.1, (y.1 * scale) • q.2) y.2).re + y.1 * scale * ‖y.2‖ < y.1 ^ 2 :=
    on_sphere.curry_nhds.exists_gt
  -- `exp (-‖l‖)` decays faster than the power `‖l‖ ^ (-rank L - 1)`, which is summable over `L`.
  have norm_tendsto : Filter.Tendsto (fun l : L ↦ ‖(l : V)‖) Filter.cofinite Filter.atTop :=
    tendsto_norm_cocompact_atTop.comp
      (L.toAddSubgroup.tendsto_coe_cofinite_of_isDiscrete
        ⟨inferInstanceAs (DiscreteTopology L)⟩)
  have h_isBigO : (fun l : L ↦ Real.exp (-1 * ‖(l : V)‖)) =O[Filter.cofinite]
      fun l : L ↦ ‖(l : V)‖ ^ (-(Module.finrank ℤ L : ℝ) - 1) :=
    (isLittleO_exp_neg_mul_rpow_atTop one_pos _).isBigO.comp_tendsto norm_tendsto
  let g (l : L) : ℝ := Real.exp (scale⁻¹ ^ 2) * Real.exp (-1 * ‖(l : V)‖)
  have g_summable : Summable g :=
    (summable_of_isBigO (ZLattice.summable_norm_rpow L _ (sub_one_lt _)) h_isBigO).mul_left _
  -- At the point of the sphere in the direction `(scale⁻¹, l)` all terms are homogeneous of degree
  -- two, and the bound reads `Re (exponent q l) + ‖l‖ < scale⁻¹ ^ 2`.
  have bound : ∀ᶠ q in nhds (b, p), ∀ l, ‖term q l‖ ≤ g l := by
    filter_upwards [near] with q hq l
    have h_unit : NormedSpace.normalize (scale⁻¹, (l : V)) ∈ Metric.sphere (0 : ℝ × V) 1 := by
      simp [h_scale_pos.ne']
    -- Multiply the bound at this unit vector by the square of the norm of `(scale⁻¹, l)`.
    have h_re : (exponent q l).re + ‖(l : V)‖ ≤ scale⁻¹ ^ 2 := by
      simpa [exponent, -Prod.norm_mk, h_scale_pos.ne', NormedSpace.normalize, norm_smul, fieldLe]
        using (hq _ h_unit).le
    calc ‖term q l‖
      _ = Real.exp (exponent q l).re := by simp [term, norm_exp, hB.norm_eq_one _ l.prop]
      _ ≤ Real.exp (scale⁻¹ ^ 2 - ‖(l : V)‖) := Real.exp_le_exp.mpr (by linarith)
      _ = g l := by simp [g, sub_eq_add_neg, Real.exp_add]
  refine ⟨g_summable.of_norm_bounded bound.self_of_nhds, ?_⟩
  -- The sum is an integral against counting measure.
  borelize V
  have dominated : ∀ᶠ q in nhds (b, p), ∀ l,
      DifferentiableAt ℂ (fun q ↦ term q l) q ∧ ‖term q l‖ ≤ g l := by
    filter_upwards [bound, hT.prod_inl_nhds p] with q hq T_an l
    exact ⟨by fun_prop, hq l⟩
  have h_analytic_integral :
      AnalyticAt ℂ (fun q ↦ ∫ l, term q l ∂Measure.count) (b, p) :=
    analyticAt_of_eventually_differentiableAt
      (eventually_differentiableAt_integral (integrable_count_iff.2 g_summable.abs) (by fun_prop)
        dominated)
  simpa [integral_count_eq_tsum] using h_analytic_integral

/-- Let `L` be a full-rank lattice in a finite-dimensional complex space `V`, and let (B, χ) be
Appell–Humbert data (instance `hB`) with `Re B(x, x) > 0` for `x ≠ 0`. The Poincaré series
`K(x, y) = ∑_{l ∈ L} exp(B(x, y − x + l) − B(l, y) − B(l, l)/2)/χ(l)` has these properties: (a) it
converges for all `x, y`; (b) it is jointly continuous in `(x, y)`; (c) for each `x` it is a theta
function of type (B, χ) in `y`; (d) the diagonal `x ↦ K(x, x)` has mean `(χ 0)⁻¹` over `V ⧸ L`; and
(e) it does not vanish at some point `(w, w)`. -/
lemma IsAppellHumbert.poincareSeries_mem_thetaSpace_and_quotMean
    (h_pos : ∀ x ≠ (0 : V), 0 < (B x x).re) :
    -- (a)
    (∀ x y : V, Summable (hB.poincareTerm x y)) ∧
    -- (b)
    Continuous ↿hB.poincareSeries ∧
    -- (c)
    (∀ x : V, hB.poincareSeries x ∈ B.thetaSpace χ) ∧
    -- (d)
    quotMean L.toAddSubgroup (fun x : V ↦ hB.poincareSeries x x) = (χ 0)⁻¹ ∧
    -- (e)
    ∃ w : V, hB.poincareSeries w w ≠ 0 := by
  -- The series is the case `T = 1` of `summable_and_analyticAt_tsum`, at the parameters
  -- `(B x, y - x, y)`; as `T` is constant, any base point `b` serves.
  let t : StrongDual ℂ V × V × V → L → ℂ :=
    fun (ξ, u, z) (l : L) ↦ (ξ (u + l) - B l z - B l l / 2).exp / χ l
  have h_T_an : ∀ᶠ c : ℂ in nhds I, ∀ x : V,
      AnalyticAt ℂ (fun c' : ℂ ↦ (1 : ℂ → V →L[ℝ] V) c' x) c := by simp [analyticAt_const]
  have series (p : StrongDual ℂ V × V × V) :
      Summable (t p) ∧ AnalyticAt ℂ (fun q ↦ tsum (t q)) p :=
    (hB.summable_and_analyticAt_tsum (b := I) (T := 1) h_T_an h_pos p).imp_right
      fun h ↦ h.comp (f := fun q ↦ (I, q)) (by fun_prop)
  have mean : (quotMean L.toAddSubgroup fun x ↦ hB.poincareSeries x x) = (χ 0)⁻¹ := by
    -- On the diagonal the series is `∑ l, 𝐞 (B.riemannForm x l) * t 0 l`, a Fourier series on
    -- `V ⧸ L`; its mean is the coefficient at `l = 0`.
    have h_term (x : V) (l : L) : hB.poincareTerm x x l = 𝐞 (B.riemannForm x l) * t 0 l := by
      simp [t, poincareTerm, exp_sub, ← hB.sub_eq_riemannForm, field]
    have coef : ∑' l : ({0} : Set L), t 0 l =
        quotMean L.toAddSubgroup fun x ↦ ∑' l : L, 𝐞 (B.riemannForm x l) * t 0 l :=
      (isPosRiemann_of_re_pos h_pos).isDualFamily.tsum_coeff_eq_quotMean
        (fun l : L ↦ ⟨l, hB.le_dualLattice l.prop⟩) (S := {0}) (by simp) (series 0).1
    have h_series (x : V) : hB.poincareSeries x x = ∑' l : L, 𝐞 (B.riemannForm x l) * t 0 l := by
      simp only [poincareSeries]
      exact tsum_congr (h_term x)
    simp only [h_series, ← coef]
    simp [t]
  refine ⟨fun x y ↦ (series (B x, y - x, y)).1, ?_, fun x ↦ ⟨fun y ↦ ?_, fun m hm z ↦ ?_⟩, mean, ?_⟩
  · exact (AnalyticOnNhd.continuous fun p _ ↦ (series p).2).comp
      (f := fun p : V × V ↦ (B p.1, p.2 - p.1, p.2)) (by fun_prop)
  · exact (series _).2.differentiableAt.comp (f := fun y ↦ (B x, y - x, y)) y (by fun_prop)
  · -- Translating `z` by `m` shifts the summation index by `m`, up to the factor of automorphy:
    -- use the cocycle rule for `χ (m + l)` and `B m l - B l m = 2 π I * B.riemannForm m l`.
    have shift (l : L) : hB.poincareTerm x (z + m) l =
        χ m * (B m z + B m m / 2).exp * hB.poincareTerm x z (Equiv.addLeft ⟨m, hm⟩ l) := by
      have hχ_m : χ m ≠ 0 := hB.ne_zero hm
      have hχ_l : χ l ≠ 0 := hB.ne_zero l.prop
      simp [poincareTerm, hB.semicharacter, hm, field, ← exp_add]
      -- The exponents differ by `(B m l - B l m) / 2 + π I E(l, m)`, which is zero.
      congr 1
      linear_combination (-1 / 2 : ℂ) * hB.sub_eq_riemannForm (l : V) m
    rw [poincareSeries, tsum_congr shift, tsum_mul_left, Equiv.tsum_eq, poincareSeries]
  · -- A function with nonzero mean is not identically zero.
    contrapose! mean
    simp [mean, hB.ne_zero, eq_comm]

omit [IsFullRankLattice L] in
/-- The form `B (I • u) v + I * B u v`, which is `2 I` times the part of `B` that is complex-linear
in the first variable, is symmetric. -/
lemma IsAppellHumbert.linearPart_symm (u v : V) :
    B (I • u) v + I * B u v = B (I • v) u + I * B v u := by
  simpa [Complex.ext_iff, hB.re_symm, add_comm] using hB.re_symm (I • u) (I • v)

include hp

/-- For Appell–Humbert data (B, χ) (instance `hB`) whose Riemann form is positive (instance `hp`)
there is a nonzero theta function of type (B, χ). -/
lemma IsAppellHumbert.exists_mem_thetaSpace_ne_zero : ∃ f ∈ B.thetaSpace χ, f ≠ 0 := by
  -- `T` is minus the part of `B` that is complex-linear in the first variable, so that `B + T` is
  -- hermitian, with the same Riemann form. Its Poincaré series is not zero at some point `(w, w)`.
  let T : RealComplexForm V := (I / 2) • (B ∘L .lsmul ℝ ℂ I + I • B)
  have T_symm {u v : V} : T u v = T v u :=
    congrArg (fun w : ℂ ↦ I / 2 * w) (hB.linearPart_symm u v)
  -- As `T` is symmetric, its Riemann form vanishes, and `(B + T, χ)` are Appell–Humbert data.
  have h_riem : (B + T).riemannForm = B.riemannForm := by
    ext u v
    simp [riemannForm_def, T_symm]
  have hB' : IsAppellHumbert (B + T) χ :=
    { re_symm := fun u v ↦ by simp [hB.re_symm u v, T_symm]
      norm_eq_one := hB.norm_eq_one
      semicharacter := by simpa [h_riem] using hB.semicharacter }
  -- The real part of `(B + T) x x` is `π E(x, i x)`, positive for `x ≠ 0`.
  have h_re (x : V) : ((B + T) x x).re = Real.pi * B.riemannForm x (I • x) := by
    simp [T, riemannForm_def, field]
    ring
  have pos : ∀ x ≠ 0, 0 < ((B + T) x x).re := fun x hx ↦ by
    rw [h_re x]
    exact mul_pos Real.pi_pos (hp.riemannForm_pos x hx)
  obtain ⟨-, -, series_mem, -, w, hw⟩ := hB'.poincareSeries_mem_thetaSpace_and_quotMean pos
  -- A factor without zeros carries theta functions for `B + T` to theta functions for `B`.
  have mem : (fun z ↦ ((B z z - (B + T) z z) / 2).exp * hB'.poincareSeries w z) ∈
      B.thetaSpace χ :=
    hB'.exp_mul_mem_thetaSpace hB h_riem (fun _ _ ↦ rfl) (series_mem w)
  exact ⟨_, mem, fun h_zero ↦ mul_ne_zero (exp_ne_zero _) hw (congrFun h_zero w)⟩

/-- For Appell–Humbert data (B, χ) with positive Riemann form (instances `hB`, `hp`), `L` has finite
index in its dual lattice, as both are full lattices. -/
lemma IsAppellHumbert.finite_dualLattice_quotient :
    Finite (B.dualLattice ⧸ (L.submoduleOf B.dualLattice).toAddSubgroup) := by
  refine (finiteQuotient_iff _).mpr ?_
  simp [ZLattice.rank ℝ, (submoduleOfEquivOfLe hB.le_dualLattice).finrank_eq]

/-- The form `T u v = (i / 2) (C (i u) v + i C u v)`, which is minus the part of `C` that is
complex-linear in the first variable. -/
private def linearPartForm (C : RealComplexForm V) : RealComplexForm V :=
  (I / 2) • (C ∘L .lsmul ℝ ℂ I + I • C)

omit [IsFullRankLattice L] hB hp in
/-- The twisted translates of a theta function `f`, `(u, z) ↦ thetaShift B u f z`, form a continuous
function of two variables. -/
private lemma continuous_uncurry_thetaShift (f : B.thetaSpace χ) :
    Continuous ↿(fun u : V ↦ B.thetaShift u f) :=
  .mul (by fun_prop) ((differentiable_of_mem_thetaSpace f.prop).continuous.comp (by fun_prop))

/-- For tuples `s`, `t` of theta functions, the function
`x ↦ exp (T b b / 2) * ∑ i, conj ((thetaShift x (s i)) 0) * (thetaShift x (t i)) b` on `V`, with `T`
the form `linearPartForm B`. Its mean over `V ⧸ L` pairs `s` with `t`. -/
private def pairingIntegrand {n : ℕ} (s t : Fin n → B.thetaSpace χ) (b : V) : V → ℂ :=
  fun x : V ↦
    (linearPartForm B b b / 2).exp *
      ∑ i : Fin n, conj (B.thetaShift x (s i) 0) * B.thetaShift x (t i) b

omit [IsFullRankLattice L] hp in
/-- The integrand `pairingIntegrand s t b` is continuous and periodic under `L`. -/
private lemma isContPeriodic_pairingIntegrand {n : ℕ}
    (s t : Fin n → B.thetaSpace χ) (b : V) :
    IsContPeriodic L.toAddSubgroup (pairingIntegrand s t b) := by
  refine ⟨?_, fun l hl x ↦ ?_⟩
  · have shift_cont := continuous_uncurry_thetaShift (B := B) (χ := χ)
    unfold pairingIntegrand
    fun_prop
  -- Translating by `l ∈ L` multiplies every translate of a theta function by one scalar `c`, and
  -- `conj c * c = ‖c‖ ^ 2 = 1`.
  let c : ℂ := exp (-(Real.pi * I * B.riemannForm x l)) * χ l
  have h_shift (f : B.thetaSpace χ) : B.thetaShift (l + x) f = c • B.thetaShift x f := by
    rw [add_comm l x]
    exact hB.thetaShift_add_eq_smul_of_mem f.prop x hl
  have h_norm_c : ‖c‖ = 1 := by simp [c, norm_exp, hB.norm_eq_one l hl]
  have h_conj_mul : conj c * c = 1 := by simp [conj_mul', h_norm_c]
  simp [pairingIntegrand, h_shift, mul_mul_mul_comm _ (conj _), h_conj_mul]

/-- The mean over `V ⧸ L` of `pairingIntegrand s t b`; at `b = 0` it is the inner product of the
tuples `s` and `t` of theta functions. -/
private def pairingMean {n : ℕ} (s t : Fin n → B.thetaSpace χ) (b : V) : ℂ :=
  quotMean L.toAddSubgroup (pairingIntegrand s t b)

omit hp in
/-- The mean `pairingMean s t` is holomorphic in `b`. -/
private lemma differentiable_pairingMean {n : ℕ} (s t : Fin n → B.thetaSpace χ) :
    Differentiable ℂ (pairingMean s t) := by
  -- `T = linearPartForm B` is symmetric, so `b ↦ T b b` is holomorphic; `fun_prop` below uses
  -- `T_symm` and `shift_cont`.
  have T_symm {u v : V} : linearPartForm B u v = linearPartForm B v u :=
    congrArg (fun z : ℂ ↦ I / 2 * z) (hB.linearPart_symm u v)
  have shift_cont (f : B.thetaSpace χ) : Continuous ↿(fun u : V ↦ B.thetaShift u f) :=
    continuous_uncurry_thetaShift f
  -- By periodicity the integrand does not depend on the representative of a class of `V ⧸ L`.
  have h_out (c x : V) : pairingIntegrand s t c (QuotientAddGroup.mk x : V ⧸ L.toAddSubgroup).out =
      pairingIntegrand s t c x :=
    (isContPeriodic_pairingIntegrand s t c).apply_out_mk x
  -- The integrand at representatives is continuous in `(b, q)` and holomorphic in `b`.
  have h_cont (a : V) (q : V ⧸ L.toAddSubgroup) :
      ContinuousAt
        (Function.uncurry fun (c : V) (q : V ⧸ L.toAddSubgroup) ↦ pairingIntegrand s t c (out q))
        (a, q) := by
    refine ((isQuotientMap_mk _).continuous_lift_prod_right ?_).continuousAt
    simp only [Function.uncurry_apply_pair, h_out]
    simp only [pairingIntegrand]
    fun_prop
  have h_diff (a : V) (q : V ⧸ L.toAddSubgroup) :
      DifferentiableAt ℂ (fun c : V ↦ pairingIntegrand s t c (out q)) a := by
    have t_diff (i : Fin n) := differentiable_of_mem_thetaSpace (t i).prop
    simp only [pairingIntegrand]
    fun_prop
  -- Hence the integrand is an analytic family, and its mean over `V ⧸ L` is analytic.
  exact fun b ↦ ((isAnalyticFamily_of_differentiable
    (.of_forall fun a q ↦ ⟨h_cont a q, h_diff a q⟩)).analyticAt_integral _).differentiableAt

omit hp in
/-- Swapping the tuples and the sign of `b` conjugates `pairingMean`, the mean over `V ⧸ L` of
`pairingIntegrand s t b`. -/
private lemma pairingMean_neg {n : ℕ} (s t : Fin n → B.thetaSpace χ) (b : V) :
    pairingMean t s (-b) = conj (pairingMean s t b) := by
  -- After translating the mean by `b`, the integrands agree up to conjugation: the theta values
  -- match, and so do the exponents, written here as they appear after unfolding.
  have h_exponent (x : V) :
      (I / 2 * B (I • b) b + I / 2 * I * B b b) / 2 +
          (-((conj (B x x) + conj (B x b) + (conj (B b x) + conj (B b b))) / 2) +
            (-((B x x + B x b + (B b x + B b b)) / 2) + (B b b + B x b))) =
        (-(I / 2 * conj (B (I • b) b)) + I / 2 * I * conj (B b b)) / 2 +
          (-(B x x / 2) + (-(conj (B x x) / 2) + -conj (B x b))) := by
    apply Complex.ext
    · -- real parts: `Re (B x b) = Re (B b x)`
      simp [hB.re_symm]
      ring
    · -- imaginary parts: `Re (B (I • b) b) = Re (B b (I • b)) = -Im (B b b)`
      simp [hB.re_symm, neg_div]
      ring
  have h_integrand (x : V) :
      pairingIntegrand t s (-b) (x + b) = conj (pairingIntegrand s t b x) := by
    simp [pairingIntegrand, linearPartForm, mul_sum, thetaShift_apply_apply, ← exp_conj,
      ← mul_assoc, mul_right_comm _ (conj _), conj_ofNat, ← exp_add, neg_div, map_sum,
      add_comm b x, h_exponent]
  calc pairingMean t s (-b)
      = quotMean L.toAddSubgroup fun x ↦ pairingIntegrand t s (-b) (x + b) :=
        (quotMean_translate (isContPeriodic_pairingIntegrand t s (-b)) b).symm
    _ = quotMean L.toAddSubgroup fun x ↦ conj (pairingIntegrand s t b x) := by
        simp only [h_integrand]
    _ = conj (pairingMean s t b) := by simp [pairingMean, quotMean, ← integral_conj]

omit hp in
/-- Liouville's theorem applied to the mean `m = pairingMean`: if `m s t 0 = 0`, then `m t s`
vanishes everywhere. -/
private lemma pairingMean_eq_zero_of_eq_zero {n : ℕ}
    {s t : Fin n → B.thetaSpace χ} (h_zero : pairingMean s t 0 = 0) (b : V) :
    pairingMean t s b = 0 := by
  -- `exp (-m s t (-b) * m t s b) = exp (-‖m t s b‖ ^ 2)` is entire and bounded by `1`, so it keeps
  -- its value `1` at `b = 0`.
  have h_entire : Differentiable ℂ fun b ↦ exp (-pairingMean s t (-b) * pairingMean t s b) :=
    (((differentiable_pairingMean s t).comp differentiable_id.neg).neg.mul
      (differentiable_pairingMean t s)).cexp
  have h_bound (c : V) : ‖exp (-pairingMean s t (-c) * pairingMean t s c)‖ ≤ 1 := by
    simp [pairingMean_neg, mul_nonneg, conj_mul', sq, norm_exp]
  have h_const : exp (-pairingMean s t (-b) * pairingMean t s b) =
      exp (-pairingMean s t (-0) * pairingMean t s 0) :=
    h_entire.apply_eq_apply_of_bounded
      (isBounded_iff_forall_norm_le.mpr ⟨1, Set.forall_mem_range.mpr h_bound⟩) b 0
  simpa [pairingMean_neg, h_zero, conj_mul', sq, norm_exp] using congrArg norm h_const

/-- Upper bound for the dimension. Let `(B, χ)` be Appell–Humbert data with positive Riemann form
for a full-rank lattice `L` in `V`. If there are `n` linearly independent theta functions `s i` of
type `(B, χ)`, then there is an injective `ℂ`-linear map from `n`-tuples of such theta functions to
the functions on the dual lattice `B.dualLattice` modulo `L`. -/
lemma IsAppellHumbert.exists_injective_to_dual_quotient {n : ℕ} {s : Fin n → B.thetaSpace χ}
    (hs : LinearIndependent ℂ s) :
    ∃ ψ : (Fin n → B.thetaSpace χ) →ₗ[ℂ]
        (B.dualLattice ⧸ (L.submoduleOf B.dualLattice).toAddSubgroup → ℂ),
      Function.Injective ψ := by
  let pairingAt (q : B.dualLattice ⧸ (L.submoduleOf B.dualLattice).toAddSubgroup) :
      (Fin n → B.thetaSpace χ) →ₗ[ℂ] ℂ :=
    { toFun t := pairingMean (thetaShiftEnd q.out ∘ s) t 0
      map_add' t t' := by
        -- The integrand is additive in `t`, and the integrands are integrable.
        have h_add (x : V) :
            pairingIntegrand (thetaShiftEnd q.out ∘ s) (t + t') 0 x =
              pairingIntegrand (thetaShiftEnd q.out ∘ s) t 0 x +
                pairingIntegrand (thetaShiftEnd q.out ∘ s) t' 0 x := by
          simp [pairingIntegrand, mul_add, sum_add_distrib]
        have h_per (u : Fin n → B.thetaSpace χ) :
            IsContPeriodic L.toAddSubgroup (pairingIntegrand (thetaShiftEnd q.out ∘ s) u 0) :=
          isContPeriodic_pairingIntegrand _ u 0
        simp only [pairingMean, quotMean, h_add]
        exact integral_add (h_per t).integrable_out (h_per t').integrable_out
      map_smul' c t := by
        unfold pairingMean pairingIntegrand
        simp [mul_left_comm, ← mul_sum] }
  refine ⟨.pi pairingAt, (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_⟩
  -- Up to a non-zero factor, `pairingMean t (thetaShiftEnd a ∘ s) (b - a)` is the Fourier
  -- coefficient of `pairingIntegrand t s b` at the character of `a`; changing `a` by an element of
  -- `L` only changes the factor.
  have coef_zero (b : V) (a : B.dualLattice) :
      quotMean L.toAddSubgroup (fun x ↦ 𝐞 (B.riemannForm x a) * pairingIntegrand t s b x) =
        0 := by
    -- The chosen representative of the class of `a` is `a + l` with `l ∈ L`.
    obtain ⟨⟨l, hl : (l : V) ∈ L⟩, out_eq⟩ := mk_out_eq_add (L.submoduleOf _).toAddSubgroup a
    have inner_zero : pairingMean (thetaShiftEnd (a + l) ∘ s) t 0 = 0 := by
      rw [← out_eq]
      exact congrFun ht _
    have shifted : pairingMean t (thetaShiftEnd (a + l) ∘ s) (b - a) = 0 :=
      pairingMean_eq_zero_of_eq_zero inner_zero (b - a)
    -- Translating `s i` by `a + l` gives `χ l`, a phase and the translate by `a`; moving that past
    -- the translation by `x` gives the character `𝐞 (E(x, a))` (`thetaShift_comm`), and evaluating
    -- at `b - a` moves the argument back to `b`.
    have h_term (x : V) (i : Fin n) :
        B.thetaShift x ((thetaShiftEnd (a + l) ∘ s) i : V → ℂ) (b - a) =
          exp (-(Real.pi * I * B.riemannForm a l)) * χ l * 𝐞 (B.riemannForm x a) *
            exp (-(B a (b - a) + B a a / 2)) * B.thetaShift x (s i) b := by
      rw [Function.comp_apply, LinearMap.coe_restrict_apply, Submodule.coe_add,
        hB.thetaShift_add_eq_smul_of_mem (s i).prop (a : V) hl, map_smul, Pi.smul_apply,
        hB.thetaShift_comm x (a : V), Pi.smul_apply, thetaShift_apply_apply (a := (a : V)),
        sub_add_cancel, smul_eq_mul, smul_eq_mul]
      ring
    -- So the integrand is `c` times `𝐞 (E(x, a))` times the integrand for `s` at `b`.
    let c : ℂ := exp (linearPartForm B (b - a) (b - a) / 2) * exp (-(B a (b - a) + B a a / 2)) *
        (exp (-(Real.pi * I * B.riemannForm a l)) * χ l) / exp (linearPartForm B b b / 2)
    have hc_ne : c ≠ 0 := by simp [c, hB.ne_zero hl]
    have h_integrand : pairingIntegrand t (thetaShiftEnd (a + l) ∘ s) (b - a) =
        fun x ↦ c * (𝐞 (B.riemannForm x a) * pairingIntegrand t s b x) := by
      funext x
      simp only [pairingIntegrand, h_term, c, mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      field_simp
    have h_mean : c * quotMean L.toAddSubgroup
        (fun x ↦ 𝐞 (B.riemannForm x a) * pairingIntegrand t s b x) = 0 := by
      rwa [← quotMean_const_mul, ← h_integrand]
    exact (mul_eq_zero.mp h_mean).resolve_left hc_ne
  -- So `pairingIntegrand t s` vanishes, which says that `∑ i, conj (t i y) • s i = 0`.
  ext i y
  have relation : ∑ i, conj ((t i : V → ℂ) y) • s i = 0 := by
    ext x
    simpa [pairingIntegrand, thetaShift_apply_apply, mul_mul_mul_comm, ← mul_sum] using
      hp.isDualFamily.eq_zero_of_quotMean_mul_eq_zero (isContPeriodic_pairingIntegrand t s (x - y))
        (fun a _ ↦ coef_zero _ a) y
  simpa using Fintype.linearIndependent_iff.mp hs _ relation i

/-- For Appell–Humbert data with positive Riemann form, the space of theta functions has finite
dimension. -/
lemma IsAppellHumbert.finite_thetaSpace : Module.Finite ℂ (B.thetaSpace χ) := by
  -- The space embeds in the functions on the dual lattice modulo `L`, a finite group.
  obtain ⟨f, hf, hf_ne⟩ : ∃ f ∈ B.thetaSpace χ, f ≠ 0 := hB.exists_mem_thetaSpace_ne_zero
  have := hB.finite_dualLattice_quotient
  have h_indep : LinearIndependent ℂ ![(⟨f, hf⟩ : B.thetaSpace χ)] := by simpa using hf_ne
  obtain ⟨ψ, hψ_inj⟩ := hB.exists_injective_to_dual_quotient h_indep
  have h_finite_tuples : Module.Finite ℂ (Fin 1 → B.thetaSpace χ) := .of_injective ψ hψ_inj
  exact Finite.pi_iff.mp h_finite_tuples 0

/-- For Appell–Humbert data with positive Riemann form, the space of theta functions has positive
dimension. -/
lemma IsAppellHumbert.finrank_thetaSpace_pos : 0 < finrank ℂ (B.thetaSpace χ) := by
  obtain ⟨f, hf, hf_ne⟩ : ∃ f ∈ B.thetaSpace χ, f ≠ 0 := hB.exists_mem_thetaSpace_ne_zero
  have h_finite : Module.Finite ℂ (B.thetaSpace χ) := hB.finite_thetaSpace
  exact finrank_pos_iff_exists_ne_zero.mpr ⟨⟨f, hf⟩, by simpa using hf_ne⟩

/-- For Appell–Humbert data with positive Riemann form, the twisted translations
`New.IsAppellHumbert.thetaShiftEnd` by representatives of the dual lattice modulo `L` are linearly
independent endomorphisms of the space of theta functions. -/
lemma IsAppellHumbert.linearIndependent_thetaShiftEnd_out :
    LinearIndependent ℂ fun q : B.dualLattice ⧸ (L.submoduleOf B.dualLattice).toAddSubgroup ↦
      hB.thetaShiftEnd q.out := by
  -- They are simultaneous eigenvectors of the conjugations by all `thetaShiftEnd y`, for distinct
  -- characters `e q`.
  let N : AddSubgroup B.dualLattice := (L.submoduleOf B.dualLattice).toAddSubgroup
  let e (q : B.dualLattice ⧸ N) (y : B.dualLattice) : ℂ := B.riemannPhase q.out (y : V)
  have e_inj : e.Injective := by
    intro q q' h_eq
    -- Equal characters give `𝐞 (E (-q + q', y)) = 1` for all `y`, so `-q + q'` lies in `L`.
    refine out_equiv_out.mp (leftRel_apply.mpr (hp.isDualFamily.mem_of_forall_eq_one _ ?_))
    show ∀ y : B.dualLattice, (𝐞 (B.riemannForm ((-out q + out q' : B.dualLattice) : V) y) : ℂ) = 1
    intro y
    have h_phase : (𝐞 (B.riemannForm ((q.out : B.dualLattice) : V) y) : ℂ) =
        𝐞 (B.riemannForm ((q'.out : B.dualLattice) : V) y) :=
      congrFun h_eq y
    simp [neg_add_eq_sub, AddChar.map_sub_eq_div, h_phase]
  let conjugation (y : B.dualLattice) : End ℂ (End ℂ (B.thetaSpace χ)) :=
    .mulLeftRight ℂ (hB.thetaShiftEnd (-y), hB.thetaShiftEnd y)
  have eigen (q : B.dualLattice ⧸ N) :
      hB.thetaShiftEnd q.out ∈ ⨅ y, (conjugation y).eigenspace (e q y) := by
    -- `T(-y) T(y) = 1`, and `T(q) T(y) = e q y • T(y) T(q)` (`thetaShift_comm`): conjugating
    -- `T(q)` by `T(y)` multiplies it by `e q y`.
    have h_conj (y : B.dualLattice) (g : V → ℂ) :
        B.thetaShift (-(y : V)) (B.thetaShift q.out (B.thetaShift y g)) =
          e q y • B.thetaShift q.out g := by
      have h_inv (g : V → ℂ) : B.thetaShift (-y : V) (B.thetaShift y g) = g := by
        simp [hB.thetaShift_thetaShift]
      rw [hB.thetaShift_comm ((q.out : B.dualLattice) : V) (y : V), map_smul, h_inv]
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    refine fun y ↦ LinearMap.ext fun g ↦ Subtype.ext ?_
    simpa [conjugation] using h_conj y g
  have shift_ne (q : B.dualLattice ⧸ N) : hB.thetaShiftEnd q.out ≠ 0 := by
    obtain ⟨f, hf, hf_ne⟩ : ∃ f ∈ B.thetaSpace χ, f ≠ 0 := hB.exists_mem_thetaSpace_ne_zero
    obtain ⟨w, hw⟩ : ∃ w : V, f w ≠ 0 := Function.ne_iff.mp hf_ne
    intro h_zero
    -- The translate of `f` would vanish at `w - q.out`, where it is a nonzero multiple of `f w`.
    have h_value := congrArg (fun T ↦ (T ⟨f, hf⟩ : V → ℂ) (w - q.out)) h_zero
    simp [thetaShift_apply_apply, hw] at h_value
  have indep : iSupIndep fun c : B.dualLattice → ℂ ↦ ⨅ y, (conjugation y).eigenspace (c y) :=
    iSupIndep.iInf _ fun y ↦ (conjugation y).eigenspaces_iSupIndep
  exact (indep.comp e_inj).linearIndependent _ eigen shift_ne

/-- For Appell–Humbert data with positive Riemann form, the index of `L` in its dual lattice is the
dimension of the endomorphism algebra of the space of theta functions. -/
lemma IsAppellHumbert.relIndex_dualLattice_eq_finrank_end :
    L.toAddSubgroup.relIndex B.dualLattice.toAddSubgroup =
      finrank ℂ (End ℂ (B.thetaSpace χ)) := by
  -- With `n` the dimension of the space of theta functions, independence of the translations gives
  -- index `≤ n ^ 2`, and the embedding of `n`-tuples gives `n ^ 2 ≤` index.
  let N : AddSubgroup B.dualLattice := (L.submoduleOf B.dualLattice).toAddSubgroup
  have := hB.finite_dualLattice_quotient
  have h_fintype_quot : Fintype (B.dualLattice ⧸ N) := Fintype.ofFinite (B.dualLattice ⧸ N)
  have h_finite : Module.Finite ℂ (B.thetaSpace χ) := hB.finite_thetaSpace
  have card_le : card (B.dualLattice ⧸ N) ≤ finrank ℂ (End ℂ (B.thetaSpace χ)) :=
    hB.linearIndependent_thetaShiftEnd_out.fintype_card_le_finrank
  -- A basis of the theta functions gives `n` independent ones, so the `n`-tuples embed.
  have h_embed :
      finrank ℂ (Fin (finrank ℂ (B.thetaSpace χ)) → B.thetaSpace χ) ≤
        finrank ℂ (B.dualLattice ⧸ N → ℂ) :=
    finrank_le_iff_exists_linearMap.mpr
      (hB.exists_injective_to_dual_quotient (finBasis ℂ (B.thetaSpace χ)).linearIndependent)
  have le_card : finrank ℂ (End ℂ (B.thetaSpace χ)) ≤ card (B.dualLattice ⧸ N) := by
    simpa [finrank_linearMap, finrank_pi_fintype] using h_embed
  calc L.toAddSubgroup.relIndex B.dualLattice.toAddSubgroup
    _ = card (B.dualLattice ⧸ N) := card_eq_nat_card.symm
    _ = finrank ℂ (End ℂ (B.thetaSpace χ)) := card_le.antisymm le_card

/-- For Appell–Humbert data with positive Riemann form, the twisted translations by the dual lattice
span the endomorphisms of the space of theta functions.

Known result: irreducibility of the action of the theta group. -/
lemma IsAppellHumbert.span_range_thetaShiftEnd_eq_top :
    span ℂ (Set.range hB.thetaShiftEnd) = ⊤ := by
  -- The translations by representatives modulo `L` are independent and as many as the dimension.
  let N : AddSubgroup B.dualLattice := (L.submoduleOf B.dualLattice).toAddSubgroup
  have := hB.finite_dualLattice_quotient
  have h_fintype_quot : Fintype (B.dualLattice ⧸ N) := Fintype.ofFinite (B.dualLattice ⧸ N)
  have card_eq : card (B.dualLattice ⧸ N) = finrank ℂ (End ℂ (B.thetaSpace χ)) :=
    card_eq_nat_card.trans hB.relIndex_dualLattice_eq_finrank_end
  exact eq_top_mono (span_mono (Set.range_comp_subset_range out hB.thetaShiftEnd))
    (hB.linearIndependent_thetaShiftEnd_out.span_eq_top_of_card_eq_finrank card_eq)

/-- For Appell–Humbert data with positive Riemann form, the square of the dimension of the space of
theta functions is the index of `L` in its dual lattice.

Known result: Frobenius' dimension formula. -/
lemma IsAppellHumbert.finrank_thetaSpace_sq :
    finrank ℂ (B.thetaSpace χ) ^ 2 = L.toAddSubgroup.relIndex B.dualLattice.toAddSubgroup := by
  have := hB.finite_thetaSpace
  simp [hB.relIndex_dualLattice_eq_finrank_end, sq, finrank_linearMap]

/-- Let `(B, χ)` be Appell–Humbert data for `L` with positive Riemann form. (a) The translations by
the dual lattice span the endomorphisms of the space of theta functions. (b) The square of its
dimension is the index of `L` in the dual lattice. (c) The dimension is positive.

Known result: Frobenius' dimension formula and irreducibility of the action of the theta group. -/
lemma IsAppellHumbert.finrank_sq_eq_relIndex :
    span ℂ (Set.range hB.thetaShiftEnd) = ⊤ ∧
    finrank ℂ (B.thetaSpace χ) ^ 2 = L.toAddSubgroup.relIndex B.dualLattice.toAddSubgroup ∧
    0 < finrank ℂ (B.thetaSpace χ) :=
  ⟨hB.span_range_thetaShiftEnd_eq_top, hB.finrank_thetaSpace_sq, hB.finrank_thetaSpace_pos⟩

/-- Irreducibility: for Appell–Humbert data with positive Riemann form, a complex space of
functions that contains all twisted translates, by the dual lattice, of one non-zero theta
function contains every theta function. -/
lemma IsAppellHumbert.thetaSpace_le_of_thetaShift_mem (hf : f ∈ B.thetaSpace χ) (h_ne : f ≠ 0)
    (S : Submodule ℂ (V → ℂ)) (hS : ∀ a ∈ B.dualLattice, B.thetaShift a f ∈ S) :
    B.thetaSpace χ ≤ S := by
  -- The translations span all endomorphisms, among them `ℓ ⊗ g` with `ℓ f = 1`, which maps `f` to
  -- `g`. The endomorphisms that map `f` into `S` form a subspace that contains the translations.
  intro g hg
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual ℂ (V → ℂ), ℓ f = 1 := Projective.exists_dual_eq_one ℂ h_ne
  -- `A` sends `f` to `ℓ f • g = g`.
  let A : End ℂ (B.thetaSpace χ) := (ℓ.domRestrict (B.thetaSpace χ)).smulRight ⟨g, hg⟩
  have hA_apply : A ⟨f, hf⟩ = ⟨g, hg⟩ := by simp [A, hℓ]
  let W : Submodule ℂ (End ℂ (B.thetaSpace χ)) :=
    (S.submoduleOf (B.thetaSpace χ)).comap (.applyₗ ⟨f, hf⟩)
  have hA_mem_span : A ∈ span ℂ (Set.range hB.thetaShiftEnd) :=
    hB.span_range_thetaShiftEnd_eq_top.ge mem_top
  have shift_mem (a : B.dualLattice) : hB.thetaShiftEnd a ∈ W := hS a a.prop
  have hA_mem : A ∈ W := mem_span.mp hA_mem_span W (Set.range_subset_iff.mpr shift_mem)
  -- Membership in `W` says that the value at `f` lies in `S`.
  have h_value_mem : ((A ⟨f, hf⟩ : B.thetaSpace χ) : V → ℂ) ∈ S := hA_mem
  rwa [hA_apply] at h_value_mem

/-- Schur's lemma: for Appell–Humbert data (L, B, χ) with positive Riemann form, a linear
endomorphism of the theta functions of type (B, χ) that commutes with the twisted
translations `New.RealComplexForm.thetaShift` by the dual lattice is a scalar. -/
lemma IsAppellHumbert.schur_lemma {Q : End ℂ (B.thetaSpace χ)}
    (h_comm : ∀ a : B.dualLattice, Commute (hB.thetaShiftEnd a) Q) :
    ∃ c : ℂ, Q = c • 1 := by
  -- `Q` commutes with the span of the translations, which is everything, so it is central.
  have central (A : End ℂ (B.thetaSpace χ)) : Commute A Q :=
    Commute.span_left (Set.forall_mem_range.mpr h_comm) A
      (hB.span_range_thetaShiftEnd_eq_top.ge mem_top)
  exact (Algebra.IsCentral.mem_center_iff ℂ).mp (Subring.mem_center_iff.mpr central)

/-- For Appell–Humbert data with positive Riemann form, some positive integer `N` multiplies every
vector of the dual lattice into `L`. -/
lemma IsAppellHumbert.exists_nsmul_mem_of_mem_dualLattice :
    ∃ N ≠ (0 : ℕ), ∀ a ∈ B.dualLattice, N • a ∈ L := by
  -- Take for `N` the index of `L` in its dual, which is the square of a positive dimension.
  refine ⟨L.toAddSubgroup.relIndex B.dualLattice.toAddSubgroup, ?_,
    fun a ha ↦ L.toAddSubgroup.nsmul_relIndex_mem ha⟩
  simpa [← hB.finrank_thetaSpace_sq] using hB.finrank_thetaSpace_pos.ne'

end New

/-!
## Multiples of a positive type have no base point

Throughout, `L` is a full lattice in a finite-dimensional complex space `V`, and `(B, χ)` are
Appell–Humbert data for `L` (`New.IsAppellHumbert`) whose Riemann form is positive
(`New.IsPosRiemann`).
-/

section BasePointFree

open New ThetaTori thetaSpace Complex

variable {V : Type} [FinComplexSpace V]
  {L : Submodule ℤ V} [IsFullRankLattice L]
  {B : LatticeForm L} {χ : V → ℂ}

/-- Let f and g be entire functions on a finite-dimensional complex space with f·g = 0. If f is not
identically zero, then g is identically zero. -/
lemma New.ThetaTori.eq_zero_of_differentiable_of_mul_eq_zero {f g : V → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : f * g = 0) (hf_ne : f ≠ 0) :
    g = 0 := by
  -- `g` vanishes near a point where `f` does not, hence everywhere by the identity theorem.
  obtain ⟨z, hz⟩ : ∃ z : V, f z ≠ 0 := Function.ne_iff.mp hf_ne
  have h_near : g =ᶠ[nhds z] 0 := by
    filter_upwards [(hf z).continuousAt.eventually_ne hz] with w hw
    exact (mul_eq_zero.mp (congrFun h w)).resolve_left hw
  exact AnalyticOnNhd.eq_of_eventuallyEq
    (fun w _ ↦ analyticAt_of_eventually_differentiableAt (.of_forall hg)) analyticOnNhd_const h_near

/-- For Appell–Humbert data (B, χ) with positive Riemann form and n ≥ 2, the theta functions of
type (nB, χⁿ) have no common zero. -/
lemma New.IsAppellHumbert.exists_mem_thetaSpace_nsmul_apply_ne_zero (hB : IsAppellHumbert B χ)
    [IsPosRiemann B] (z : V) (n : ℕ) (hn : n > 1) : ∃ f ∈ (n • B).thetaSpace (χ ^ n), f z ≠ 0 := by
  -- Take a nonzero theta function `f` of type `(B, χ)` and write the degree as `m + 1`, `m ≥ 1`.
  -- For any `a`, the product of the translates of `f ^ m` by `a` and of `f` by `-m a` has type
  -- `((m + 1) • B, χ ^ (m + 1))`. If all of these vanish at `z`, the product of two nonzero
  -- entire functions of `a` is zero.
  rcases n with _ | m
  · omega
  have hm_ne : m ≠ 0 := by omega
  obtain ⟨f, hf, hf_ne⟩ : ∃ f ∈ B.thetaSpace χ, f ≠ 0 := hB.exists_mem_thetaSpace_ne_zero
  have hf_diff : Differentiable ℂ f := differentiable_of_mem_thetaSpace hf
  by_contra! h_zero
  -- The two factors `exp (± 2 π i m E(l, a))` in the multiplier of the product cancel.
  have h_multiplier (a l : V) :
      (χ ^ m) l * (m • B).riemannPhase l a * (χ l * B.riemannPhase l (-(m : ℝ) • a)) =
        (χ ^ (m + 1)) l := by
    simp [exp_neg, field, pow_succ]
  have h_mem (a : V) : thetaShift (m • B) a (f ^ m) * thetaShift B (-(m : ℝ) • a) f ∈
      ((m + 1) • B).thetaSpace (χ ^ (m + 1)) := by
    refine (mul (thetaShift_mem (pow hf m) a) (thetaShift_mem hf _)).imp_right
      fun h_law l hl w ↦ ?_
    simp only [h_law l hl w, Pi.mul_apply, h_multiplier a l, ← succ_nsmul]
  -- At `z` the product is `f (z + a) ^ m * f (z - m a)` times a nonzero exponential.
  have h_mul : ((fun a ↦ f (z + a)) * fun a ↦ f (z + -(m : ℝ) • a)) = 0 := by
    funext a
    simpa [thetaShift_apply, hm_ne] using h_zero _ (h_mem a)
  have h_left : (fun a ↦ f (z + a)) ≠ 0 := (add_left_surjective z).injective_comp_right.ne hf_ne
  have h_surj : Function.Surjective fun a : V ↦ z + -(m : ℝ) • a :=
    (add_left_surjective z).comp (MulAction.surjective₀ (by simpa using hm_ne))
  have h_right : (fun a ↦ f (z + -(m : ℝ) • a)) = 0 :=
    eq_zero_of_differentiable_of_mul_eq_zero (by fun_prop) (by fun_prop) h_mul h_left
  exact h_surj.injective_comp_right.ne hf_ne h_right

end BasePointFree

/-!
## The canonical multiplier and normalised translations

* `New.ThetaTori.canonicalMultiplier`: for a linear map `b`, the multiplier `exp (π i E(b x, x))`,
  defined on all of `V`. By `New.ThetaTori.isAppellHumbert_canonicalMultiplier` it satisfies the
  Appell–Humbert conditions `New.IsAppellHumbert` if b + b* = 1 (adjoint for `E`), the real part of
  `B` is symmetric and `E(b L, L)` is integral.
* `New.ThetaTori.normalizedShift`: the twisted translation `New.RealComplexForm.thetaShift B x`
  divided by this multiplier. The theta functions are the entire functions fixed by it along `L`
  (`New.ThetaTori.mem_thetaSpace_iff_normalizedShift`). If b + b* = 1 and `B` admits some
  Appell–Humbert multiplier, it obeys the Heisenberg law
  `New.IsAppellHumbert.normalizedShift_normalizedShift`.
-/

namespace New

open Complex Finset ThetaTori

variable {V V' ι : Type} [FinComplexSpace V] [FinComplexSpace V']
  (B : RealComplexForm V) (b : V →L[ℂ] V) {L : Submodule ℤ V}

/-- The canonical multiplier x ↦ exp(πi E(bx, x)) attached to a complex-linear endomorphism b of
V, where E is the Riemann form of B. -/
def ThetaTori.canonicalMultiplier (x : V) : ℂ := Complex.exp (Real.pi * I * B.riemannForm (b x) x)

/-- Normalised translation: the twisted translation by x, divided by the canonical multiplier
exp(πi E(bx, x)). -/
def ThetaTori.normalizedShift (x : V) : (V → ℂ) →ₗ[ℂ] V → ℂ :=
  (canonicalMultiplier B b x)⁻¹ • B.thetaShift x

/-- For the sum of the pull-backs of forms B_i along linear maps A_i, the twisted translate by u of
the product of the f_i∘A_i is the product of the pulled-back translates of f_i by A_i u. -/
lemma thetaShift_prod [Fintype ι] {B : ι → RealComplexForm V} {A : ι → V' →L[ℂ] V} {f : ι → V → ℂ}
    (u : V') :
    thetaShift (∑ i : ι, pullForm (A i) (B i)) u (∏ i : ι, f i ∘ A i) =
      ∏ i : ι, thetaShift (B i) (A i u) (f i) ∘ A i := by
  simp [funext_iff, thetaShift_apply, sum_div, exp_add, exp_neg, exp_sum, prod_mul_distrib]

variable {B : LatticeForm L} {b} {x y : V} {f : V → ℂ}

/-- The theta functions for L, B and the canonical multiplier of b are the entire functions
fixed by the normalised translations by the elements of L. -/
lemma ThetaTori.mem_thetaSpace_iff_normalizedShift :
    f ∈ B.thetaSpace (canonicalMultiplier B b) ↔
      Differentiable ℂ f ∧ ∀ l ∈ L, normalizedShift B b l f = f := by
  refine Iff.and Iff.rfl ?_
  -- Both sides say `f (z + l) = exp (π i E(b l, l)) * exp (B l z + B l l / 2) * f z`.
  simp [mul_right_comm, canonicalMultiplier, exp_add, normalizedShift, funext_iff,
    thetaShift_apply, exp_neg, fieldEq]

/-- Let E be the Riemann form of `B`. If b + b* = 1 for E, that is E(bu, w) + E(u, bw) = E(u, w)
(hypothesis `adj`), the real part of `B` is symmetric and E(b L, L) is integral, then `B` and the
canonical multiplier are Appell–Humbert data for L. -/
lemma ThetaTori.isAppellHumbert_canonicalMultiplier
    (adj : ∀ u w : V, B.riemannForm (b u) w = B.riemannForm u w - B.riemannForm u (b w))
    (re_symm : ∀ u w : V, (B u w).re = (B w u).re)
    (h_int : ∀ l ∈ L, ∀ m ∈ L, ∃ n : ℤ, B.riemannForm (b l) m = n) :
    IsAppellHumbert B (canonicalMultiplier B b) := by
  refine ⟨re_symm, fun l _ ↦ ?_, fun l hl m hm ↦ ?_⟩
  · -- The multiplier is the exponential of an imaginary number.
    simp [norm_exp, canonicalMultiplier]
  -- By `adj`, `E(b l, m) + E(b m, l) = E(m, l) + 2 E(b l, m)`, and `E(b l, m)` is an integer.
  obtain ⟨n, hn⟩ : ∃ n : ℤ, B.riemannForm (b l) m = n := h_int l hl m hm
  have h_riemannForm_add :
      B.riemannForm (b (l + m)) (l + m) =
        B.riemannForm (b l) l + B.riemannForm (b m) m + B.riemannForm m l + 2 * n := by
    simp only [map_add, LinearMap.add_apply]
    linear_combination adj m l - riemannForm_swap (B := B) (b l) m + 2 * hn
  simp only [canonicalMultiplier, ← exp_add, h_riemannForm_add]
  refine exp_eq_exp_iff_exists_int.mpr ⟨n, ?_⟩
  simp [fieldEq]

/-- Heisenberg law: if (L, B, χ) are Appell–Humbert data and E(bu, w) + E(u, bw) = E(u, w), the
normalised translation by y followed by that by x is exp(2πi E(bx, y)) times that by x + y. -/
lemma IsAppellHumbert.normalizedShift_normalizedShift
    (adj : ∀ u w : V, B.riemannForm (b u) w = B.riemannForm u w - B.riemannForm u (b w))
    {χ : V → ℂ} (h : IsAppellHumbert B χ) :
    normalizedShift B b x (normalizedShift B b y f) =
      B.riemannPhase (b x) y • normalizedShift B b (x + y) f := by
  -- The translations compose with the factor `exp (π i E(x, y))` (`thetaShift_thetaShift`); the
  -- multipliers at `x`, `y` and `x + y` contribute `exp (π i (E(b x, y) + E(b y, x)))`, and by
  -- `adj` `E(b y, x) = E(b x, y) - E(x, y)`.
  have h_exponent : B.riemannForm (b y) x = B.riemannForm (b x) y - B.riemannForm x y := by
    linear_combination adj y x - riemannForm_swap (B := B) (b x) y + riemannForm_swap (B := B) x y
  -- The scalar in front of `thetaShift B (x + y) f` on each side.
  have h_mult :
      (canonicalMultiplier B b y)⁻¹ *
          ((canonicalMultiplier B b x)⁻¹ * exp (Real.pi * I * B.riemannForm x y)) =
        B.riemannPhase (b x) y * (canonicalMultiplier B b (x + y))⁻¹ := by
    simp only [canonicalMultiplier, RealComplexForm.riemannPhase, coe_fourierChar_eq_exp,
      ← exp_neg, ← exp_add, map_add, LinearMap.add_apply]
    congr 1
    simp only [h_exponent]
    push_cast
    ring
  simp only [normalizedShift, LinearMap.smul_apply, map_smul, h.thetaShift_thetaShift x y,
    smul_smul, h_mult]

end New

end
