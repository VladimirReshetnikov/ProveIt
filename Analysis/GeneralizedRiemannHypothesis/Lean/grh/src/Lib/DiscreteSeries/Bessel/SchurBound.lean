import Lib.DiscreteSeries.Bessel.Basic

/-!
# Traces and L² bounds for Bessel functions

This file collects tools for estimating integrals of Bessel functions. It writes σ(u) + conj σ(u⁻¹),
for the sum σ(u) of simple root entries, as a trace against a fixed matrix. It proves abstract `L²`
bounds for convolutions on a unimodular group, and shows that norms of Bessel functions are
invariant under the Bessel subgroup `S = New.Shape.Form.besselS`.

## Main definitions and results

* `New.Filling.besselCharMatrix`, `New.Filling.trace_besselCharMatrix_mul`: a fixed matrix C with
  tr(C u) = σ(u) + conj σ(u⁻¹) for every isometry u of the form `New.Shape.Form.splitGram`.
* `New.IsBoundedMeasurable.integral_inner_translate`: if `F * ψ = F` for an idempotent kernel `ψ`
  with `ψ 1 = d`, the inner products of the right translates of `F` are values of `ψ / d` times
  `‖F‖²`.
* `New.IsIdempotentKernel.enorm_integral_convolve_sq_le`: Schur's bound for a family of vectors of a
  Hilbert space with these inner products.
* `New.IsBoundedMeasurable.lintegral_sq_convolve_convolve_le`: the bound for `F * x` convolved once
  more with an integrable function.
* `New.IsBesselFunction.enorm_besselS_mul`: the norm of `W (s y)` equals that of `W y` for `s` in
  `S`.

Notions from other files:
* `New.convolve F x`: The function `y ↦ ∫ x a⁻¹ • F (y * a)`.
* `New.IsIdempotentKernel ψ`: `ψ` is continuous and integrable, `ψ g⁻¹ = conj (ψ g)`, `ψ 1 ≠ 0`,
  and `ψ * δ_t * ψ = (ψ t⁻¹ / ψ 1) ψ`.
* `New.orbitMeasure ρ volume`: A measure on `G` against which a left `S`-invariant function has the
  same integral as on `S \ G`.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure` and `Lib.DiscreteSeries.CuspKernel` for
sources.
-/

/-!
## The sum of the simple root entries as a trace against a fixed matrix

Let σ(u) = `New.simpleRootSum` u be the sum of the entries of u just above the diagonal on the frame
(e_0, …, e_{ϱ-1}, z) (`New.Shape.besselFrame`). Here A is a commutative star ring.
-/

namespace New.Filling

open Matrix Finset


/-- The matrix C, indexed by the Bessel index set, for which tr(C u) is the sum of the entries
u_{j,j+1} on the frame (e_0, …, e_{ϱ-1}, z) plus the entries of J u in row `besselFrame a.succ` and
column `eStar a`, for a : Fin ϱ. Here J = `New.Shape.Form.splitGram` T. -/
noncomputable def besselCharMatrix {A : Type*} {𝔰 : Shape} [CommRing A] (T : 𝔰.Form A) :
    Matrix 𝔰.BesselIndex 𝔰.BesselIndex A :=
  of fun y x ↦
    ∑ a : Fin 𝔰.ϱ,
      ((if .inl a = x then (if 𝔰.besselFrame a.succ = y then 1 else 0) else 0) +
        if eStar a = y then T.splitGram (𝔰.besselFrame a.succ) x else 0)

variable {A : Type} {𝔰 : Shape} [CommRing A] {T : 𝔰.Form A} [StarRing A]
/-- For u in `T.G`, an isometry of the form, so J u = (u⁻¹)ᴴ J for J = `New.Shape.Form.splitGram` T,
tr(Cu) = σ(u) + conj σ(u⁻¹), where C = `New.Filling.besselCharMatrix` T and σ = `New.simpleRootSum`
sums the entries u_{j,j+1} on the frame. -/
lemma trace_besselCharMatrix_mul (u : T.G) :
    (besselCharMatrix T * u.val.val).trace = simpleRootSum u + star (simpleRootSum u⁻¹) := by
  -- The first summand of `besselCharMatrix T` picks the entries of `u` that make up
  -- `simpleRootSum u`. The second picks entries of `J u`, where `J = T.splitGram`, and
  -- `J u = (u⁻¹)ᴴ J` turns them into conjugates of the entries of `u⁻¹` that make up
  -- `simpleRootSum u⁻¹`.
  have h_unitary : T.splitGram * u.val.val = u⁻¹.val.valᴴ * T.splitGram := by
    simpa using U.form_mul_inv_eq u⁻¹
  have h_trace : (besselCharMatrix T * u.val.val).trace = ∑ a : Fin 𝔰.ϱ,
      (u.val.val (.inl a) (𝔰.besselFrame a.succ) +
        (T.splitGram * u.val.val) (𝔰.besselFrame a.succ) (eStar a)) := by
    -- The instantiated `sum_comm` moves the frame index outwards; the sums stay over one type.
    simp [besselCharMatrix, trace, mul_apply, sum_mul, add_mul, sum_add_distrib,
      @sum_comm (Fin _), -Fintype.sum_sum_type]
  have h_dual (a : Fin 𝔰.ϱ) : (T.splitGram * u.val.val) (𝔰.besselFrame a.succ) (eStar a) =
      star (u⁻¹.val.val (.inl a) (𝔰.besselFrame a.succ)) := by
    rw [h_unitary]
    simp [mul_apply]
  simp [h_trace, h_dual, simpleRootSum, sum_add_distrib]

/-- On the Bessel subgroup S (`New.Shape.Form.besselS`), σ(u⁻¹) = −σ(u), where σ is the sum
`New.simpleRootSum` of the entries just above the diagonal on the frame. -/
lemma simpleRootSum_inv (u : T.G) (hu : u ∈ besselS) : simpleRootSum u⁻¹ = -simpleRootSum u := by
  -- `simpleRootSum` is additive on `besselS` and vanishes at `1 ∈ besselH`.
  rw [eq_neg_iff_add_eq_zero, ← simpleRootSum_mul (inv_mem hu) hu, inv_mul_cancel,
    simpleRootSum_eq_zero_of_mem_besselH (one_mem _)]

end New.Filling

/-!
## Schur orthogonality and L² bounds for convolutions

Let `G` be a unimodular group. Write `F * x` for `New.convolve F x`, the function
`y ↦ ∫ x a⁻¹ • F (y * a)`.
-/

section BesselSchurBound

open MeasureTheory ContinuousLinearMap InnerProductSpace ENNReal

namespace New

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasureSpace G]
  {F : G → E}
  [BorelSpace G] [(volume : Measure G).IsHaarMeasure] {x z ψ c : G → ℂ} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E] {ν : Measure G} [SFinite ν] {S : Subgroup G}
  {ρ : Measure S} [SFinite ρ] [HasCutoff ρ G] [ρ.IsInvInvariant] {d : ℝ}

/-! ### General facts on integrals and the convolution -/

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [(volume : Measure G).IsHaarMeasure] [InnerProductSpace ℂ E] [CompleteSpace E] [SFinite ν] in
/-- If `F` is integrable and essentially bounded for `ν`, the lower integral of `‖F‖ₑ ^ 2` is the
Bochner integral of `‖F‖ ^ 2`. -/
lemma lintegral_enorm_sq (hF_int : Integrable F ν) (h_top : MemLp F ∞ ν) :
    ∫⁻ y : G, ‖F y‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ y : G, ‖F y‖ ^ 2 ∂ν) := by
  have h_sq_int := hF_int.norm.mul_of_top_left h_top.norm
  simpa [sq] using (ofReal_integral_norm_eq_lintegral_enorm h_sq_int).symm

/-- Schur's orthogonality relation for an idempotent kernel `ψ`:
`∫ ψ a⁻¹ * ψ (g * (a * y)) da = ψ g / ψ 1 * ψ y`, where `ψ a⁻¹ = conj (ψ a)`. -/
theorem IsIdempotentKernel.integral_inv_mul_translate [(volume : Measure G).IsMulRightInvariant]
    [LocallyCompactSpace G] [PolishSpace G] (hψ : IsIdempotentKernel ψ) (g y : G) :
    ∫ a : G, ψ a⁻¹ * ψ (g * (a * y)) = ψ g / ψ 1 * ψ y := by
  -- The convolution identity of the kernel, after the substitution `a ↦ a⁻¹`.
  rw [← integral_inv_eq_self]
  simpa [mul_assoc] using hψ.convolution_eq g⁻¹ y

/-- For an idempotent kernel `ψ` and a function `x` with `ψ * x = x`, the function
`x⋆ y = conj (x y⁻¹)`, written `⟪x y⁻¹, 1⟫` here, satisfies `x⋆ * ψ = x⋆`. -/
theorem convolve_star (hψ : IsIdempotentKernel ψ) (hx_conv : convolve ψ x = x) :
    convolve (fun y : G ↦ ⟪x y⁻¹, 1⟫_ℂ) ψ = fun y : G ↦ ⟪x y⁻¹, 1⟫_ℂ := by
  -- Conjugate `ψ * x = x` at `y⁻¹`, substitute `a ↦ y⁻¹ * a` and use that `ψ a⁻¹ = conj (ψ a)`.
  funext y
  rw [convolve, ← integral_mul_left_eq_self _ y⁻¹]
  have h_conj : starRingEnd ℂ (x y⁻¹) =
      ∫ a : G, starRingEnd ℂ (x a⁻¹) * starRingEnd ℂ (ψ (y⁻¹ * a)) := by
    simp [← congrFun hx_conv y⁻¹, convolve, ← integral_conj]
  simp [h_conj, ← hψ.apply_inv, mul_comm]

variable [(volume : Measure G).IsMulRightInvariant] [LocallyCompactSpace G] [PolishSpace G]

/-- The convolution of two integrable functions is integrable. -/
theorem integrable_convolve (hx : Integrable x) (hz : Integrable z) :
    Integrable (convolve x z) :=
  (integral_skew_product (map_mul_right_eq_self _) (hz.comp_inv.mul_prod hx)).1

/-- On a second countable locally compact group G with two-sided Haar measure, for F : G → E
bounded and strongly measurable, E a Hilbert space, and x integrable, y ↦ ∫ x(a⁻¹) F(ya) da
is continuous. -/
theorem IsBoundedMeasurable.continuous_convolve (hF : IsBoundedMeasurable F)
    (hx : Integrable x) : Continuous (convolve F x) := by
  -- `convolve F x y` pairs the translate by `y` of `a ↦ x a⁻¹` in `L¹` with `F` in `L^∞`, and
  -- translation is continuous in `L¹`.
  have h_pairing : Continuous fun y : G ↦ (lsmul ℂ ℂ).lpPairing volume 1 ∞
      (DomMulAct.mk y⁻¹ • hx.comp_inv.toL1) hF.memLp_top.toLp := by fun_prop
  refine h_pairing.congr fun y ↦ ?_
  -- Write the pairing as an integral and substitute `a ↦ y * a`.
  have h_ae : (fun a : G ↦ (DomMulAct.mk y⁻¹ • hx.comp_inv.toL1) a • hF.memLp_top.toLp F a)
      =ᵐ[volume] fun a : G ↦ x (y⁻¹ * a)⁻¹ • F a :=
    (AEEqFun.coeFn_mk ..).smul hF.memLp_top.coeFn_toLp
  calc
    _ = ∫ a : G, x (y⁻¹ * a)⁻¹ • F a := (lpPairing_eq_integral ..).trans (integral_congr_ae h_ae)
    _ = convolve F x y := by
      rw [← integral_mul_left_eq_self _ y]
      simp [convolve]

/-- The convolution of a bounded strongly measurable function with an integrable function is
bounded and strongly measurable. -/
theorem IsBoundedMeasurable.convolve_right (hF : IsBoundedMeasurable F) (hx : Integrable x) :
    IsBoundedMeasurable (convolve F x) := by
  obtain ⟨C, hC⟩ := hF.bounded
  refine ⟨(hF.continuous_convolve hx).stronglyMeasurable, ∫ a : G, ‖x a⁻¹‖ * C, fun y ↦
    norm_integral_le_of_norm_le (hx.comp_inv.norm.mul_const C) (.of_forall fun a ↦ ?_)⟩
  grw [norm_smul, hC]

omit [(volume : Measure G).IsMulRightInvariant] [LocallyCompactSpace G] [PolishSpace G]
  [(volume : Measure G).IsHaarMeasure] [CompleteSpace E] in
/-- For bounded strongly measurable `F` and integrable `x`, the function `a ↦ x a • F (y * a)` is
integrable. -/
theorem IsBoundedMeasurable.integrable_smul (hF : IsBoundedMeasurable F) (hx : Integrable x)
    (y : G) : Integrable fun a : G ↦ x a • F (y * a) :=
  hx.smul_of_top_left (hF.comp (measurable_const_mul y)).memLp_top

/-- Convolution is associative, `(F * x) * z = F * (x * z)`, for bounded strongly measurable `F`
and integrable `x` and `z`. -/
theorem IsBoundedMeasurable.convolve_assoc (hF : IsBoundedMeasurable F) (hx : Integrable x)
    (hz : Integrable z) : convolve (convolve F x) z = convolve F (convolve x z) := by
  ext y
  -- Second part of `integral_conv`: two successive averages of the bounded function `F (y * ·)`
  -- are one average, against the convolution of the two weights.
  have h : ∫ b : G, z b⁻¹ • ∫ a : G, x a⁻¹ • F (y * (b * a)) =
      ∫ a : G, (∫ b : G, z b⁻¹ * x (b⁻¹ * a)⁻¹) • F (y * a) :=
    (integral_conv id hz.comp_inv hx.comp_inv (hF.comp (measurable_const_mul y))).2
  simpa [convolve, mul_assoc] using h

section Translates

omit [CompleteSpace E] [SFinite ν] in
/-- Let `F` be bounded and strongly measurable, with `F (s * y) = c s • F y` for `s` in the subgroup
`S`, where `|c g| = 1` for all `g : G`. Then a right translation does not change the distribution
of `‖F‖` for the measure `ν` on `G` that integrates over `S \ G` (`New.orbitMeasure`). -/
theorem IsBoundedMeasurable.identDistrib_norm_translate (hν : orbitMeasure ρ volume = ν)
    (hc : ∀ s : G, ‖c s‖ = 1) (hF : IsBoundedMeasurable F)
    (hF_left : ∀ s ∈ S, ∀ y : G, F (s * y) = c s • F y) (g : G) :
    ProbabilityTheory.IdentDistrib (fun y : G ↦ ‖F (y * g)‖) (fun y : G ↦ ‖F y‖) ν ν := by
  rw [← hν]
  refine identDistrib_orbitMeasure_mul_right g (fun (s : S) y ↦ ?_)
    hF.stronglyMeasurable.norm.measurable
  rw [Subgroup.smul_def, smul_eq_mul, hF_left _ s.2, norm_smul, hc, one_mul]

omit [CompleteSpace E] in
/-- If `x` is integrable and `F` is bounded, transforms under `S` by factors `c s` of modulus one
and is integrable for the measure `ν` of `S \ G`, then `(a, y) ↦ x a⁻¹ • F (y * a)` is integrable
for `volume.prod ν`. -/
theorem IsBoundedMeasurable.integrable_prod_translate (hν : orbitMeasure ρ volume = ν)
    (hc : ∀ s : G, ‖c s‖ = 1) (hF : IsBoundedMeasurable F)
    (hF_left : ∀ s ∈ S, ∀ y : G, F (s * y) = c s • F y) (hF_int : Integrable F ν)
    (hx : Integrable x) :
    Integrable (fun p : G × G ↦ x p.1⁻¹ • F (p.2 * p.1)) (volume.prod ν) := by
  have hF_meas : StronglyMeasurable F := hF.stronglyMeasurable
  have shift (a : G) : ProbabilityTheory.IdentDistrib (fun y : G ↦ ‖F (y * a)‖)
      (fun y : G ↦ ‖F y‖) ν ν :=
    hF.identDistrib_norm_translate hν hc hF_left a
  have h_meas : AEStronglyMeasurable (fun p : G × G ↦ x p.1⁻¹ • F (p.2 * p.1)) (volume.prod ν) :=
    hx.comp_inv.1.comp_fst.smul (StronglyMeasurable.aestronglyMeasurable (by fun_prop))
  refine (integrable_prod_iff h_meas).2 ⟨.of_forall fun a ↦ Integrable.smul (x a⁻¹) ?_, ?_⟩
  · exact (integrable_norm_iff (StronglyMeasurable.aestronglyMeasurable (by fun_prop))).1
      ((shift a).integrable_iff.2 hF_int.norm)
  · simp only [norm_smul, integral_const_mul, (shift _).integral_eq]
    exact hx.comp_inv.norm.mul_const _

/-- Let `F` be bounded, integrable for the measure `ν` of `S \ G` and transform under `S` by
factors `c s` of modulus one, and let `x` be integrable. Then the `ν`-pairing with a bounded
strongly measurable function `h` commutes with the convolution `F * x` (`New.convolve`):
`∫ ⟪h y, (F * x) y⟫ ∂ν = ∫ x a⁻¹ * (∫ ⟪h y, F (y * a)⟫ ∂ν) da`. -/
theorem IsBoundedMeasurable.integral_inner_convolve (hν : orbitMeasure ρ volume = ν)
    (hc : ∀ s : G, ‖c s‖ = 1) (hF : IsBoundedMeasurable F)
    (hF_left : ∀ s ∈ S, ∀ y : G, F (s * y) = c s • F y) (hF_int : Integrable F ν)
    (hx : Integrable x) {h : G → E} (hh : IsBoundedMeasurable h) :
    ∫ y : G, ⟪h y, convolve F x y⟫_ℂ ∂ν =
      ∫ a : G, x a⁻¹ * ∫ y : G, ⟪h y, F (y * a)⟫_ℂ ∂ν := by
  obtain ⟨h_meas, C, hC⟩ := hh
  have h_prod := hF.integrable_prod_translate hν hc hF_left hF_int hx
  have h_int : Integrable (fun p : G × G ↦ ⟪h p.2, x p.1⁻¹ • F (p.2 * p.1)⟫_ℂ) (volume.prod ν) :=
    (h_prod.norm.const_mul C).mono'
      ((StronglyMeasurable.aestronglyMeasurable (by fun_prop)).inner h_prod.1)
      (.of_forall fun p ↦ (norm_inner_le_norm ..).trans (by grw [hC]))
  calc
    _ = ∫ y, (∫ a, ⟪h y, x a⁻¹ • F (y * a)⟫_ℂ) ∂ν := integral_congr_ae (.of_forall fun y ↦
      (integral_inner (hF.integrable_smul hx.comp_inv y) (h y)).symm)
    _ = ∫ a, ∫ y, ⟪h y, x a⁻¹ • F (y * a)⟫_ℂ ∂ν := (integral_integral_swap h_int).symm
    _ = _ := by simp only [inner_smul_right, integral_const_mul]

/-- Let `F * ψ = F` for an idempotent kernel `ψ` with `ψ 1 = d`, where `F` is bounded, transforms
under `S` by factors `c s` of modulus one and is integrable for the measure `ν` of `S \ G`. Then
the inner product in `L²(ν)` of the right translates of `F` by `a` and `b` is `ψ (a⁻¹ b) / d`
times the squared norm of `F`. -/
theorem IsBoundedMeasurable.integral_inner_translate (hν : orbitMeasure ρ volume = ν)
    (hc : ∀ s : G, ‖c s‖ = 1) (hF : IsBoundedMeasurable F) {d : ℝ}
    (hF_left : ∀ s ∈ S, ∀ y : G, F (s * y) = c s • F y) (hF_int : Integrable F ν)
    (hψ : IsIdempotentKernel ψ) (hψ_one : ψ 1 = d) (hF_conv : convolve F ψ = F) (a b : G) :
    ∫ y : G, ⟪F (y * a), F (y * b)⟫_ℂ ∂ν = ψ (a⁻¹ * b) / d * (∫ y : G, ‖F y‖ ^ 2 ∂ν : ℝ) := by
  -- The coefficient `k` is reproduced by `ψ` on both sides, and `ψ * δ_t * ψ = (ψ t⁻¹ / d) ψ`;
  -- so `k = (ψ / d) * k 1`.
  have hF_meas : StronglyMeasurable F := hF.stronglyMeasurable
  obtain ⟨C, hC⟩ := hF.bounded
  let k (g : G) : ℂ := ∫ y : G, ⟪F y, F (y * g)⟫_ℂ ∂ν
  have shift (s t : G) : ∫ y : G, ⟪F (y * s), F (y * t)⟫_ℂ ∂ν = k (s⁻¹ * t) := by
    have h_inv (u : S) (y : G) :
        ⟪F (u • y), F (u • y * (s⁻¹ * t))⟫_ℂ = ⟪F y, F (y * (s⁻¹ * t))⟫_ℂ := by
      simp [Subgroup.smul_def, mul_assoc, hF_left _ u.2,
        mul_left_comm (c (u : G)), Complex.mul_conj', hc]
    have h_meas : StronglyMeasurable fun y : G ↦ ⟪F y, F (y * (s⁻¹ * t))⟫_ℂ := by fun_prop
    simpa [k, hν, mul_assoc] using (identDistrib_orbitMeasure_mul_right (ν := ρ) (μ := volume)
      s h_inv h_meas.measurable).integral_eq
  have k_inv (g : G) : k g⁻¹ = starRingEnd ℂ (k g) := by
    rw [← mul_one g⁻¹, ← shift, ← integral_conj]
    simp only [mul_one, inner_conj_symm]
  have k_bdd : IsBoundedMeasurable k := by
    refine ⟨StronglyMeasurable.integral_prod_right (f := fun g y ↦ ⟪F y, F (y * g)⟫_ℂ)
      (by fun_prop), ∫ y, ‖F y‖ * C ∂ν, fun g ↦ norm_integral_le_of_norm_le
        (hF_int.norm.mul_const C) (.of_forall fun y ↦ ?_)⟩
    exact (norm_inner_le_norm ..).trans (by grw [hC (y * g)])
  have right (g : G) : k g = ∫ t : G, ψ t⁻¹ * k (g * t) := calc
    k g = ∫ y : G, ⟪F (y * g⁻¹), convolve F ψ y⟫_ℂ ∂ν := by
      simpa only [hF_conv, inv_inv, mul_one] using (shift g⁻¹ 1).symm
    _ = ∫ t : G, ψ t⁻¹ * k (g * t) := by
      simp only [hF.integral_inner_convolve hν hc hF_left hF_int hψ.integrable
        (hF.comp (measurable_mul_const g⁻¹)), shift, inv_inv]
  have left (g : G) : k g = ∫ t : G, ψ t * k (t⁻¹ * g) := by
    rw [← inv_inv g, k_inv, right]
    simp [← integral_conj, ← k_inv, ← hψ.apply_inv]
  have key (g : G) : k g = ψ g / d * k 1 := calc
    k g = ∫ s : G, ψ s * ∫ t : G, ψ t⁻¹ * k (s⁻¹ * g * t) := by simp only [left g, ← right]
    _ = ∫ t : G, (∫ s : G, ψ s * ψ ((s * t)⁻¹ * g)) * k t := by
      simpa only [smul_eq_mul, mul_inv_rev, inv_inv, mul_assoc] using
        (integral_conv (fun s ↦ s⁻¹ * g) hψ.integrable hψ.integrable.comp_inv k_bdd).2
    _ = ψ g / d * ∫ t : G, ψ t⁻¹ * k t := by
      simp only [hψ.convolution_eq, hψ_one, ← integral_const_mul]
      congr with t
      ring
    _ = ψ g / d * k 1 := by simp only [right 1, one_mul]
  rw [shift, key]
  simp [k, ← integral_complex_ofReal, inner_self_eq_norm_sq_to_K]

end Translates

/-- The average of the values of `F * x` against an integrable function `z` is the value at `1` of
the convolution of `F` with `x * (a ↦ z a⁻¹)`. -/
theorem IsBoundedMeasurable.integral_smul_convolve (hF : IsBoundedMeasurable F)
    (hx : Integrable x) (hz : Integrable z) :
    ∫ g : G, z g • convolve F x g = convolve F (convolve x fun a : G ↦ z a⁻¹) 1 := by
  rw [← hF.convolve_assoc hx hz.comp_inv]
  simp [convolve]

/-- For bounded strongly measurable `F` and integrable `x`, the inner product with a fixed vector
commutes with the integral `convolve F x g = ∫ x a⁻¹ • F (g * a)`. -/
theorem IsBoundedMeasurable.inner_convolve (hF : IsBoundedMeasurable F) (hx : Integrable x)
    (u : E) (g : G) : ⟪u, convolve F x g⟫_ℂ = ∫ a : G, x a⁻¹ * ⟪u, F (g * a)⟫_ℂ := by
  simp [convolve, ← integral_inner (hF.integrable_smul hx.comp_inv g), inner_smul_right]

omit [MeasureSpace G] [(volume : Measure G).IsMulRightInvariant] [LocallyCompactSpace G]
  [PolishSpace G] [BorelSpace G] [(volume : Measure G).IsHaarMeasure] [CompleteSpace E] in
/-- A map `w` of the group `G` into an inner product space with `⟪w a, w b⟫ = k (a⁻¹ * b)` for a
continuous function `k` is continuous. -/
theorem continuous_of_inner_eq {w : G → E} {k : G → ℂ} (hk : Continuous k)
    (hw : ∀ a b : G, ⟪w a, w b⟫_ℂ = k (a⁻¹ * b)) : Continuous w := by
  refine continuous_iff_continuousAt.2 fun a ↦ tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have h_norm (b : G) : ‖w b - w a‖ = √(2 * (k 1).re - 2 * (k (b⁻¹ * a)).re) := by
    rw [← Real.sqrt_sq (norm_nonneg (w b - w a)), norm_sub_sq (𝕜 := ℂ)]
    simp only [← inner_self_eq_norm_sq (𝕜 := ℂ), hw, inv_mul_cancel, RCLike.re_to_complex]
    ring_nf
  have h_cont : Continuous fun b : G ↦ √(2 * (k 1).re - 2 * (k (b⁻¹ * a)).re) := by fun_prop
  simpa [h_norm] using h_cont.tendsto a

/-- Schur's orthogonality relation on `G`: if `ψ` is a bounded idempotent kernel with `ψ 1 = d` and
`x` is integrable with `ψ * x = x`, then `∫ x (a⁻¹ g) * conj (x (b⁻¹ g)) dg` is
`ψ (a⁻¹ * b) / d` times the squared `L²` norm of `x`. -/
theorem IsIdempotentKernel.integral_mul_conj_translate (hx : Integrable x)
    (hψ : IsIdempotentKernel ψ) (hψ_one : ψ 1 = d) (hψ_bdd : IsBoundedMeasurable ψ)
    (hx_conv : convolve ψ x = x) (a b : G) :
    ∫ g : G, x (a⁻¹ * g) * starRingEnd ℂ (x (b⁻¹ * g)) =
      ψ (a⁻¹ * b) / d * (∫ g : G, ‖x g‖ ^ 2 : ℝ) := by
  -- This is `integral_inner_translate` on `G` itself, for `y ↦ conj (x y⁻¹)`.
  obtain ⟨x_meas, C, hC⟩ : IsBoundedMeasurable x := by
    simpa only [hx_conv] using hψ_bdd.convolve_right hx
  have h_bdd : IsBoundedMeasurable fun y : G ↦ ⟪x y⁻¹, 1⟫_ℂ := ⟨by fun_prop, C, by simp [hC]⟩
  -- Take the trivial subgroup and the character `1`; the quotient measure is then `volume`.
  have h : ∫ y : G, ⟪⟪x (y * a)⁻¹, 1⟫_ℂ, ⟪x (y * b)⁻¹, 1⟫_ℂ⟫_ℂ =
      ψ (a⁻¹ * b) / d * (∫ y : G, ‖⟪x y⁻¹, 1⟫_ℂ‖ ^ 2 : ℝ) :=
    h_bdd.integral_inner_translate quotMeasure_bot (c := 1) (by simp) (by simp)
      (hx.comp_inv.inner_const (𝕜 := ℂ) 1) hψ hψ_one (convolve_star hψ hx_conv) a b
  rw [← integral_inv_eq_self]
  simpa [integral_inv_eq_self fun y ↦ ‖x y‖ ^ 2, mul_comm] using h

section Orbit

/-! The vectors `w a` below stand for the translates `π(a) v₀` of a vector `v₀` of a unitary
representation with `∫ ψ a⁻¹ • π(a) v₀ = v₀` and `‖v₀‖ ^ 2 = q`; only their inner products are
used. The vectors `convolve w x g = ∫ x a⁻¹ • w (g * a)` are the translates of one vector in the
closed span of the `w a`. -/
omit [(volume : Measure G).IsMulRightInvariant] [LocallyCompactSpace G]
  [(volume : Measure G).IsHaarMeasure] [CompleteSpace E] in
/-- If `⟪w a, w b⟫ = ψ (a⁻¹ * b) / d * q` for an idempotent kernel `ψ` with `ψ 1 = d`, then `w` is
strongly measurable and bounded: it is continuous and `‖w a‖ ^ 2 = q`. -/
theorem IsIdempotentKernel.isBoundedMeasurable_of_inner_eq (hψ : IsIdempotentKernel ψ)
    (hψ_one : ψ 1 = d) {w : G → E} {q : ℝ}
    (hw : ∀ a b : G, ⟪w a, w b⟫_ℂ = ψ (a⁻¹ * b) / d * q) : IsBoundedMeasurable w := by
  have w_cont : Continuous w :=
    continuous_of_inner_eq ((hψ.continuous.div_const _).mul_const _) hw
  have h_norm (a : G) : ‖w a‖ ^ 2 = q := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hw]
    simp [← hψ_one, hψ.apply_one_ne_zero]
  exact ⟨w_cont.stronglyMeasurable, √q, fun a ↦ Real.le_sqrt_of_sq_le (h_norm a).le⟩

/-- Let `ψ` be an idempotent kernel with `ψ 1 = d`, `x` integrable with `ψ * x = x`, and
`⟪w a, w b⟫ = ψ (a⁻¹ * b) / d * q`. Then the coefficient of `convolve w x g` with `w a` is
`q / d * x (a⁻¹ * g)`. -/
theorem IsIdempotentKernel.inner_convolve_eq (hx : Integrable x) (hψ : IsIdempotentKernel ψ)
    (hψ_one : ψ 1 = d) (hx_conv : convolve ψ x = x) {w : G → E} {q : ℝ}
    (hw : ∀ a b : G, ⟪w a, w b⟫_ℂ = ψ (a⁻¹ * b) / d * q) (a g : G) :
    ⟪w a, convolve w x g⟫_ℂ = q / d * x (a⁻¹ * g) := by
  calc ⟪w a, convolve w x g⟫_ℂ
    _ = ∫ t : G, x t⁻¹ * ⟪w a, w (g * t)⟫_ℂ :=
      (hψ.isBoundedMeasurable_of_inner_eq hψ_one hw).inner_convolve hx _ g
    _ = q / d * convolve ψ x (a⁻¹ * g) := by
      simp [hw, convolve, ← integral_const_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = q / d * x (a⁻¹ * g) := by rw [hx_conv]

/-- For an idempotent kernel `ψ` with `ψ 1 = d`, an integrable `x` with `ψ * x = x` and vectors
with `⟪w a, w b⟫ = ψ (a⁻¹ * b) / d * q`, the squared norm of `convolve w x 1` is
`‖x‖₂ ^ 2 * q / d`. -/
theorem IsIdempotentKernel.norm_convolve_sq (hx : Integrable x) (hψ : IsIdempotentKernel ψ)
    (hψ_one : ψ 1 = d) (hx_conv : convolve ψ x = x) {w : G → E} {q : ℝ}
    (hw : ∀ a b : G, ⟪w a, w b⟫_ℂ = ψ (a⁻¹ * b) / d * q) :
    ‖convolve w x 1‖ ^ 2 = (∫ y : G, ‖x y‖ ^ 2) / d * q := by
  have h_point (a : G) : x a⁻¹ * ⟪convolve w x 1, w a⟫_ℂ = (‖x a⁻¹‖ ^ 2 / d * q : ℝ) := by
    rw [← inner_conj_symm, hψ.inner_convolve_eq hx hψ_one hx_conv hw, mul_one]
    simp only [map_mul, map_div₀, Complex.conj_ofReal, mul_left_comm _ (_ / _ : ℂ),
      Complex.mul_conj']
    push_cast
    ring
  refine Complex.ofReal_injective ?_
  calc ((‖convolve w x 1‖ ^ 2 : ℝ) : ℂ)
    _ = ⟪convolve w x 1, convolve w x 1⟫_ℂ := by simp [inner_self_eq_norm_sq_to_K]
    _ = ∫ a : G, x a⁻¹ * ⟪convolve w x 1, w a⟫_ℂ := by
      simpa only [one_mul] using
        (hψ.isBoundedMeasurable_of_inner_eq hψ_one hw).inner_convolve hx (convolve w x 1) 1
    _ = _ := by
      simp only [h_point, integral_complex_ofReal, integral_mul_const, integral_div,
        integral_inv_eq_self fun y : G ↦ ‖x y‖ ^ 2]

/-- Let `ψ` be an idempotent kernel with `ψ 1 = d`, `x` integrable with `ψ * x = x`, and
`⟪w a, w b⟫ = ψ (a⁻¹ * b) / d * q`. For `u` in the span of the `w a`, the coefficient
`g ↦ ⟪u, convolve w x g⟫` is integrable. -/
theorem IsIdempotentKernel.integrable_inner_convolve (hx : Integrable x)
    (hψ : IsIdempotentKernel ψ) (hψ_one : ψ 1 = d) (hx_conv : convolve ψ x = x) {w : G → E} {q : ℝ}
    (hw : ∀ a b : G, ⟪w a, w b⟫_ℂ = ψ (a⁻¹ * b) / d * q) {u : E}
    (hu : u ∈ Submodule.span ℂ (Set.range w)) :
    Integrable fun g : G ↦ ⟪u, convolve w x g⟫_ℂ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    simpa only [hψ.inner_convolve_eq hx hψ_one hx_conv hw] using (hx.comp_mul_left a⁻¹).const_mul _
  | zero => simp
  | add u u' _ _ h h' => simpa only [inner_add_left] using h.fun_add h'
  | smul t u _ h => simpa only [inner_smul_left] using h.const_mul _

/-- Schur's orthogonality relation for the translates of `v = convolve w x 1` and finite
combinations `u`, `u'` of the vectors `w a`: `∫ ⟪u, convolve w x g⟫ * ⟪convolve w x g, u'⟫ dg` is
`‖v‖ ^ 2 / d * ⟪u, u'⟫`. Here `ψ` is a bounded idempotent kernel with `ψ 1 = d`, `x` is integrable
with `ψ * x = x`, and `⟪w a, w b⟫ = ψ (a⁻¹ * b) / d * q`. -/
theorem IsIdempotentKernel.integral_inner_convolve_mul (hx : Integrable x)
    (hψ : IsIdempotentKernel ψ) (hψ_one : ψ 1 = d) (hψ_bdd : IsBoundedMeasurable ψ)
    (hx_conv : convolve ψ x = x) {w : G → E} {q : ℝ}
    (hw : ∀ a b : G, ⟪w a, w b⟫_ℂ = ψ (a⁻¹ * b) / d * q) {u u' : E}
    (hu : u ∈ Submodule.span ℂ (Set.range w)) (hu' : u' ∈ Submodule.span ℂ (Set.range w)) :
    ∫ g : G, ⟪u, convolve w x g⟫_ℂ * ⟪convolve w x g, u'⟫_ℂ =
      (‖convolve w x 1‖ ^ 2 / d : ℝ) * ⟪u, u'⟫_ℂ := by
  obtain ⟨v_meas, C, hC⟩ := (hψ.isBoundedMeasurable_of_inner_eq hψ_one hw).convolve_right hx
  have prod_int {u : E} (hu : u ∈ Submodule.span ℂ (Set.range w)) (u' : E) :
      Integrable fun g ↦ ⟪u, convolve w x g⟫_ℂ * ⟪convolve w x g, u'⟫_ℂ :=
    (hψ.integrable_inner_convolve hx hψ_one hx_conv hw hu).mul_bdd (c := C * ‖u'‖)
      (StronglyMeasurable.aestronglyMeasurable (by fun_prop))
      (.of_forall fun g ↦ (norm_inner_le_norm ..).trans (by grw [hC]))
  -- Both sides are sesquilinear in `u`, `u'`.
  induction hu, hu' using Submodule.span_induction₂ with
  | mem_mem u u' hu hu' =>
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hu'
    have h_point (g : G) : ⟪w a, convolve w x g⟫_ℂ * ⟪convolve w x g, w b⟫_ℂ =
        (q / d) ^ 2 * (x (a⁻¹ * g) * starRingEnd ℂ (x (b⁻¹ * g))) := by
      simp [← inner_conj_symm _ (w b), hψ.inner_convolve_eq hx hψ_one hx_conv hw]
      ring
    simp [h_point, integral_const_mul, hψ.integral_mul_conj_translate hx hψ_one hψ_bdd hx_conv, hw,
      hψ.norm_convolve_sq hx hψ_one hx_conv hw]
    ring
  | zero_left | zero_right => simp
  | add_left u₁ u₂ u' h₁ h₂ _ ih₁ ih₂ =>
    simp only [inner_add_left, add_mul, mul_add, integral_add (prod_int h₁ _) (prod_int h₂ _),
      ih₁, ih₂]
  | add_right u u₁ u₂ h _ _ ih₁ ih₂ =>
    simp only [inner_add_right, mul_add, integral_add (prod_int h _) (prod_int h _), ih₁, ih₂]
  | smul_left t u u' _ _ ih =>
    simp only [inner_smul_left, mul_assoc, integral_const_mul, ih]
    ring
  | smul_right t u u' _ _ ih =>
    simp only [inner_smul_right, mul_left_comm _ t, integral_const_mul, ih]

omit [CompleteSpace E] in
/-- If a vector `V` of an inner product space lies in the closure of a subspace `H` and
`‖⟪u, V⟫‖ ^ 2 ≤ B * ‖u‖ ^ 2` for every `u` in `H`, then `‖V‖ ^ 2 ≤ B`. -/
theorem enorm_sq_le_of_forall_mem_inner_sq_le {H : Submodule ℂ E} {V : E} {B : ℝ≥0∞}
    (hV : V ∈ closure (H : Set E)) (h_le : ∀ u ∈ H, ‖⟪u, V⟫_ℂ‖ₑ ^ 2 ≤ B * ‖u‖ₑ ^ 2) :
    ‖V‖ₑ ^ 2 ≤ B := by
  obtain h_top | h_fin := eq_or_ne B ∞
  · simp [h_top]
  have h_self : ‖⟪V, V⟫_ℂ‖ₑ ^ 2 ≤ B * ‖V‖ₑ ^ 2 := closure_minimal h_le
    (isClosed_le (by fun_prop) ((ENNReal.continuous_const_mul h_fin).comp (by fun_prop))) hV
  have h_enorm : ‖⟪V, V⟫_ℂ‖ₑ = ‖V‖ₑ ^ 2 := by simp [inner_self_eq_norm_sq_to_K, ← ofReal_norm]
  rw [h_enorm, sq (‖V‖ₑ ^ 2)] at h_self
  -- Cancel the finite factor `‖V‖ ^ 2` if it is not zero.
  obtain h_zero | h_ne := eq_or_ne (‖V‖ₑ ^ 2) 0
  · simp [h_zero]
  exact (ENNReal.mul_le_mul_iff_left h_ne (by simp)).1 h_self

/-- **Schur's bound.** Let `ψ` be a bounded idempotent kernel with `ψ 1 = d`, `x` integrable with
`ψ * x = x`, and `⟪w a, w b⟫ = ψ (a⁻¹ * b) / d * q`. The average of the translates of
`v = convolve w x 1` against an integrable function `z` has squared norm at most
`‖v‖ ^ 2 ‖z‖₂ ^ 2 / d`. -/
theorem IsIdempotentKernel.enorm_integral_convolve_sq_le (hx : Integrable x)
    (hψ : IsIdempotentKernel ψ) (hψ_one : ψ 1 = d) (hψ_bdd : IsBoundedMeasurable ψ)
    (hx_conv : convolve ψ x = x) {w : G → E} {q : ℝ}
    (hw : ∀ a b : G, ⟪w a, w b⟫_ℂ = ψ (a⁻¹ * b) / d * q) (hz : Integrable z) :
    ‖∫ g : G, z g • convolve w x g‖ₑ ^ 2 ≤
      ENNReal.ofReal (‖convolve w x 1‖ ^ 2 / d) * ∫⁻ y : G, ‖z y‖ₑ ^ 2 := by
  -- Let `V` be the average. Orthogonality and the Cauchy–Schwarz inequality bound `⟪u, V⟫` for `u`
  -- in the span `H` of the `w a`. The bound passes to the closure of `H`, which contains `V`.
  have w_bdd : IsBoundedMeasurable w := hψ.isBoundedMeasurable_of_inner_eq hψ_one hw
  have v_bdd : IsBoundedMeasurable (convolve w x) := w_bdd.convolve_right hx
  set V : E := ∫ g : G, z g • convolve w x g
  set B : ℝ≥0∞ := .ofReal (‖convolve w x 1‖ ^ 2 / d) * ∫⁻ y : G, ‖z y‖ₑ ^ 2 with hB
  let H : Submodule ℂ E := Submodule.span ℂ (Set.range w)
  have inner_V (u : E) : ⟪u, V⟫_ℂ = ∫ g : G, z g * ⟪u, convolve w x g⟫_ℂ := by
    simpa [inner_smul_right] using (integral_inner (𝕜 := ℂ) (v_bdd.integrable_smul hz 1) u).symm
  have bound (u : E) (hu : u ∈ H) : ‖⟪u, V⟫_ℂ‖ₑ ^ 2 ≤ B * ‖u‖ₑ ^ 2 := by
    have coef_int := hψ.integrable_inner_convolve hx hψ_one hx_conv hw hu
    have coef_bdd : IsBoundedMeasurable fun g ↦ ⟪u, convolve w x g⟫_ℂ := by
      obtain ⟨v_meas, C, hC⟩ := v_bdd
      exact ⟨by fun_prop, ‖u‖ * C, fun g : G ↦ (norm_inner_le_norm ..).trans (by grw [hC g])⟩
    have orth : ∫ g, ‖⟪u, convolve w x g⟫_ℂ‖ ^ 2 = ‖convolve w x 1‖ ^ 2 / d * ‖u‖ ^ 2 := by
      have h_point (v : E) : ⟪u, v⟫_ℂ * ⟪v, u⟫_ℂ = ‖⟪u, v⟫_ℂ‖ ^ 2 := by
        rw [← inner_conj_symm v u, Complex.mul_conj']
      apply Complex.ofReal_injective
      simpa [h_point, inner_self_eq_norm_sq_to_K, ← integral_complex_ofReal] using
        hψ.integral_inner_convolve_mul hx hψ_one hψ_bdd hx_conv hw hu hu
    calc
      _ ≤ (∫⁻ g, ‖z g * ⟪u, convolve w x g⟫_ℂ‖ₑ) ^ 2 := by
        grw [inner_V, enorm_integral_le_lintegral_enorm]
      _ ≤ (∫⁻ g, ‖z g‖ₑ ^ 2) * ∫⁻ g, ‖⟪u, convolve w x g⟫_ℂ‖ₑ ^ 2 :=
        sq_lintegral_le (hz.1.enorm.pow_const 2) (coef_int.1.enorm.pow_const 2) (by simp [mul_pow])
      _ = B * ‖u‖ₑ ^ 2 := by
        rw [lintegral_enorm_sq coef_int coef_bdd.memLp_top, orth, ofReal_mul' (by positivity),
          ofReal_pow (norm_nonneg u), ofReal_norm, hB]
        ring
  have V_mem : V ∈ closure (H : Set E) := by
    rw [← Submodule.topologicalClosure_coe, ← Submodule.orthogonal_orthogonal_eq_closure]
    intro u hu
    simp [inner_V, w_bdd.inner_convolve hx, Submodule.inner_left_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self _)) hu]
  exact enorm_sq_le_of_forall_mem_inner_sq_le V_mem bound

end Orbit

/-! ### Schur's bound in `L²(S ∖ G)` -/

omit [SFinite ν] [CompleteSpace E] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [(volume : Measure G).IsMulRightInvariant] [LocallyCompactSpace G] [PolishSpace G] [BorelSpace G]
  [(volume : Measure G).IsHaarMeasure] [InnerProductSpace ℂ E] in
/-- A bounded measurable function that is integrable for `ν` is square integrable for `ν`. -/
theorem IsBoundedMeasurable.memLp_two {f : G → E} (hf : IsBoundedMeasurable f)
    (h_int : Integrable f ν) : MemLp f 2 ν :=
  (memLp_two_iff_integrable_sq_norm h_int.1).2
    ((h_int.norm.mul_of_top_left hf.memLp_top.norm).congr (.of_forall fun _ ↦ (sq _).symm))

omit [IsTopologicalGroup G] [(volume : Measure G).IsMulRightInvariant] [LocallyCompactSpace G]
  [PolishSpace G] [BorelSpace G] [(volume : Measure G).IsHaarMeasure] in
/-- The value at `1` of an idempotent kernel, if real, is nonnegative: it is the integral of the
squared absolute value of the kernel. -/
theorem IsIdempotentKernel.apply_one_nonneg (hψ : IsIdempotentKernel ψ) (hψ_one : ψ 1 = d) :
    0 ≤ d := by
  have h : (d : ℂ) = (∫ g : G, ‖ψ g‖ ^ 2 : ℝ) := by
    simpa [hψ_one, hψ.apply_inv, Complex.mul_conj', ← integral_complex_ofReal] using
      (hψ.convolution_self 1).symm
  rw [Complex.ofReal_injective h]
  positivity

/-- Schur's bound in `L²(S ∖ G)`, for the vector `F * x` in the closed span of the right translates
of `F`, where `G` is a locally compact Polish group with Haar measure `volume`. Here
`ν = orbitMeasure ρ volume` is a measure on `G` that integrates over `S ∖ G`, for an s-finite,
inversion-invariant measure `ρ` on the subgroup `S` admitting a cutoff. The bounded measurable `F`
is integrable for `ν` and transforms under `S` by factors `c s` of modulus one; `ψ` is a bounded
idempotent kernel with `ψ 1 = d` and `F * ψ = F`; the integrable `x` has `ψ * x = x`; and `z` is any
integrable function on `G`. The squared `ν`-norm of `(F * x) * (a ↦ z a⁻¹)` is then at most
`‖x‖₂ ^ 2 ‖F‖₂ ^ 2 ‖z‖₂ ^ 2 / d ^ 2`. -/
theorem IsBoundedMeasurable.lintegral_sq_convolve_convolve_le
    (hν : orbitMeasure ρ volume = ν) (hc : ∀ s : G, ‖c s‖ = 1) (hF : IsBoundedMeasurable F)
    {d : ℝ} (hF_left : ∀ s ∈ S, ∀ y : G, F (s * y) = c s • F y) (hF_int : Integrable F ν)
    (hx : Integrable x) (hψ : IsIdempotentKernel ψ) (hψ_one : ψ 1 = d) (hF_conv : convolve F ψ = F)
    (hψ_bdd : IsBoundedMeasurable ψ) (hx_conv : convolve ψ x = x) (hz : Integrable z) :
    ∫⁻ y : G, ‖convolve (convolve F x) (fun a : G ↦ z a⁻¹) y‖ₑ ^ 2 ∂ν ≤
      ENNReal.ofReal ((∫ y : G, ‖x y‖ ^ 2) / d) *
        (ENNReal.ofReal d⁻¹ * ∫⁻ y : G, ‖F y‖ₑ ^ 2 ∂ν) * ∫⁻ y : G, ‖z y‖ₑ ^ 2 := by
  -- Let `w a` be the translates of `F` in `L²(ν)` and `Z = x * (a ↦ z a⁻¹)`. Schur's bound holds
  -- for the vector `convolve w Z 1 = ∫ Z a⁻¹ • w a`. The function `Φ = F * Z` on the left has
  -- `⟪Φ, Φ⟫ = ⟪Φ, convolve w Z 1⟫` by Fubini's theorem, so `‖Φ‖ ≤ ‖convolve w Z 1‖`.
  have translate_memLp (a : G) : MemLp (fun y : G ↦ F (y * a)) 2 ν :=
    have h_bdd : IsBoundedMeasurable fun y : G ↦ F (y * a) := hF.comp (measurable_mul_const a)
    h_bdd.memLp_two ((integrable_norm_iff h_bdd.stronglyMeasurable.aestronglyMeasurable).1
      ((hF.identDistrib_norm_translate hν hc hF_left a).integrable_iff.2 hF_int.norm))
  let w (a : G) : Lp E 2 ν := (translate_memLp a).toLp _
  have inner_toLp {f g : G → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
      ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ y, ⟪f y, g y⟫_ℂ ∂ν :=
    integral_congr_ae (hf.coeFn_toLp.comp₂ _ hg.coeFn_toLp)
  have hw (a b : G) : ⟪w a, w b⟫_ℂ = ψ (a⁻¹ * b) / d * (∫ y : G, ‖F y‖ ^ 2 ∂ν : ℝ) :=
    (inner_toLp ..).trans (hF.integral_inner_translate hν hc hF_left hF_int hψ hψ_one hF_conv a b)
  have w_bdd : IsBoundedMeasurable w := hψ.isBoundedMeasurable_of_inner_eq hψ_one hw
  let Z : G → ℂ := convolve x fun a : G ↦ z a⁻¹
  have Z_int : Integrable Z := integrable_convolve hx hz.comp_inv
  have Φ_bdd : IsBoundedMeasurable (convolve F Z) := hF.convolve_right Z_int
  have Φ_int : Integrable (convolve F Z) ν :=
    (hF.integrable_prod_translate hν hc hF_left hF_int Z_int).integral_prod_right
  let Φ : Lp E 2 ν := (Φ_bdd.memLp_two Φ_int).toLp _
  have hd_nonneg : 0 ≤ d := hψ.apply_one_nonneg hψ_one
  have schur_le : ‖convolve w Z 1‖ₑ ^ 2 ≤ .ofReal ((∫ y, ‖x y‖ ^ 2) / d) *
      (.ofReal d⁻¹ * .ofReal (∫ y, ‖F y‖ ^ 2 ∂ν)) * ∫⁻ y, ‖z y‖ₑ ^ 2 := by
    have schur := hψ.enorm_integral_convolve_sq_le hx hψ_one hψ_bdd hx_conv hw hz
    rwa [w_bdd.integral_smul_convolve hx hz, hψ.norm_convolve_sq hx hψ_one hx_conv hw,
      mul_div_assoc, div_eq_inv_mul (∫ y, ‖F y‖ ^ 2 ∂ν), ofReal_mul (by positivity),
      ofReal_mul (by positivity)] at schur
  have Φ_inner : ⟪Φ, Φ⟫_ℂ = ⟪Φ, convolve w Z 1⟫_ℂ := by
    rw [inner_toLp, hF.integral_inner_convolve hν hc hF_left hF_int Z_int Φ_bdd,
      w_bdd.inner_convolve Z_int]
    simp only [Φ, w, inner_toLp, one_mul]
  have Φ_le : ‖Φ‖ ≤ ‖convolve w Z 1‖ := by
    have h : ‖Φ‖ * ‖Φ‖ ≤ ‖Φ‖ * ‖convolve w Z 1‖ := by
      grw [← inner_self_eq_norm_mul_norm (𝕜 := ℂ), Φ_inner, re_inner_le_norm]
    nlinarith [norm_nonneg Φ, norm_nonneg (convolve w Z 1)]
  have Φ_norm : ∫ y, ‖convolve F Z y‖ ^ 2 ∂ν = ‖Φ‖ ^ 2 := by
    apply Complex.ofReal_injective
    have h : ⟪Φ, Φ⟫_ℂ = ∫ y : G, ⟪convolve F Z y, convolve F Z y⟫_ℂ ∂ν := inner_toLp _ _
    simpa [inner_self_eq_norm_sq_to_K, ← integral_complex_ofReal] using h.symm
  calc
    _ = .ofReal (‖Φ‖ ^ 2) := by
      rw [hF.convolve_assoc hx hz.comp_inv, lintegral_enorm_sq Φ_int Φ_bdd.memLp_top, Φ_norm]
    _ ≤ ‖convolve w Z 1‖ₑ ^ 2 := by grw [Φ_le, ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ _ := by rwa [lintegral_enorm_sq hF_int hF.memLp_top]

end New

end BesselSchurBound

/-!
## Left invariance of norms of Bessel functions under the Bessel subgroup

A Bessel function (`New.IsBesselFunction rep W`) is a bounded strongly measurable vector-valued
function on `New.Shape.G₁` that transforms on the left by a character under the unipotent group
`New.Shape.Form.besselU` and by the unitary representation `rep` under `New.RealPlace.embedH`.
Together these generate the Bessel subgroup `S = New.Shape.Form.besselS`.
-/

namespace New.IsBesselFunction

open MeasureTheory RealPlace

variable {𝔰 : Shape} {I : Type*} [Fintype I] [DecidableEq I]
  {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* Matrix.unitaryGroup I ℂ} {W : 𝔰.G₁ → EuclideanSpace ℂ I}

/-- For `s` in the Bessel subgroup `besselS` and a Bessel function `W` (a bounded function with
values in a unitary representation that transforms under `besselS`), replacing `g` by `s * g` does
not change the norm of a weighted integral of right translates of `W`. -/
lemma enorm_integral_besselS_mul (hW : IsBesselFunction rep W) {s : 𝔰.G₁} (hs : s ∈ besselS)
    (β : 𝔰.G₁ → ℂ) (g : 𝔰.G₁) {μ : Measure 𝔰.G₁} :
    ‖∫ y : 𝔰.G₁, β y • W (s * g * y) ∂μ‖ₑ = ‖∫ y : 𝔰.G₁, β y • W (g * y) ∂μ‖ₑ := by
  -- `s = u * toBesselH 𝔰 1 h` changes `W` by a scalar of norm one and by the unitary operator
  -- `A = rep h`.
  obtain ⟨u, hu, h, rfl⟩ := exists_besselU_mul_toBesselH hs isUnit_one
  let A : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ I :=
    (Unitary.linearIsometryEquiv (DiscreteSeries.besselValueRep rep h)).toLinearIsometry
  have h_transl (y : 𝔰.G₁) :
      W (u * toBesselH 𝔰 1 h * g * y) = wave (simpleRootSum u) • A (W (g * y)) := by
    rw [mul_assoc, mul_assoc, hW.map_unipotent_mul u hu]
    -- `toBesselH 𝔰 1` is `embedH` and `A` is `rep h` by definition.
    exact congrArg _ (hW.map_unitary_mul h (g * y))
  calc ‖∫ y : 𝔰.G₁, β y • W (u * toBesselH 𝔰 1 h * g * y) ∂μ‖ₑ
    _ = ‖wave (simpleRootSum u) • ∫ y : 𝔰.G₁, A (β y • W (g * y)) ∂μ‖ₑ := by
      simp only [h_transl, map_smul, smul_comm (β _), integral_smul]
    _ = ‖∫ y : 𝔰.G₁, A (β y • W (g * y)) ∂μ‖ₑ := by simp [← ofReal_norm, norm_smul]
    _ = ‖∫ y : 𝔰.G₁, β y • W (g * y) ∂μ‖ₑ := by rw [A.integral_comp_comm, A.enorm_map]

/-- The norm of a Bessel function `W` is invariant under left multiplication by the Bessel
subgroup. -/
lemma enorm_besselS_mul (hW : IsBesselFunction rep W) {s : 𝔰.G₁} (hs : s ∈ besselS)
    (y : 𝔰.G₁) : ‖W (s * y)‖ₑ = ‖W y‖ₑ := by
  -- the case of a unit mass at `1`
  simpa using hW.enorm_integral_besselS_mul hs 1 y (μ := .dirac 1)

end New.IsBesselFunction
