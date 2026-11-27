import Lib.General.Analysis.HolomorphicIntegrals
import Lib.General.Geometry.GeometricPoints
import Lib.Shimura.Uniformisation.HolomorphicFamilies

/-!
# Exponential of compact commutative Lie groups and uniformisation of abelian varieties

The complex points `New.ComplexPoint A` of a scheme `A` over ℂ carry the classical topology. Here
`A` is an object of `Over (Spec ℂ)`, and a point is a morphism from `Spec ℂ` over it. A smooth
scheme has holomorphic charts, and a projective variety has compact complex points. For an abelian
variety A with a projective embedding (`New.LineBundle.IsProjEmbedding`), the group A(ℂ) is
therefore compact and commutative with a holomorphic chart at 0. An exponential map exists for any
such group, and it gives a uniformisation of A by ℂᵈ, where d is the dimension of A.

## Main definitions and results

* `New.exists_lie_exponential` constructs the exponential map of a compact commutative group with a
  chart at `0` in which addition is complex analytic. The value at `v` is a limit of `n • ψ (v / n)`
  along an ultrafilter on `ℕ`, which exists by compactness; no differential equation is solved.
* `New.exists_holomorphic_chart`: a smooth scheme has a holomorphic chart at every complex point.
* `New.LineBundle.IsProjEmbedding.compactSpace_complexPoint`: the complex points of a projective
  variety are compact.
* `New.LineBundle.IsProjEmbedding.nonempty_uniformisation`: an abelian variety of dimension d is
  uniformised by ℂᵈ.

Notions from other files:
* `New.IsFullRankLattice L`: the `ℤ`-submodule `L` of `V` is discrete and spans `V` over `ℝ`. Here
  `V` is a `FinComplexSpace`, that is, a finite-dimensional complex normed space.
* `New.IsAbelianScheme`: a commutative group scheme A over S is abelian if it is smooth and proper
  over S and multiplication by every m ≠ 0 is surjective.
* `New.Uniformisation`: a surjective homomorphism from a complex vector space V to the complex
  points of A, with kernel a lattice, holomorphic and immersive, through which homomorphisms
  holomorphic at 0 factor ℂ-linearly.
* `New.LineBundle.IsProjEmbedding`: The linear system N embeds the proper scheme X in projective
  space: points in one chart with the same affine coordinates and the same base point are equal.
* `New.HasGermAt`: For each open U of X containing φ(w₀) and each f regular on U: φ(w) lies in U for
  w near w₀, and the function f∘φ satisfies Q. `New.HolomorphicAt` is the case where Q is
  analyticity at w₀.

## Relation to the literature

Known; see `Lib.Shimura.Uniformisation.AppellHumbert` for sources.
-/

/-! ## The exponential map of a compact commutative complex Lie group -/

section LieExponential

open Filter Topology Submodule AddSubgroup tangentConeAt Ultrafilter

/-- Let `φ : G → V` be a chart at `0` of a commutative group `G` with inverse `ψ`: `ψ 0 = 0` and
`φ ∘ ψ = id` near `0`. If addition read in the chart, `(v, w) ↦ φ (ψ v + ψ w)`, is analytic at `0`,
then its strict derivative at `0` is `(v, w) ↦ v + w`: on each axis the map is `φ ∘ ψ`. -/
lemma New.hasStrictFDerivAt_chart_add {G V : Type*} [AddCommGroup G] [FinComplexSpace V] {φ : G → V}
    {ψ : V → G} (ψ_zero : ψ 0 = 0) (h_right : φ ∘ ψ =ᶠ[𝓝 0] id)
    (h_add : AnalyticAt ℂ (fun p : V × V ↦ φ (ψ p.1 + ψ p.2)) 0) :
    HasStrictFDerivAt (𝕜 := ℂ) (fun p : V × V ↦ φ (ψ p.1 + ψ p.2)) (ContinuousLinearMap.coprod 1 1)
      0 := by
  -- Along an axis `i` of `V × V` the map is `φ ∘ ψ`, the identity near `0`.
  have on_axis (i : V →L[ℂ] V × V) (hi : ∀ w : V, ψ (i w).1 + ψ (i w).2 = ψ w) :
      (fderiv ℂ (fun p : V × V ↦ φ (ψ p.1 + ψ p.2)) 0).comp i = ContinuousLinearMap.id ℂ V := by
    have h_eq_id : (fun p : V × V ↦ φ (ψ p.1 + ψ p.2)) ∘ i =ᶠ[𝓝 0] id := by
      filter_upwards [h_right] with w hw
      simpa [hi] using hw
    have h_deriv : HasFDerivAt (fun p : V × V ↦ φ (ψ p.1 + ψ p.2))
        (fderiv ℂ (fun p : V × V ↦ φ (ψ p.1 + ψ p.2)) 0) (i 0) := by
      simpa using h_add.differentiableAt.hasFDerivAt
    exact (h_deriv.comp 0 i.hasFDerivAt).unique ((hasFDerivAt_id 0).congr_of_eventuallyEq h_eq_id)
  refine h_add.hasStrictFDerivAt.congr_fderiv ?_
  ext1
  · simpa [ContinuousLinearMap.one_def] using on_axis (.inl ℂ V V) (by simp [ψ_zero])
  · simpa [ContinuousLinearMap.one_def] using on_axis (.inr ℂ V V) (by simp [ψ_zero])

/-- Multiples in a chart: as long as `n • b` is small, `n • ψ b` stays in the set `C` on which `ψ`
inverts `φ`, and its coordinate is `n • b` up to a relative error `ε`. Here `φ 0 = 0`, `ψ 0 = 0`,
addition read in the chart stays in `C` near `0`, and its strict derivative at `0` is addition. -/
lemma New.exists_chart_nsmul_approx {G V : Type*} [AddCommGroup G] [FinComplexSpace V] {φ : G → V}
    {ψ : V → G} (h0 : φ 0 = 0) (ψ_zero : ψ 0 = 0) {C : Set G} (zero_mem : 0 ∈ C)
    (hC : ∀ x ∈ C, ψ (φ x) = x) (add_mem_C : ∀ᶠ p : V × V in 𝓝 0, ψ p.1 + ψ p.2 ∈ C)
    (add_deriv :
      HasStrictFDerivAt (𝕜 := ℂ) (fun p : V × V ↦ φ (ψ p.1 + ψ p.2))
        (ContinuousLinearMap.coprod 1 1) 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > (0 : ℝ), ∀ (b : V) (n : ℕ),
      (1 + ε) * ‖(n : ℝ) • b‖ < r →
      ‖φ (n • ψ b) - (n : ℝ) • b‖ ≤ ε * ‖(n : ℝ) • b‖ ∧ n • ψ b ∈ C := by
  -- Strict differentiability of addition in the chart, between `(φ x, b)` and `(φ x, 0)`.
  obtain ⟨r, r_pos, hr⟩ := Metric.eventually_nhds_iff.mp ((add_deriv.isLittleO.def hε).and
    (continuousAt_fst add_mem_C))
  -- One step: for `x ∈ C` with `φ x` and `b` small, adding `ψ b` adds `b` to `φ x` up to
  -- `ε * ‖b‖`.
  have step {x : G} {b : V} (hx : x ∈ C) (h_small : ‖φ x‖ + ‖b‖ < r) :
      ‖φ (x + ψ b) - φ x - b‖ ≤ ε * ‖b‖ ∧ x + ψ b ∈ C := by
    have near : dist (((φ x, b), φ x, 0) : (V × V) × V × V) 0 < r := by
      grind [dist_zero_right, Prod.norm_mk, norm_zero, norm_nonneg]
    simpa [ψ_zero, hC x hx] using hr near
  -- Adding up `n` steps, the errors `ε * ‖b‖` sum to `ε * ‖n • b‖`.
  refine ⟨r, r_pos, fun b n hn ↦ ?_⟩
  induction n with
    | zero => simp [h0, zero_mem]
    | succ n ih =>
      have norm_succ : ‖((n + 1 : ℕ) : ℝ) • b‖ = ‖(n : ℝ) • b‖ + ‖b‖ := by
        simp [add_smul, SameRay.norm_add]
      rw [norm_succ] at hn ⊢
      have εb_nonneg : 0 ≤ ε * ‖b‖ := by positivity
      obtain ⟨approx, mem⟩ := ih (by linarith [norm_nonneg b])
      have h_small : ‖φ (n • ψ b)‖ + ‖b‖ < r := by
        linarith [norm_le_norm_sub_add (φ (n • ψ b)) ((n : ℝ) • b)]
      obtain ⟨approx_step, mem_step⟩ := step mem h_small
      rw [succ_nsmul]
      refine ⟨?_, mem_step⟩
      calc
        _ = ‖(φ (n • ψ b) - (n : ℝ) • b) + (φ (n • ψ b + ψ b) - φ (n • ψ b) - b)‖ := by
          rw [Nat.cast_succ, add_smul, one_smul]
          abel_nf
        _ ≤ ε * ‖(n : ℝ) • b‖ + ε * ‖b‖ := norm_add_le_of_le approx approx_step
        _ = ε * (‖(n : ℝ) • b‖ + ‖b‖) := by ring

/-- Let `e : V →+ G` be a homomorphism from a finite-dimensional complex space to a compact group
that maps neighbourhoods of `0` onto neighbourhoods of `0` and has `0` as an isolated zero. Then its
kernel is a full-rank lattice in `V`. -/
lemma New.isFullRankLattice_ker_of_isolated {G V : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [FinComplexSpace V] (e : V →+ G)
    (isolated : ∀ᶠ v : V in 𝓝[≠] 0, e v ≠ 0) (e_open : 𝓝 (0 : G) ≤ Filter.map e (𝓝 0)) :
    IsFullRankLattice e.ker.toIntSubmodule := by
  have discrete : DiscreteTopology e.ker.toIntSubmodule :=
    discreteTopology_of_isOpen_singleton_zero ((isOpen_singleton_iff_punctured_nhds _).mpr
      (nhds_ne_subtype_eq_bot_iff.mpr (inf_principal_eq_bot.mpr isolated)))
  -- The kernel spans `V`. Otherwise a real form `l` kills the kernel and `l v ≠ 0` for some `v`.
  -- By compactness some `n • e v`, `n ≥ 1`, is so near `0` that it is `e b` with `|l b| < |l v|`;
  -- but `b - n • v` is in the kernel, so `l b = n * l v`.
  refine { toDiscreteTopology := discrete
           span_top := eq_top_iff'.mpr fun v ↦ by_contra fun hv ↦ ?_ }
  obtain ⟨l, lv_ne, l_ker⟩ := exists_le_ker_of_notMem hv
  have small : {b : V | |l b| < |l v|} ∈ 𝓝 (0 : V) :=
    l.toContinuousLinearMap.cont.abs.continuousAt (gt_mem_nhds (by simpa using lv_ne))
  have often : ∃ᶠ n : ℕ in atTop, n • e v ∈ e '' {b : V | |l b| < |l v|} :=
    (mapClusterPt_zero_atTop_nsmul (e v)).frequently (e_open (image_mem_map small))
  obtain ⟨n, ⟨b, lb_lt, eb_eq⟩, n_ge⟩ := (often.and_eventually (eventually_ge_atTop 1)).exists
  have h_ker : b - n • v ∈ (toIntSubmodule e.ker : Set V) := by simp [eb_eq]
  have lb_eq : l b = l (n • v) := l.sub_mem_ker_iff.mp (l_ker (subset_span h_ker))
  have hn_lt_one : n < 1 := by simpa [lb_eq, lv_ne] using lb_lt
  exact n_ge.not_gt hn_lt_one

private lemma tendsto_norm_natCast_hyperfilter :
    Tendsto (fun n : ℕ ↦ ‖(n : ℝ)‖) (hyperfilter ℕ) atTop :=
  tendsto_norm_atTop_atTop.comp (tendsto_natCast_atTop_iff.mpr Nat.hyperfilter_le_atTop)

/-- For a map `ψ : V → G`, `x` is an exponential limit of `v` when some sequence `b` has
`n • b n → v` and `n • ψ (b n) → x`, both along the hyperfilter of `ℕ`. -/
private def New.IsExpLimit {G V : Type*} [AddCommGroup G] [TopologicalSpace G] [FinComplexSpace V]
    (ψ : V → G) (v : V) (x : G) : Prop :=
  ∃ b : ℕ → V, Tendsto (fun n : ℕ ↦ (n : ℝ) • b n) (hyperfilter ℕ) (𝓝 v) ∧
    Tendsto (fun n : ℕ ↦ n • ψ (b n)) (hyperfilter ℕ) (𝓝 x)

/-- Exponential limits add. Let `ψ` invert `φ` on `C`, with `φ 0 = 0`, `ψ 0 = 0`, addition read in
the chart staying in `C` near `0` and having strict derivative `(v, w) ↦ v + w` at `0`. If `x` is an
exponential limit of `v` and `y` one of `w`, then `x + y` is one of `v + w`. -/
private lemma New.isExpLimit_add {G V : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [FinComplexSpace V] {φ : G → V} {ψ : V → G} (h0 : φ 0 = 0)
    (ψ_zero : ψ 0 = 0) {C : Set G} (hC_inv : ∀ x ∈ C, ψ (φ x) = x)
    (add_mem_C : ∀ᶠ p : V × V in 𝓝 0, ψ p.1 + ψ p.2 ∈ C)
    (add_deriv :
      HasStrictFDerivAt (𝕜 := ℂ) (fun p : V × V ↦ φ (ψ p.1 + ψ p.2))
        (ContinuousLinearMap.coprod 1 1) 0)
    {v w : V} {x y : G} (hx : IsExpLimit ψ v x) (hy : IsExpLimit ψ w y) :
    IsExpLimit ψ (v + w) (x + y) := by
  obtain ⟨b, hb, hb_lim⟩ := hx
  obtain ⟨c, hc, hc_lim⟩ := hy
  -- As `n • b n` and `n • c n` converge, `b n` and `c n` tend to `0`.
  have bc_zero : Tendsto (fun n : ℕ ↦ (b n, c n)) (hyperfilter ℕ) (𝓝 0) :=
    (lim_zero _ tendsto_norm_natCast_hyperfilter hb).prodMk_nhds
      (lim_zero _ tendsto_norm_natCast_hyperfilter hc)
  refine ⟨fun n ↦ φ (ψ (b n) + ψ (c n)), ?_, (hb_lim.add hc_lim).congr' ?_⟩
  · -- `n • φ (ψ (b n) + ψ (c n))` is a difference quotient of addition in the chart, so it tends
    -- to the derivative at `(v, w)`, which is `v + w` (`HasFDerivWithinAt.lim`).
    simpa [ψ_zero, h0] using
      (hasFDerivWithinAt_univ.mpr (add_deriv.hasFDerivAt.restrictScalars ℝ)).lim bc_zero univ_mem
        (hb.prodMk_nhds hc)
  · filter_upwards [bc_zero add_mem_C] with n hn
    rw [hC_inv _ hn, smul_add]

/-- The main estimate. Let `C` be a closed set containing `0` on which `ψ` inverts `φ` and `φ` is
continuous, with `φ 0 = 0`, `ψ 0 = 0`, addition read in the chart staying in `C` near `0` and having
strict derivative `(v, w) ↦ v + w` at `0`. If `x` is an exponential limit of a small `v`, then `x`
lies in the chart and `φ x = v` up to a relative error `ε`. -/
private lemma New.eventually_norm_sub_le_of_isExpLimit {G V : Type*} [AddCommGroup G]
    [TopologicalSpace G]
    [IsTopologicalAddGroup G] [FinComplexSpace V] {φ : G → V} {ψ : V → G} (h0 : φ 0 = 0)
    (ψ_zero : ψ 0 = 0) {C : Set G} (zero_mem : (0 : G) ∈ C) (C_closed : IsClosed C)
    (hC_inv : ∀ x ∈ C, ψ (φ x) = x) (hC_cont : ∀ x ∈ C, ContinuousAt φ x)
    (add_mem_C : ∀ᶠ p : V × V in 𝓝 0, ψ p.1 + ψ p.2 ∈ C)
    (add_deriv :
      HasStrictFDerivAt (𝕜 := ℂ) (fun p : V × V ↦ φ (ψ p.1 + ψ p.2))
        (ContinuousLinearMap.coprod 1 1) 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ v : V in 𝓝 0, ∀ {x : G}, IsExpLimit ψ v x → ψ (φ x) = x ∧ ‖φ x - v‖ ≤ ε * ‖v‖ := by
  obtain ⟨r, r_pos, multiples⟩ :=
    exists_chart_nsmul_approx h0 ψ_zero zero_mem hC_inv add_mem_C add_deriv hε
  -- Pass to the limit along the ultrafilter: `C` is closed and `φ` is continuous on it.
  have small : ∀ᶠ v : V in 𝓝 0, (1 + ε) * ‖v‖ < r :=
    (tendsto_norm_zero.const_mul _).eventually_lt_const (by simpa using r_pos)
  filter_upwards [small.eventually_nhds] with v hv x ⟨b, hb, hx⟩
  have near : ∀ᶠ n : ℕ in hyperfilter ℕ, (1 + ε) * ‖(n : ℝ) • b n‖ < r := hb.eventually hv
  have x_mem : x ∈ C :=
    C_closed.mem_of_tendsto hx (near.mono fun n hn ↦ (multiples _ n hn).right)
  have hφ_lim : Tendsto (fun n : ℕ ↦ φ (n • ψ (b n))) (hyperfilter ℕ) (𝓝 (φ x)) :=
    (hC_cont x x_mem).tendsto.comp hx
  have h_est : ‖φ x - v‖ ≤ ε * ‖v‖ :=
    le_of_tendsto_of_tendsto (hφ_lim.sub hb).norm (hb.norm.const_mul ε)
      (near.mono fun n hn ↦ (multiples _ n hn).left)
  exact ⟨hC_inv x x_mem, h_est⟩

/-- A homomorphism `e : V →+ G` read in the chart is analytic at `0`. Here addition read in the
chart is analytic at `0`, `φ 0 = 0`, `e` stays in the chart near `0` (`ψ (φ (e v)) = e v`), and
`φ ∘ e` has derivative the identity at `0`. -/
private lemma New.analyticAt_chart_comp_of_hasFDerivAt {G V : Type*} [AddCommGroup G]
    [FinComplexSpace V] {φ : G → V} {ψ : V → G} (h0 : φ 0 = 0)
    (h_add : AnalyticAt ℂ (fun p : V × V ↦ φ (ψ p.1 + ψ p.2)) 0) (e : V →+ G)
    (e_chart : ∀ᶠ v : V in 𝓝 0, ψ (φ (e v)) = e v)
    (e_deriv : HasFDerivAt (φ ∘ e) (ContinuousLinearMap.id ℂ V) 0) :
    AnalyticAt ℂ (φ ∘ e) 0 := by
  -- `φ ∘ e` is differentiable at every `x` near `0`, as `φ (e (x + y))` is the sum in the chart
  -- of `φ (e x)` and `φ (e y)`.
  have φe_tendsto : Tendsto (φ ∘ e) (𝓝 0) (𝓝 0) := by
    simpa [h0] using e_deriv.continuousAt.tendsto
  have add_analytic : ∀ᶠ p : V × V in 𝓝 (0, 0),
      AnalyticAt ℂ (fun q : V × V ↦ φ (ψ q.1 + ψ q.2)) (φ (e p.1), φ (e p.2)) :=
    (φe_tendsto.prodMap_nhds φe_tendsto).eventually h_add.eventually_analyticAt
  refine analyticAt_of_eventually_differentiableAt ?_
  filter_upwards [add_analytic.curry_nhds, e_chart] with x hx ψφx
  have sum_diff : DifferentiableAt ℂ ((fun w ↦ φ (ψ (φ (e x)) + ψ w)) ∘ φ ∘ e) 0 :=
    hx.self_of_nhds.curry_right.differentiableAt.comp 0 e_deriv.differentiableAt
  have h_shift_eq : (fun y : V ↦ (φ ∘ e) (x + y)) =ᶠ[𝓝 0]
      (fun w ↦ φ (ψ (φ (e x)) + ψ w)) ∘ φ ∘ e := by
    filter_upwards [e_chart] with y ψφy
    simp [ψφx, ψφy]
  simpa using (differentiableAt_comp_add_left (f := φ ∘ e) x).mp
    (sum_diff.congr_of_eventuallyEq h_shift_eq)

/-- The universal property of exponential limits. Let `ψ` invert `φ` near `0`, with `φ 0 = 0`. For a
homomorphism `γ : P →+ G`, continuous at `0` and with `φ ∘ γ` differentiable at `0`, `γ z` is an
exponential limit of `F z`, where `F` is the derivative of `φ ∘ γ` at `0`. -/
private lemma New.isExpLimit_fderiv_apply {G V P : Type*} [AddCommGroup G] [TopologicalSpace G]
    [FinComplexSpace V] [FinComplexSpace P] {φ : G → V} {ψ : V → G} (h0 : φ 0 = 0)
    (h_left : ∀ᶠ x : G in 𝓝 0, ψ (φ x) = x) (γ : P →+ G) (γ_cont : ContinuousAt γ 0)
    (γ_diff : DifferentiableAt ℂ (φ ∘ γ) 0) (z : P) :
    IsExpLimit ψ (fderiv ℂ (φ ∘ γ) 0 z) (γ z) := by
  -- The difference quotients of `φ ∘ γ` at `0` in the direction `z` tend to `F z`.
  refine ⟨_, (γ_diff.hasFDerivAt.restrictScalars ℝ).lim z tendsto_norm_natCast_hyperfilter,
    EventuallyEq.tendsto ?_⟩
  have near : ∀ᶠ n : ℕ in hyperfilter ℕ, ψ (φ (γ (‖(n : ℝ)‖⁻¹ • z))) = γ (‖(n : ℝ)‖⁻¹ • z) :=
    (tendsto_norm_natCast_hyperfilter.inv_tendsto_atTop.zero_smul_const z).eventually
      (γ_cont.eventually (by rwa [map_zero]))
  filter_upwards [near, tendsto_norm_natCast_hyperfilter.eventually_ne_atTop 0] with n ψφγ n_ne
  -- For `n ≠ 0`, `n • ψ (φ (γ (n⁻¹ • z))) = n • γ (n⁻¹ • z) = γ (n • n⁻¹ • z) = γ z`.
  simp_all [← map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]

/-- The exponential map. Let `G` be a compact commutative topological group and `φ : G → V` a chart
at `0`: `φ 0 = 0`, and `φ`, `ψ` are inverse to each other near `0`, with `φ` continuous near `0` and
`ψ` at `0`. Let addition be analytic in the chart. Then some homomorphism `e : V → G` has (a) a
lattice as kernel; (b) `ψ ∘ φ ∘ e = e` near `0`, and `φ ∘ e` analytic at `0` with derivative the
identity; (c) image of finite index; (d) every homomorphism `γ` from a finite-dimensional complex
normed space, continuous at `0` and differentiable at `0` in the chart, is `e ∘ F` for a continuous
linear `F`. -/
lemma New.exists_lie_exponential {G V : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [FinComplexSpace V] {φ : G → V} {ψ : V → G}
    (h0 : φ 0 = 0) (h_left : ∀ᶠ x : G in 𝓝 0, ψ (φ x) = x)
    (hφ_cont : ∀ᶠ x : G in 𝓝 0, ContinuousAt φ x) (h_right : φ ∘ ψ =ᶠ[𝓝 0] id)
    (hψ : ContinuousAt ψ 0) (h_add : AnalyticAt ℂ (fun p : V × V ↦ φ (ψ p.1 + ψ p.2)) 0) :
    ∃ e : V →+ G,
      -- (a) the kernel is a lattice
      IsFullRankLattice e.ker.toIntSubmodule ∧
      -- (b) near `0`, `e` lies in the chart, is analytic and has derivative `1`
      ψ ∘ φ ∘ e =ᶠ[𝓝 0] e ∧
      AnalyticAt ℂ (φ ∘ e) 0 ∧
      HasFDerivAt (φ ∘ e) (ContinuousLinearMap.id ℂ V) 0 ∧
      -- (c) the image has finite index
      e.range.FiniteIndex ∧
      -- (d) universal property
      ∀ {P : Type*} [FinComplexSpace P] (γ : P →+ G), ContinuousAt γ 0 →
        DifferentiableAt ℂ (φ ∘ γ) 0 → ∃ F : P →L[ℂ] V, ∀ z : P, e (F z) = γ z := by
  -- The value `e v` is the `x` with `IsExpLimit ψ v x`: a limit of `n • ψ (b n)` with
  -- `n • b n → v`, along an ultrafilter on `ℕ` (limits exist as `G` is compact). This relation
  -- is additive, and `φ x = v + o(v)` near `0`; hence it is the graph of a homomorphism `e` with
  -- derivative `1` at `0`. The rest uses the inverse function theorem and compactness.
  have ψ_zero : ψ 0 = 0 := by simpa [h0] using h_left.self_of_nhds
  -- A closed neighbourhood `C` of `0` on which `φ` is continuous with left inverse `ψ`.
  obtain ⟨C, C_nhds, C_closed, hC⟩ : ∃ C ∈ 𝓝 (0 : G),
      IsClosed C ∧ C ⊆ {x : G | ψ (φ x) = x ∧ ContinuousAt φ x} :=
    exists_mem_nhds_isClosed_subset (h_left.and hφ_cont)
  have hC_inv (x : G) (hx : x ∈ C) : ψ (φ x) = x := (hC hx).left
  have add_mem_C : ∀ᶠ p : V × V in 𝓝 0, ψ p.1 + ψ p.2 ∈ C :=
    hψ.fst'.fun_add hψ.snd' (by simpa [ψ_zero] using C_nhds)
  have add_deriv : HasStrictFDerivAt (𝕜 := ℂ) (fun p : V × V ↦ φ (ψ p.1 + ψ p.2))
      (ContinuousLinearMap.coprod 1 1) 0 :=
    hasStrictFDerivAt_chart_add ψ_zero h_right h_add
  have isExp_add {v w : V} {x y : G} (hx : IsExpLimit ψ v x) (hy : IsExpLimit ψ w y) :
      IsExpLimit ψ (v + w) (x + y) :=
    isExpLimit_add h0 ψ_zero hC_inv add_mem_C add_deriv hx hy
  have isExp_approx {ε : ℝ} (hε : 0 < ε) :
      ∀ᶠ v : V in 𝓝 0, ∀ {x : G}, IsExpLimit ψ v x → ψ (φ x) = x ∧ ‖φ x - v‖ ≤ ε * ‖v‖ :=
    eventually_norm_sub_le_of_isExpLimit h0 ψ_zero (mem_of_mem_nhds C_nhds) C_closed hC_inv
      (fun x hx ↦ (hC hx).right) add_mem_C add_deriv hε
  -- Existence: take `b n = n⁻¹ • v` and the limit of the ultrafilter in the compact group `G`.
  have h_exists (v : V) : ∃ x : G, IsExpLimit ψ v x := by
    let b (n : ℕ) : V := id (0 + (n : ℝ)⁻¹ • v) - id 0
    -- The image of the hyperfilter under `n ↦ n • ψ (b n)` converges, as `G` is compact.
    exact ⟨(Ultrafilter.map (fun n ↦ n • ψ (b n)) (hyperfilter ℕ)).lim, b,
      (hasFDerivAt_id 0).lim v tendsto_norm_natCast_hyperfilter, Ultrafilter.le_nhds_lim _⟩
  choose f hf using h_exists
  -- Uniqueness: `IsExpLimit ψ 0 y` forces `y = 0`; apply this to `y = x + f (-v)`.
  have isExp_unique {v : V} {x : G} (h : IsExpLimit ψ v x) : x = -f (-v) := by
    have h_sum : IsExpLimit ψ 0 (x + f (-v)) := by simpa using isExp_add h (hf (-v))
    obtain ⟨h_inv, h_est⟩ := (isExp_approx one_pos).self_of_nhds h_sum
    have h_φ_zero : φ (x + f (-v)) = 0 := by simpa using h_est
    rw [h_φ_zero, ψ_zero] at h_inv
    exact eq_neg_of_add_eq_zero_left h_inv.symm
  have isExp_eq {v : V} {x : G} (h : IsExpLimit ψ v x) : f v = x :=
    (isExp_unique (hf v)).trans (isExp_unique h).symm
  let e : V →+ G := .mk' f fun v w ↦ isExp_eq (isExp_add (hf v) (hf w))
  have e_chart : ∀ᶠ v : V in 𝓝 0, ψ (φ (e v)) = e v :=
    (isExp_approx one_pos).mono fun v h ↦ (h (hf v)).left
  have e_deriv : HasFDerivAt (φ ∘ e) (.id ℂ V) 0 := by
    refine .of_isLittleO (.of_bound fun ε hε ↦ ?_)
    filter_upwards [isExp_approx hε] with v h_v
    have h_est : ‖φ (e v) - v‖ ≤ ε * ‖v‖ := (h_v (hf v)).right
    simpa [h0] using h_est
  have e_analytic : AnalyticAt ℂ (φ ∘ e) 0 :=
    analyticAt_chart_comp_of_hasFDerivAt h0 h_add e e_chart e_deriv
  -- By the inverse function theorem, `e` maps neighbourhoods of `0` onto neighbourhoods of `0`.
  have e_open : 𝓝 (0 : G) ≤ map e (𝓝 0) := by
    have map_φe : map (φ ∘ e) (𝓝 0) = 𝓝 0 := by
      simpa [h0] using e_analytic.hasStrictFDerivAt.map_nhds_eq_of_surj (by simp [e_deriv.fderiv])
    calc
      𝓝 (0 : G) ≤ map ψ (𝓝 0) :=
        le_map_of_right_inverse h_left (by simpa only [h0] using hφ_cont.self_of_nhds.tendsto)
      _ = map (ψ ∘ φ ∘ e) (𝓝 0) := by rw [← Filter.map_map, map_φe]
      _ = map e (𝓝 0) := map_congr e_chart
  -- As `φ ∘ e` has an injective derivative, `0` is an isolated zero of `e`.
  have isolated : ∀ᶠ v : V in 𝓝[≠] 0, e v ≠ 0 :=
    (e_deriv.eventually_ne ⟨1, AntilipschitzWith.id⟩).mono fun _ ↦ ne_of_apply_ne φ
  -- The image is an open subgroup of a compact group, so it has finite index.
  have finite_index : e.range.FiniteIndex := finiteIndex_iff_finite_quotient.mpr
    (quotient_finite_of_isOpen _ (isOpen_of_mem_nhds _ (e_open (by simp))))
  have h_lattice : IsFullRankLattice e.ker.toIntSubmodule :=
    isFullRankLattice_ker_of_isolated e isolated e_open
  -- The universal property holds with `F` the derivative of `φ ∘ γ` at `0`.
  exact ⟨e, h_lattice, e_chart, e_analytic, e_deriv, finite_index, fun γ γ_cont γ_diff ↦
    ⟨fderiv ℂ (φ ∘ γ) 0, fun z ↦ isExp_eq (isExpLimit_fderiv_apply h0 h_left γ γ_cont γ_diff z)⟩⟩

end LieExponential

/-! ## Classical topology, charts, compactness and uniformisation -/

namespace New

open CategoryTheory AlgebraicGeometry Topology PointFn ProjSpace IsLocalRing Matrix Over Spec
  Function AnalyticAt TopologicalSpace ContinuousLinearMap.HasRightInverse ContinuousLinearEquiv
  MvPolynomial

attribute [local instance low] Fintype.ofFinite

variable {A : Over (Spec (CommRingCat.of ℂ))} {T : Type*} {ι : Type} {d : ℕ}
  {t₀ : T} [TopologicalSpace T] {γ : T → ComplexPoint A} [Finite ι] {N : LineBundle A.left ι}

/-- The classical topology on the complex points of `A`. It is generated by the sets of points that
lie in an open `U` (`LandsIn x.1 U`) and at which a function `f : PointFn` regular on `U`
(`IsRegularOn f U`), evaluated at `ℂ` and the point, takes a value in a given open set `O`. -/
instance : TopologicalSpace (ComplexPoint A) :=
  .induced (fun x U f O ↦ IsRegularOn f U ∧ IsOpen O ∧ LandsIn x.1 U ∧ f _ x.1 ∈ O) inferInstance

/-- A family `γ` of complex points is continuous at `t₀` for the classical topology iff, for
every open `U` containing `γ t₀` and every function `f` regular on `U`, the point `γ t` lies
in `U` for `t` near `t₀` and `t ↦ f (γ t)` is continuous at `t₀`. -/
lemma continuousAt_complexPoint_iff :
    ContinuousAt γ t₀ ↔ HasGermAt (fun g : T → ℂ ↦ ContinuousAt g t₀) (fun t : T ↦ (γ t).1) t₀ := by
  -- Unfold the induced topology: `γ` is continuous at `t₀` iff, for `f` regular on `U` and `O`
  -- open, the condition "`γ t ∈ U` and `f (γ t) ∈ O`" spreads from `t₀` to a neighbourhood.
  have h_unfold : ContinuousAt γ t₀ ↔ ∀ (U : A.left.Opens) (f : PointFn A.left) (O : Set ℂ),
      f.IsRegularOn U → IsOpen O → LandsIn (γ t₀).left U → f (CommRingCat.of ℂ) (γ t₀).left ∈ O →
        f.IsRegularOn U ∧ IsOpen O ∧ (∀ᶠ t in 𝓝 t₀, LandsIn (γ t).left U) ∧
          ∀ᶠ t in 𝓝 t₀, f (CommRingCat.of ℂ) (γ t).left ∈ O := by
    simp [ContinuousAt, tendsto_pi_nhds, nhds_induced, tendsto_nhds_Prop]
  have h_germ : HasGermAt (fun g : T → ℂ ↦ ContinuousAt g t₀) (fun t : T ↦ (γ t).1) t₀ ↔
      ∀ ⦃U : A.left.Opens⦄ ⦃f : PointFn A.left⦄, f.IsRegularOn U → LandsIn (γ t₀).left U →
        (∀ᶠ t in 𝓝 t₀, LandsIn (γ t).left U) ∧
          ∀ O' : Set ℂ, f (CommRingCat.of ℂ) (γ t₀).left ∈ O' → IsOpen O' →
            ∀ᶠ t in 𝓝 t₀, f (CommRingCat.of ℂ) (γ t).left ∈ O' := by
    simp [HasGermAt, ContinuousAt, (nhds_basis_opens (_ : ℂ)).tendsto_right_iff]
  rw [h_unfold, h_germ]
  constructor
  · intro h U f hf hU
    -- The case `O = univ` says that `γ` stays in `U`.
    obtain ⟨-, -, h_lands, -⟩ := h U f Set.univ hf isOpen_univ hU (Set.mem_univ _)
    exact ⟨h_lands, fun O hO hO_open ↦ (h U f O hf hO_open hU hO).right.right.right⟩
  · intro h U f O hf hO_open hU hO
    obtain ⟨h_lands, h_mem⟩ := h hf hU
    exact ⟨hf, hO_open, h_lands, h_mem O hO hO_open⟩

/-- The zeros of an analytic map `F : ℂ^ι → ℂ^σ` near a zero `p₀` with onto derivative have an
analytic chart `c` to `ℂᵈ`, `d = #ι - #σ`, with analytic local inverse `g`. -/
lemma exists_zero_set_chart {ι σ : Type} [Finite ι] [Finite σ] {d : ℕ} {F : (ι → ℂ) → σ → ℂ}
    {p₀ : ι → ℂ} (hF : ∀ p : ι → ℂ, AnalyticAt ℂ F p) (hF0 : F p₀ = 0)
    (h_onto : Function.Surjective (fderiv ℂ F p₀)) (h_dim : Nat.card ι - Nat.card σ = d) :
    ∃ (c : (ι → ℂ) → Fin d → ℂ) (g : (Fin d → ℂ) → ι → ℂ),
      (∀ p : ι → ℂ, AnalyticAt ℂ c p) ∧
      c p₀ = 0 ∧ AnalyticAt ℂ g 0 ∧
      (∀ᶠ z : Fin d → ℂ in 𝓝 0, F (g z) = 0 ∧ c (g z) = z) ∧
      ∀ᶠ p : ι → ℂ in 𝓝 p₀, F p = 0 → g (c p) = p := by
  -- Split off the kernel of the derivative, which has dimension d: G is an isomorphism with first
  -- component dF. Its second component c completes F to a local isomorphism (F, c).
  let G₀ : (ι → ℂ) ≃L[ℂ] (σ → ℂ) × (fderiv ℂ F p₀).ker :=
    equivOfRightInverse (fderiv ℂ F p₀) (of_surjective_of_finiteDimensional h_onto).choose
      (of_surjective_of_finiteDimensional h_onto).choose_spec
  have h_rank : Module.finrank ℂ (ι → ℂ) = Module.finrank ℂ ((σ → ℂ) × (fderiv ℂ F p₀).ker) :=
    G₀.finrank_eq
  have h_ker_rank : Module.finrank ℂ (fderiv ℂ F p₀).ker = Module.finrank ℂ (Fin d → ℂ) := by
    simp_all
  let G : (ι → ℂ) ≃L[ℂ] (σ → ℂ) × (Fin d → ℂ) :=
    G₀.trans (.prodCongr (.refl ℂ (σ → ℂ)) (.ofFinrankEq h_ker_rank))
  let c (p : ι → ℂ) : Fin d → ℂ := (G p - G p₀).snd
  have hc (p : ι → ℂ) : AnalyticAt ℂ c p := ContDiffAt.analyticAt (by fun_prop)
  have hc0 : c p₀ = 0 := sub_self (G p₀).snd
  have hΦ : HasStrictFDerivAt (fun p : ι → ℂ ↦ (F p, c p)) G.toContinuousLinearMap p₀ :=
    (hF _).hasStrictFDerivAt.prodMk (G.hasStrictFDerivAt.sub_const _).snd
  -- By the inverse function theorem, g parametrises the zeros of F near p₀ by the value of c.
  let g (z : Fin d → ℂ) : ι → ℂ := hΦ.localInverse (fun p : ι → ℂ ↦ (F p, c p)) G p₀ (F p₀, z)
  refine ⟨c, g, hc, hc0, ?_, ?_, ?_⟩
  · show AnalyticAt ℂ g 0
    have h_inv_an : AnalyticAt ℂ (hΦ.localInverse (fun p : ι → ℂ ↦ (F p, c p)) G p₀) (F p₀, c p₀) :=
      ((hF p₀).prod (hc p₀)).contDiffAt.to_localInverse hΦ.hasFDerivAt top_ne_bot |>.analyticAt
    rw [hc0] at h_inv_an
    exact h_inv_an.curry_right
  · show ∀ᶠ (z : Fin d → ℂ) in 𝓝 0, F (g z) = 0 ∧ c (g z) = z
    have h_right : ∀ᶠ z : Fin d → ℂ in 𝓝 (c p₀), (F (g z), c (g z)) = (F p₀, z) :=
      hΦ.eventually_right_inverse.curry_nhds.self_of_nhds
    rw [hc0] at h_right
    filter_upwards [h_right] with z hz
    simpa [hF0] using hz
  · -- near `p₀`, `g` is a left inverse of `c` on the zeros of `F`
    filter_upwards [hΦ.eventually_left_inverse] with p hp hFp
    simpa [g, hF0, hFp] using hp

/-- Let `P` present `Γ(A, U)` over `Γ(Spec ℂ, V)`, the algebra map being `A.hom.appLE V U e`. At
a complex point `y` of `U`, a polynomial `q` in the generators takes the value of the polynomial
function of `q` (constants evaluated at the base point) at the coordinates of `y`. -/
private lemma ofSection_aeval_eq_eval {V : (Spec (CommRingCat.of ℂ)).Opens} {U : A.left.Opens}
    (e : U ≤ A.hom ⁻¹ᵁ V) {ι σ : Type} [Finite ι] [Finite σ]
    [Algebra Γ(Spec (CommRingCat.of ℂ), V) Γ(A.left, U)]
    (h_alg : algebraMap Γ(Spec (CommRingCat.of ℂ), V) Γ(A.left, U) = (A.hom.appLE V U e).hom)
    (P : Algebra.SubmersivePresentation Γ(Spec (CommRingCat.of ℂ), V) Γ(A.left, U) ι σ)
    (hV1 : LandsIn (𝟙 (Spec (CommRingCat.of ℂ))) V) (y : ComplexPoint A) (hy : LandsIn y.left U)
    (q : P.Ring) :
    PointFn.ofSection (aeval P.val q) (CommRingCat.of ℂ) y.left =
      MvPolynomial.eval (fun i : ι ↦ PointFn.ofSection (P.val i) (CommRingCat.of ℂ) y.left)
        (MvPolynomial.map (evalSection (𝟙 (Spec (CommRingCat.of ℂ))) hV1).hom q) := by
  simp only [ofSection_eq hy, map_aeval, coe_eval₂Hom, MvPolynomial.eval_map]
  congr 1 with r
  -- The constants are evaluated along `A.hom`, which sends `y` to the base point.
  simpa [ofSection_eq, hy, hV1, h_alg] using ofSection_appLE A.hom e r hy

/-- Let `P` be a submersive presentation of `Γ(A, U)` over `Γ(Spec ℂ, V)` and `x` a complex point of
`U` at which each `aeval P.val q` takes the value of the polynomial function of `q` at the
coordinates of `x`. Read the relations of `P` as polynomial functions on `ℂ^ι`; their derivative at
the coordinates of `x` is onto, because the Jacobian minor of `P` is a unit. -/
private lemma surjective_fderiv_relations {V : (Spec (CommRingCat.of ℂ)).Opens} {U : A.left.Opens}
    {ι σ : Type} [Finite ι] [Finite σ] [Algebra Γ(Spec (CommRingCat.of ℂ), V) Γ(A.left, U)]
    (P : Algebra.SubmersivePresentation Γ(Spec (CommRingCat.of ℂ), V) Γ(A.left, U) ι σ)
    (hV1 : LandsIn (𝟙 (Spec (CommRingCat.of ℂ))) V) (x : ComplexPoint A) (hx : LandsIn x.left U)
    (h_eval : ∀ q : P.Ring, PointFn.ofSection (aeval P.val q) (CommRingCat.of ℂ) x.left =
      MvPolynomial.eval (fun i : ι ↦ PointFn.ofSection (P.val i) (CommRingCat.of ℂ) x.left)
        (MvPolynomial.map (evalSection (𝟙 (Spec (CommRingCat.of ℂ))) hV1).hom q)) :
    Function.Surjective (fderiv ℂ
      (fun (p : ι → ℂ) (j : σ) ↦ MvPolynomial.eval p
        (MvPolynomial.map (evalSection (𝟙 (Spec (CommRingCat.of ℂ))) hV1).hom (P.relation j)))
      (fun i : ι ↦ PointFn.ofSection (P.val i) (CommRingCat.of ℂ) x.left)) := by
  classical
  have h_jac : IsUnit (P.aevalDifferentialEquiv : Module.End Γ(A.left, U) (σ → Γ(A.left, U))) :=
    (Module.End.isUnit_iff _).mpr P.aevalDifferentialEquiv.bijective
  have h_unit : IsUnit ((evalSection x.left hx).hom.mapMatrix (LinearMap.toMatrix'
      (P.aevalDifferentialEquiv : Module.End Γ(A.left, U) (σ → Γ(A.left, U))))) :=
    (LinearMap.isUnit_toMatrix'_iff.mpr h_jac).map (evalSection x.left hx).hom.mapMatrix
  refine (vecMul_surjective_iff_isUnit.mpr h_unit).forall.mpr fun v ↦
    ⟨∑ j, v j • Pi.single (P.map j) 1, ?_⟩
  rw [(hasFDerivAt_pi.mpr fun _ ↦ hasFDerivAt_mvPolynomial_eval ..).fderiv]
  ext
  simp [h_eval, ← ofSection_eq hx, vecMul_eq_sum, Pi.single_apply, pderiv_map]

private lemma concreteCategory_hom_eq_hom {R S : CommRingCat} (f : R ⟶ S) :
    ConcreteCategory.hom f = f.hom :=
  rfl

/-- Let `P` present `Γ(A, U)` over `Γ(Spec ℂ, V)`, the algebra map being `A.hom.appLE V U e`, for
affine opens `U` and `V`. Every zero `p` of the relations of `P`, read as polynomial functions on
`ℂ^ι`, is the vector of coordinates of a complex point of `U`. -/
private lemma exists_point_of_relations_eq_zero {V : (Spec (CommRingCat.of ℂ)).Opens}
    {U : A.left.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ A.hom ⁻¹ᵁ V)
    {ι σ : Type} [Finite ι] [Finite σ] [Algebra Γ(Spec (CommRingCat.of ℂ), V) Γ(A.left, U)]
    (h_alg : algebraMap Γ(Spec (CommRingCat.of ℂ), V) Γ(A.left, U) = (A.hom.appLE V U e).hom)
    (P : Algebra.SubmersivePresentation Γ(Spec (CommRingCat.of ℂ), V) Γ(A.left, U) ι σ)
    (hV1 : LandsIn (𝟙 (Spec (CommRingCat.of ℂ))) V) (p : ι → ℂ)
    (hp : ∀ j : σ, MvPolynomial.eval p
      (MvPolynomial.map (evalSection (𝟙 (Spec (CommRingCat.of ℂ))) hV1).hom (P.relation j)) = 0) :
    ∃ y : ComplexPoint A, LandsIn y.left U ∧
      (fun i : ι ↦ PointFn.ofSection (P.val i) (CommRingCat.of ℂ) y.left) = p := by
  -- Evaluation at `p` kills the relations, so it factors through `Γ(A, U)` as `lift`.
  let ev : P.Ring →+* ℂ := (MvPolynomial.eval p).comp
    (MvPolynomial.map (evalSection (𝟙 (Spec (CommRingCat.of ℂ))) hV1).hom)
  have h_ker : P.ker ≤ RingHom.ker ev := by
    rw [← P.span_range_relation_eq_ker]
    exact Ideal.span_le.mpr (Set.forall_mem_range.mpr hp)
  let lift : Γ(A.left, U) →+* ℂ :=
    (algebraMap P.Ring Γ(A.left, U)).liftOfSurjective P.algebraMap_surjective ⟨ev, h_ker⟩
  have h_lift (q : P.Ring) : lift (algebraMap P.Ring Γ(A.left, U) q) = ev q :=
    RingHom.liftOfSurjective_comp_apply _ P.algebraMap_surjective ⟨ev, h_ker⟩ q
  refine ⟨homMk (map (CommRingCat.ofHom lift : Γ(A.left, U) ⟶ CommRingCat.of ℂ) ≫ hU.fromSpec)
      (point_eq_of_ofSection_eq hV (landsIn_preimage.mp ((landsIn_fromSpec hU _).mono e)) hV1
        fun r ↦ ?_),
    landsIn_fromSpec hU _, funext fun i ↦ ?_⟩
  · -- The point lies over `Spec ℂ`, since the constants are evaluated as before.
    rw [← ofSection_appLE A.hom e r (landsIn_fromSpec hU _)]
    simpa [landsIn_fromSpec hU, ofSection_eq hV1, h_alg, ev, concreteCategory_hom_eq_hom] using
      h_lift (C r)
  · -- Its `i`-th coordinate is `p i`: the generator `X i` evaluates to `p i`.
    simpa [Algebra.Generators.algebraMap_apply, ev] using h_lift (X i)

/-- A scheme smooth of relative dimension `d` over ℂ has a holomorphic chart at every complex point
`x`: maps `φ` to ℂᵈ and `ψ` back with `φ x = 0`, such that `ψ` inverts `φ` near `x` and near `0`,
`φ` is continuous near `x`, `ψ` is a holomorphic family at `0`, and along every holomorphic family
`γ` through `x` the map `φ ∘ γ` is analytic, with derivative zero in each direction in which `γ`
is constant to first order. -/
lemma exists_holomorphic_chart (hd : SmoothOfRelativeDimension d A.hom) (x : ComplexPoint A) :
    ∃ᵉ (φ : ComplexPoint A → Fin d → ℂ) (ψ : (Fin d → ℂ) → ComplexPoint A),
      φ x = 0 ∧
      -- (a) `ψ` is a left inverse of `φ` near `x`, where `φ` is continuous
      (∀ᶠ y : ComplexPoint A in 𝓝 x, ψ (φ y) = y ∧ ContinuousAt φ y) ∧
      -- (b) `ψ` is a right inverse of `φ` near `0`
      φ ∘ ψ =ᶠ[𝓝 0] id ∧
      -- (c) `ψ` is a holomorphic family of points
      HolomorphicAt (fun z : Fin d → ℂ ↦ (ψ z).left) 0 ∧
      -- (d) `φ` takes holomorphic families through `x` to analytic maps, and a zero
      -- tangent vector of the family to a zero derivative
      ∀ {P : Type} [FinComplexSpace P] {γ : P → ComplexPoint A} {w : P}, γ w = x →
        HolomorphicAt (fun z : P ↦ (γ z).1) w →
        AnalyticAt ℂ (φ ∘ γ) w ∧
        ∀ v : P, IsFirstOrderConst (fun z : P ↦ (γ z).1) w v → fderiv ℂ (φ ∘ γ) w v = 0 := by
  classical
  -- Near x the scheme is cut out of affine space ℂ^ι by equations F with onto derivative. The
  -- chart of the scheme is the chart c of the zeros of F (`exists_zero_set_chart`), applied to
  -- the coordinates of a point.
  -- `P` is a submersive presentation of Γ(A, U) over Γ(Spec ℂ, V), for affine opens U ∋ x and V,
  -- with variables ι, relations σ and #ι - #σ = d; the two `_` are the finiteness instances.
  obtain ⟨V, hV, U, hU, hxU, e, ι, σ, _, _, P, (h_dim : Nat.card ι - Nat.card σ = d)⟩ :=
    hd.exists_isStandardSmoothOfRelativeDimension (x.left (closedPoint ℂ))
  have h_nonempty : Nonempty (ComplexPoint A) := ⟨x⟩
  have hx : LandsIn x.left U := landsIn_iff_mem.mpr hxU
  have hV1 : LandsIn (𝟙 _) V := by simpa using hx.mono e
  algebraize [(A.hom.appLE V U e).hom]
  -- `E q` is the polynomial function on ℂ^ι of `q`; `a y` are the coordinates of a point `y` of
  -- `U`.
  let E (q : P.Ring) (p : ι → ℂ) : ℂ :=
    (MvPolynomial.eval p).comp (MvPolynomial.map (evalSection _ hV1).hom) q
  have hE {p : ι → ℂ} {q : P.Ring} : AnalyticAt ℂ (E q) p := AnalyticOnNhd.eval_mvPolynomial _ _ ⟨⟩
  let a (y : ComplexPoint A) (i : ι) : ℂ := PointFn.ofSection (P.val i) _ y.left
  have ev_aeval (y : ComplexPoint A) (hy : LandsIn y.left U) (q : P.Ring) :
      PointFn.ofSection (aeval P.val q) _ y.left = E q (a y) :=
    ofSection_aeval_eq_eval e (RingHom.algebraMap_toAlgebra _) P hV1 y hy q
  let F (p : ι → ℂ) (j : σ) : ℂ := E (P.relation j) p
  have hF {y : ComplexPoint A} (hy : LandsIn y.left U) : F (a y) = 0 := by
    simp [F, ← ev_aeval, hy, funext_iff]
  -- The Jacobian minor of the presentation is a unit, so the derivative of `F` at `a x` is onto,
  -- and the zeros of `F` near `a x` have a chart `c` with local inverse `g`.
  obtain ⟨c, g, hc, hc0, hg_an, hg, h_inv⟩ :=
    exists_zero_set_chart (F := F) (fun _ ↦ pi fun _ ↦ hE) (hF hx)
      (surjective_fderiv_relations P hV1 x hx (ev_aeval x hx)) h_dim
  -- Every zero p of F is the vector of coordinates of a point of U: evaluation at p kills the
  -- relations, so it factors through Γ(A, U).
  have h_pt (p : ι → ℂ) (hp : F p = 0) : ∃ y : ComplexPoint A, LandsIn y.left U ∧ a y = p :=
    exists_point_of_relations_eq_zero hV hU e (RingHom.algebraMap_toAlgebra _) P hV1 p
      (fun j ↦ congrFun hp j)
  choose! ψ hψ using h_pt
  -- `U` is a neighbourhood of its points, and sections over `U` (so the coordinates) are
  -- continuous.
  have h_near (y : ComplexPoint A) (s : Γ(A.left, U)) (hy : LandsIn y.left U) :
      (∀ᶠ t : ComplexPoint A in 𝓝 y, LandsIn t.left U) ∧
        ContinuousAt (fun t : ComplexPoint A ↦ ofSection s (CommRingCat.of ℂ) t.left) y :=
    continuousAt_complexPoint_iff.mp (continuousAt_id' y) (isRegularOn_ofSection s) hy
  have ha (y : ComplexPoint A) (hy : LandsIn y.left U) : ContinuousAt a y :=
    continuousAt_pi' (f := a) fun i ↦ (h_near y (P.val i) hy).right
  refine ⟨c ∘ a, ψ ∘ g, hc0, ?_, ?_, ?_, fun {Q} [FinComplexSpace Q] {γ'} {w} hγ h_hol ↦ ?_⟩
  · -- Left inverse: a point of `U` near `x` is determined by its coordinates, and
    -- `g (c (a y)) = a y`.
    filter_upwards [(h_near x 0 hx).left, (ha x hx).eventually h_inv] with y hy h_inv
    obtain ⟨h_in, h_a⟩ := hψ (a y) (hF hy)
    refine ⟨?_, (hc _).continuousAt.comp (ha y hy)⟩
    simp only [Function.comp_apply, h_inv (hF hy)]
    refine OverMorphism.ext (point_eq_of_ofSection_eq hU h_in hy fun s ↦ ?_)
    obtain ⟨q, rfl⟩ := P.aeval_val_surjective s
    rw [ev_aeval _ h_in, ev_aeval _ hy, h_a]
  · -- Right inverse: `ψ (g z)` has coordinates `g z`, and `c (g z) = z`.
    filter_upwards [hg] with z ⟨hFz, hcz⟩
    simp [(hψ (g z) hFz).2, hcz]
  · -- The inverse is holomorphic: its coordinates `g` are analytic.
    refine .of_affine hU (hg.mono fun z hz ↦ (hψ _ hz.left).left) fun s ↦ ?_
    obtain ⟨q, rfl⟩ := P.aeval_val_surjective s
    refine ((hE (q := q)).comp hg_an).congr (hg.mono fun z hz ↦ ?_)
    simp [ev_aeval, hψ _ hz.left]
  · -- The coordinates of a holomorphic family are analytic; then use the chain rule.
    have h_lands : LandsIn (γ' w).left U := by rwa [hγ]
    have h_an (i : ι) :
        AnalyticAt ℂ (fun z : Q ↦ ofSection (P.val i) (CommRingCat.of ℂ) (γ' z).left) w :=
      (h_hol (isRegularOn_ofSection (P.val i)) h_lands).right
    refine ⟨(hc _).comp (pi h_an), fun v hv ↦ ?_⟩
    rw [show (c ∘ a) ∘ γ' = c ∘ fun z i ↦ ofSection (P.val i) _ (γ' z).left from rfl,
      fderiv_comp w (hc _).differentiableAt (pi h_an).differentiableAt]
    simp [isFirstOrderConst_iff.mp hv, ← Pi.zero_def, fderiv_pi, differentiableAt, h_an, h_lands]

/-- The complex points of a projective variety `A`, embedded by the linear system
`N : LineBundle A.left ι` with `ι` finite, are compact in the classical topology: they are a
continuous image of a closed subset of the unit sphere. -/
lemma LineBundle.IsProjEmbedding.compactSpace_complexPoint (hN : N.IsProjEmbedding A.hom) :
    CompactSpace (ComplexPoint A) := by
  -- The points are the continuous image of a closed subset K of the unit sphere in ℂ^ι.
  -- First the homogeneous coordinates of each point, and the closed immersion j into projective
  -- space along which N is pulled back.
  have h_coord (x : ComplexPoint A) : ∃ p : ι → ℂ, N.IsHomogeneousCoords x.left p :=
    ⟨_, hN.isLinearSystem.isHomogeneousCoords_transition (N.exists_landsIn x.left).choose_spec⟩
  obtain ⟨j, hj_closed, hj, rfl⟩ : ∃ j : A.left ⟶ ProjSpace ι ⨯ Spec (CommRingCat.of ℂ),
      IsClosedImmersion j ∧ j ≫ Limits.prod.snd = A.hom ∧
        ((hyperplaneBundle ι).pull Limits.prod.fst).pull j = N :=
    hN.exists_isClosedImmersion
  -- Each unit vector `c` gives a point `t c` of projective space, continuously in `c`.
  have h_points (c : Metric.sphere (0 : ι → ℂ) 1) : ∃ t : Spec ⟨ℂ⟩ ⟶ ProjSpace ι ⨯ Spec ⟨ℂ⟩,
      t ≫ Limits.prod.snd = 𝟙 (Spec ⟨ℂ⟩) ∧
        ((hyperplaneBundle ι).pull Limits.prod.fst).IsHomogeneousCoords t (c : ι → ℂ) := by
    -- A unit vector has a nonzero coordinate `i`.
    obtain ⟨i, hi⟩ := ne_iff.mp (ne_zero_of_mem_unit_sphere c)
    exact exists_isHomogeneousCoords (𝟙 (Spec ⟨ℂ⟩)) hi.isUnit
  choose t ht_over ht_lifts using h_points
  have ht_cont (c : Metric.sphere (0 : ι → ℂ) 1) : HasGermAt (ContinuousAt · c) t c :=
    .of_isHomogeneousCoords isProjEmbedding_projSpace (continuousAt_pi.mp (by fun_prop))
      (.of_forall ht_lifts) ht_over
  -- So the unit vectors whose point is outside the image of `j` form an open set; `K` is the rest.
  let W : Scheme.Opens (ProjSpace ι ⨯ Spec (CommRingCat.of ℂ)) :=
    ⟨(Set.range j)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have h_open : IsOpen {c | LandsIn (t c) W} :=
    isOpen_iff_mem_nhds.mpr fun c hc ↦ (ht_cont c (isRegularOn_ofSection 0) hc).left
  let K : Compacts (Metric.sphere (0 : ι → ℂ) 1) :=
    ⟨{c | LandsIn (t c) W}ᶜ, h_open.isClosed_compl.isCompact⟩
  -- For `c` in `K` the point `t c` factors through `j`.
  have h_lift (c : K) : ∃ s : Spec ⟨ℂ⟩ ⟶ A.left, s ≫ j = t c := by
    have h_mem : t c (closedPoint ℂ) ∈ Set.range j :=
      by_contra fun h ↦ c.prop (landsIn_iff_mem.mpr h)
    exact exists_lift_of_dense_preimage j _ (dense_indiscrete ⟨closedPoint ℂ, h_mem⟩)
  choose s hs using h_lift
  let f (c : K) : ComplexPoint A := homMk (s c) (by simp [← hj, reassoc_of% hs, ht_over])
  have hf : Continuous f := by
    refine continuous_iff_continuousAt.mpr fun c ↦ continuousAt_complexPoint_iff.mpr ?_
    have hv_coords (c : K) : (((hyperplaneBundle ι).pull Limits.prod.fst).pull
        j).IsHomogeneousCoords (f c).left (c.1 : ι → ℂ) := by
      rw [IsHomogeneousCoords.pull_iff, show (f c).left ≫ j = t c from hs c]
      exact ht_lifts c
    exact .of_isHomogeneousCoords hN (continuousAt_pi.mp (by fun_prop)) (.of_forall hv_coords)
      fun c ↦ Over.w (f c)
  refine Function.Surjective.compactSpace (f := f) hf fun x ↦ ?_
  -- Onto: normalise the coordinates `p` of `x` to a unit vector `c`; then `t c` is the image of `x`
  -- under `j`.
  obtain ⟨p, hp⟩ := h_coord x
  have hp_ne : p ≠ 0 := hp.ne_zero
  let c : Metric.sphere (0 : ι → ℂ) 1 :=
    ⟨(‖p‖ : ℂ)⁻¹ • p, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hp_ne)⟩
  have h_unit : IsUnit ((‖p‖ : ℂ)⁻¹) := by simpa using hp_ne
  have h_over : (x.left ≫ j) ≫ Limits.prod.snd = t c ≫ Limits.prod.snd := by simp [hj, ht_over]
  -- points with the same homogeneous coordinates are equal
  have hc : x.left ≫ j = t c :=
    isProjEmbedding_projSpace.eq_of_isHomogeneousCoords h_over
      ((IsHomogeneousCoords.pull_iff.mp hp).smul h_unit) (ht_lifts c)
        (LineBundle.exists_landsIn _ _)
  have h_base : (x.left ≫ j) (closedPoint ℂ) = (t c) (closedPoint ℂ) := by rw [hc]
  have hcK : c ∈ K := fun h ↦ landsIn_iff_mem.mp h ⟨_, h_base⟩
  exact ⟨⟨c, hcK⟩, OverMorphism.ext (by simpa [f, ← cancel_mono j, hs] using hc.symm)⟩

/-- On the complex points of an abelian variety with a projective embedding, addition and negation
are continuous: they are morphisms of schemes. -/
private lemma isTopologicalAddGroup_complexPoint [IsAbelianScheme A]
    (hN : N.IsProjEmbedding A.hom) : IsTopologicalAddGroup (ComplexPoint A) := by
  refine { continuous_add := ?_, continuous_neg := ?_ }
  · refine continuous_iff_continuousAt.mpr fun _ ↦
      continuousAt_complexPoint_iff.mpr (.comp_hom ?_ _)
    -- Every goal that `apply_rules` leaves is a continuity side condition.
    apply_rules [HasGermAt.lift, continuousAt_complexPoint_iff.mp] <;> fun_prop
  · exact continuous_iff_continuousAt.mpr fun _ ↦ continuousAt_complexPoint_iff.mpr
      (.comp_hom (continuousAt_complexPoint_iff.mp continuousAt_id) _)

/-- Let `φ`, `ψ` be a chart at `0` of the complex points of `A`, with `φ 0 = 0` and `ψ` holomorphic
at `0`, and let `e` be a homomorphism from `ℂᵈ` with `φ ∘ e` analytic at `0` and `ψ ∘ φ ∘ e = e`
near `0`. Then `e` is a holomorphic family of points at `0`. -/
private lemma holomorphicAt_of_analyticAt_chart_comp [IsAbelianScheme A]
    {φ : ComplexPoint A → Fin d → ℂ} {ψ : (Fin d → ℂ) → ComplexPoint A} (hφ0 : φ 0 = 0)
    (hψ_hol : HolomorphicAt (fun z : Fin d → ℂ ↦ (ψ z).left) 0)
    (e : (Fin d → ℂ) →+ ComplexPoint A) (he_an : AnalyticAt ℂ (φ ∘ e) 0)
    (he_near : ψ ∘ φ ∘ e =ᶠ[𝓝 0] e) :
    HolomorphicAt (fun z : Fin d → ℂ ↦ (e z).left) 0 := by
  have hψ_hol_at : HolomorphicAt (fun w ↦ (ψ w).left) ((φ ∘ e) 0) := by simpa [hφ0] using hψ_hol
  have h_comp : HolomorphicAt (fun z ↦ (ψ (φ (e z))).left) 0 :=
    .comp (φ := fun w ↦ (ψ w).left) hψ_hol_at he_an
  intro U f hf hU
  replace he_near : ∀ᶠ z in 𝓝 0, ψ (φ (e z)) = e z := he_near
  have hU_comp : LandsIn (ψ (φ (e 0))).left U := by simpa only [he_near.self_of_nhds] using hU
  obtain ⟨h_in, h_an⟩ : (∀ᶠ z in 𝓝 0, LandsIn (ψ (φ (e z))).left U) ∧
      AnalyticAt ℂ (fun z ↦ f (CommRingCat.of ℂ) (ψ (φ (e z))).left) 0 :=
    h_comp hf hU_comp
  have h_lands_e : ∀ᶠ z in 𝓝 0, LandsIn (e z).left U := by
    filter_upwards [h_in, he_near] with z hz_in hz_eq
    rwa [hz_eq] at hz_in
  exact ⟨h_lands_e, h_an.congr (he_near.mono fun z hz ↦ by simp only [hz])⟩

/-- Uniformisation: an abelian variety A over ℂ, smooth of relative dimension d and embedded in
projective space by a linear system N, admits a uniformisation ℂ^d/L ≅ A(ℂ), with L a lattice in
ℂ^d. -/
lemma LineBundle.IsProjEmbedding.nonempty_uniformisation [IsAbelianScheme A]
    (hN : N.IsProjEmbedding A.hom) (hd : SmoothOfRelativeDimension d A.hom) :
    Nonempty (Uniformisation A (Fin d → ℂ)) := by
  -- `A(ℂ)` is a compact commutative topological group with a holomorphic chart at `0` in which
  -- addition is analytic, so it has an exponential map `e` (`exists_lie_exponential`). It remains
  -- to see that `e` is onto, holomorphic and immersive; translations carry the last two from `0` to
  -- any point.
  obtain ⟨φ, ψ, hφ0, hψφ, hφψ, hψ_hol, h_chart⟩ := exists_holomorphic_chart hd 0
  -- Addition and negation are morphisms of schemes, hence continuous on complex points.
  have h_group : IsTopologicalAddGroup (ComplexPoint A) := isTopologicalAddGroup_complexPoint hN
  have h_compact : CompactSpace (ComplexPoint A) := hN.compactSpace_complexPoint
  have hψ_cont : ContinuousAt ψ 0 := continuousAt_complexPoint_iff.mpr fun U f hf hU ↦
    (hψ_hol hf hU).imp_right AnalyticAt.continuousAt
  have hψ0 : ψ 0 = 0 := by simpa [hφ0] using hψφ.self_of_nhds.left
  -- Addition read in the chart is analytic: it is a holomorphic family of points through `0`.
  have h_fst : HolomorphicAt (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦ (ψ p.1).left) 0 :=
    .comp (φ := fun w ↦ (ψ w).left) hψ_hol analyticAt_fst
  have h_snd : HolomorphicAt (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦ (ψ p.2).left) 0 :=
    .comp (φ := fun w ↦ (ψ w).left) hψ_hol analyticAt_snd
  have h_add_hol : HolomorphicAt (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦ (ψ p.1 + ψ p.2).left) 0 :=
    (HasGermAt.lift hN h_fst h_snd).comp_hom _
  have h_add : AnalyticAt ℂ (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦ φ (ψ p.1 + ψ p.2)) 0 :=
    (h_chart (γ := fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦ ψ p.1 + ψ p.2) (w := 0) (by simp [hψ0])
      h_add_hol).left
  -- `e` has a lattice as kernel and image of finite index, `φ ∘ e` is analytic at `0` with
  -- derivative `1`, and homomorphisms differentiable in the chart factor linearly through `e`.
  obtain ⟨e, h_lat, he_near, he_an, he_deriv, h_index, h_univ⟩ :=
    exists_lie_exponential hφ0 (hψφ.mono fun _ ↦ And.left) (hψφ.mono fun _ ↦ And.right) hφψ hψ_cont
      h_add
  -- Near `0` we have `e = ψ ∘ (φ ∘ e)`, so `e` is a holomorphic family of points at `0`.
  have he_hol : HolomorphicAt (fun z ↦ (e z).left) 0 :=
    holomorphicAt_of_analyticAt_chart_comp hφ0 hψ_hol e he_an he_near
  -- So is its shift `w ↦ e (-z + w)` at `z`.
  have h_shift (z : Fin d → ℂ) : HolomorphicAt (fun w ↦ (e (-z + w)).left) z := by
    have he_hol_at : HolomorphicAt (fun w ↦ (e w).left) (-z + z) := by simpa using he_hol
    exact .comp (φ := fun w ↦ (e w).left) he_hol_at (by fun_prop)
  refine ⟨{ expMap := e
            lattice := e.ker.toIntSubmodule
            surjective := fun y ↦ ?_
            eq_zero_iff := fun z ↦ by tauto
            immersive := fun z ↦ ⟨?_, fun v hv ↦ ?_⟩
            universal := fun γ hγ ↦ ?_ }⟩
  · -- Onto: multiplication by the index `m ≠ 0` of the image is surjective, so `y` lifts to a
    -- complex point `x`; then `y = m • x` lies in the image.
    obtain ⟨x, hx⟩ :
        ∃ x : Spec (CommRingCat.of ℂ) ⟶ A.left, x ≫ (e.range.index • 𝟙 A).left = y.left :=
      exists_point_over _ ((IsAbelianScheme.nsmul_surjective _ h_index.index_ne_zero).surj _)
    have hxy : homMk x (by simp [← y.w, ← hx]) ≫ (e.range.index • 𝟙 A) = y := OverMorphism.ext hx
    rw [← hxy]
    simpa [comp_nsmul] using e.range.nsmul_index_mem _
  · -- Holomorphic at `z`: `e w` is the translate of `e (-z + w)` by `e z`.
    simpa [← comp_left, comp_add] using (h_shift z).comp_hom (translation (e z)).left
  · -- Immersive at `z`: the translate `w ↦ e (-z + w)` by `-e z` is still constant to first order
    -- in the direction `v`, and in the chart it has derivative `1` at `z`.
    have h_still : IsFirstOrderConst (fun w ↦ (e (-z + w)).left) z v := by
      simpa [IsFirstOrderConst, ← comp_left, add_comm, comp_add] using
        hv.comp_hom (translation (-e z)).left
    have he_deriv_at : HasFDerivAt (φ ∘ e) (.id ℂ _) (-z + z) := by simpa using he_deriv
    have h_deriv : HasFDerivAt (φ ∘ fun w ↦ e (-z + w)) (.id ℂ _) z :=
      (hasFDerivAt_comp_add_left (f := φ ∘ e) _).mpr he_deriv_at
    have h_zero : fderiv ℂ (φ ∘ fun w ↦ e (-z + w)) z v = 0 :=
      (h_chart (γ := fun w ↦ e (-z + w)) (w := z) (by simp) (h_shift z)).right v h_still
    rw [h_deriv.fderiv] at h_zero
    simpa using h_zero
  · -- Universal: a homomorphism holomorphic at `0` is continuous, and differentiable in the chart.
    exact h_univ γ (continuousAt_complexPoint_iff.mpr fun U f hf hU ↦
      (hγ hf hU).imp_right AnalyticAt.continuousAt) (h_chart γ.map_zero hγ).left.differentiableAt

end New
