import Lib.DiscreteSeries.Haar.GramCoordinates

/-!
# The polar formula for the Gram map on bases

Let `J` be a hermitian involution of size `r` and `G = U(J)`, with the compact dual Haar measure
`dγ` (`New.haarU`). A basis `Y` whose Gram matrix `T = Yᴴ J Y` is near `J` is `γ σ(T)`, with `γ` in
`G` and `σ` a local section of the Gram map (`New.exists_isGramSection`).

* `New.IsGramSection.lintegral_eq`: the polar formula `dY = (vol U(r) / 2 ^ r) dγ dT`, where
  `vol U(r)` is `New.volU r`. The Jacobian is computed on tangent vectors: `Yᴴ J dY` has hermitian
  part `dT / 2`, and for fixed `T` it is `σᴴ (J γ⁻¹ dγ) σ`, which is skew-hermitian. The constant
  does not depend on the signature of `J`.

Notions from other files:
* `IsHermitianInvolution J`: the complex matrix `J` is hermitian and `J * J = 1`;
* `U J`: the group of `g` with `gᴴ * J * g = J`, where `volume` is the Haar measure `New.haarU J`,
  normalized so that it has mass `1` for `J = 1`;
* `gramCoords J Y`: the real coordinates of the hermitian matrix `Yᴴ * J * Y`;
* `cayleyChart J`: the Cayley parametrization of almost all of `U J` by real matrices `y` with
  `(cayleyDenom J y).det ≠ 0`; the density of the Haar measure there is `cayleyDensity J y` divided
  by `volU r`;
* `logDerivU (cayleyChart J) y`: the linear map `v ↦ γᴴ J dγ(v)`, with `γ = cayleyChart J y`;
* `skewAddHerm`: the linear equivalence from pairs of real matrices to complex matrices; its inverse
  sends `X` to the coordinates of the hermitian matrix `X + Xᴴ` and of the skew-hermitian matrix
  `(X - Xᴴ) / 2`.

## Relation to the literature

Known result: the invariant measure `dY / dT` on tuples of vectors with a given Gram matrix. Source:
C. L. Siegel, Über die analytische Theorie der quadratischen Formen, Ann. of Math. 36 (1935).
-/

noncomputable section

namespace New

open Matrix MeasureTheory Measure Complex Fintype ENNReal Norms.L2Operator Filter Topology

variable {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
  {J : Matrix ι ι ℂ} [IsHermitianInvolution J]

/-- The Haar measure of `U J` is invariant under right translations. -/
instance : (volume (α := U J)).IsMulRightInvariant :=
  ⟨fun g ↦ (measurePreserving_haarU 1 g 1 (.mulRight g) (by simp [mem_U.1 g.2]) (by simp)).map_eq⟩

theorem IsHermitianInvolution.norm_det : ‖J.det‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_
  rw [← norm_pow, sq, ← det_mul, IsHermitianInvolution.mul_self, det_one, norm_one]

/-- Left multiplication by an element of the unitary group `U J` preserves Lebesgue measure on
tuples of vectors. -/
theorem measurePreserving_U_mul (g : U J) :
    MeasurePreserving fun y : Matrix ι n ℂ ↦ (g : Matrix ι ι ℂ) * y := by
  refine ⟨by fun_prop, ext_of_lintegral _ fun K hK ↦ ?_⟩
  rw [lintegral_map hK (by fun_prop), lintegral_eq_det_mul_comp_mul_mul (P := (g : Matrix ι ι ℂ))
    (Q := 1) (norm_pos_iff.1 (by simp)) (by simp) hK]
  simp [← ofReal_norm]

omit [Fintype n] [IsHermitianInvolution J] in
theorem gramCoords_U_mul (g : U J) (Y : Matrix ι n ℂ) :
    gramCoords J ((g : Matrix ι ι ℂ) * Y) = gramCoords J Y := by
  rw [gramCoords, U.gram_invariant, gramCoords]

/-- Almost every element `g` of `U(J)`, for its Haar measure, has no eigenvalue `-1`. -/
theorem ae_isUnit_add_one : ∀ᵐ g : U J, IsUnit ((g : Matrix ι ι ℂ) + 1) := by
  have h_chart : ∀ᵐ g : U J, ∃ y, (cayleyDenom J y).det ≠ 0 ∧ cayleyChart J y = g :=
    measurableEmbedding_cayleyChart.ae_map_iff.2 (.of_forall fun ⟨y, hy⟩ ↦ ⟨y, hy, rfl⟩)
  filter_upwards [h_chart]
  rintro _ ⟨y, hy, rfl⟩
  have h_eq : (cayleyChart J y : Matrix ι ι ℂ) + 1 = (2 : ℂ) • (cayleyDenom J y)⁻¹ :=
    sub_add_cancel _ _
  simp [h_eq, isUnit_iff_isUnit_det, hy]

variable (J) in
/-- The map `σ` is a differentiable section of the Gram map over the open set `V` of real
coordinates `t` of hermitian matrices, and its values there are bases. -/
structure IsGramSection (V : Set (Matrix ι ι ℝ)) (σ : Matrix ι ι ℝ → Matrix ι ι ℂ) : Prop where
  /-- The set `V` is open. -/
  isOpen : IsOpen V
  /-- The map `σ` is measurable on the whole space. -/
  measurable : Measurable σ
  /-- The map `σ` is differentiable on `V`. -/
  differentiableAt {t : Matrix ι ι ℝ} : t ∈ V → DifferentiableAt ℝ σ t
  /-- For `t` in `V` the Gram matrix of `σ t` has the coordinates `t`. -/
  gramCoords_eq {t : Matrix ι ι ℝ} : t ∈ V → gramCoords J (σ t) = t
  /-- For `t` in `V` the matrix `σ t` is invertible. -/
  isUnit {t : Matrix ι ι ℝ} : t ∈ V → IsUnit (σ t)

variable (J) in
/-- There are an open set `V` of coordinates of Gram matrices, containing those of `1ᴴ * J * 1 = J`,
and a differentiable section of the Gram map over `V` through the standard basis `1`. -/
theorem exists_isGramSection :
    ∃ (V : Set (Matrix ι ι ℝ)) (σ : Matrix ι ι ℝ → Matrix ι ι ℂ),
      IsGramSection J V σ ∧
      gramCoords J (1 : Matrix ι ι ℂ) ∈ V ∧
      σ (gramCoords J (1 : Matrix ι ι ℂ)) = 1 := by
  -- On the slice `β x = 1 + J X / 2`, `X = hermOfReal x`, the Gram map has derivative the identity
  -- at `0`. The inverse function theorem inverts it near `0`.
  obtain ⟨N, hN⟩ : ∃ N : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℂ,
      ∀ x : Matrix ι ι ℝ, N x = J * ((2⁻¹ : ℂ) • hermOfReal x) :=
    ⟨(LinearMap.mulLeft ℝ J ∘ₗ ((2⁻¹ : ℂ) • -I • skewOfReal)).toContinuousLinearMap, fun _ ↦ rfl⟩
  let β (x : Matrix ι ι ℝ) : Matrix ι ι ℂ := 1 + N x
  have hβ : ContDiff ℝ 1 β := contDiff_const.add N.contDiff
  have hβ_zero : β 0 = 1 := by simp [β]
  have h_smooth : ContDiffAt ℝ 1 (fun x ↦ gramCoords J (β x)) 0 :=
    ((contDiff_gramCoords J).comp hβ).contDiffAt
  have h_deriv : HasFDerivAt (fun x ↦ gramCoords J (β x))
      (ContinuousLinearEquiv.refl ℝ (Matrix ι ι ℝ) : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ) 0 := by
    obtain ⟨D, hD, hD_apply⟩ :=
      hasFDerivAt_gramCoords J (σ := β) (t := 0) (N.hasFDerivAt.const_add 1)
    refine hD.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
    have h_sum : (β 0)ᴴ * J * N v + (N v)ᴴ * J * β 0 = hermOfReal v := by
      have h_left : (β 0)ᴴ * J * N v = (2⁻¹ : ℂ) • hermOfReal v := by
        simp [hN, hβ_zero, ← Matrix.mul_assoc, IsHermitianInvolution.mul_self]
      have h_right : (N v)ᴴ * J * β 0 = (2⁻¹ : ℂ) • hermOfReal v := by
        simp [hN, hβ_zero, Matrix.mul_assoc _ J J, IsHermitianInvolution.mul_self,
          IsHermitianInvolution.isHermitian.eq, conjTranspose_smul]
      rw [h_left, h_right]
      module
    rw [hD_apply, h_sum, skewCoords_I_smul_hermOfReal]
    rfl
  let σ (t : Matrix ι ι ℝ) : Matrix ι ι ℂ := β (h_smooth.localInverse h_deriv one_ne_zero t)
  have hσ_smooth : ContDiffAt ℝ 1 σ (gramCoords J (β 0)) :=
    hβ.contDiffAt.comp _ (h_smooth.to_localInverse h_deriv one_ne_zero)
  have hσ_base : σ (gramCoords J (β 0)) = 1 :=
    (congrArg β (h_smooth.localInverse_apply_image h_deriv one_ne_zero)).trans hβ_zero
  have h_near : ∀ᶠ t in 𝓝 (gramCoords J (β 0)),
      DifferentiableAt ℝ σ t ∧ gramCoords J (σ t) = t ∧ IsUnit (σ t) := by
    filter_upwards [hσ_smooth.eventually (by simp),
      (h_smooth.hasStrictFDerivAt' h_deriv one_ne_zero).eventually_right_inverse,
      hσ_smooth.continuousAt.eventually_mem (Units.isOpen.mem_nhds (by simp [hσ_base]))]
      with t h_diff h_inv h_unit
    exact ⟨h_diff.differentiableAt one_ne_zero, h_inv, h_unit⟩
  rw [hβ_zero] at h_near hσ_base
  obtain ⟨V, hV, hV_open, h_base⟩ := eventually_nhds_iff.1 h_near
  -- Outside `V` put `σ = 1`, to make it measurable.
  classical
  choose h_diff h_gram h_unit using hV
  have h_eq : Set.EqOn (V.piecewise σ 1) σ V := V.piecewise_eqOn σ 1
  exact ⟨V, V.piecewise σ 1,
    { isOpen := hV_open
      measurable := ContinuousOn.measurable_piecewise
        (fun t ht ↦ (h_diff t ht).continuousAt.continuousWithinAt) continuousOn_const
        hV_open.measurableSet
      differentiableAt ht :=
        (h_diff _ ht).congr_of_eventuallyEq (h_eq.eventuallyEq_of_mem (hV_open.mem_nhds ht))
      gramCoords_eq ht := by rw [h_eq ht, h_gram _ ht]
      isUnit ht := by simpa only [h_eq ht] using h_unit _ ht },
    h_base, (h_eq h_base).trans hσ_base⟩

namespace IsGramSection

variable {V S : Set (Matrix ι ι ℝ)} {σ : Matrix ι ι ℝ → Matrix ι ι ℂ}

omit [IsHermitianInvolution J] in
/-- The identity `gramCoords J (σ t) = t` of a section, differentiated at `t ∈ V` in the
direction `v`. -/
theorem skewCoords_fderiv_gram (hσ : IsGramSection J V σ) {t : Matrix ι ι ℝ} (ht : t ∈ V)
    (v : Matrix ι ι ℝ) :
    skewCoords (I • ((σ t)ᴴ * J * fderiv ℝ σ t v + (fderiv ℝ σ t v)ᴴ * J * σ t)) = v := by
  obtain ⟨T, hT, hT_apply⟩ := hasFDerivAt_gramCoords J (hσ.differentiableAt ht).hasFDerivAt
  have hT_id : T = .id ℝ (Matrix ι ι ℝ) :=
    hT.unique ((hasFDerivAt_id t).congr_of_eventuallyEq
      (eventually_of_mem (hσ.isOpen.mem_nhds ht) fun _ ↦ hσ.gramCoords_eq))
  rw [← hT_apply, hT_id, ContinuousLinearMap.id_apply]

omit [IsHermitianInvolution J] in
/-- A section of the Gram map over `V` restricts to a section over each open subset of `V`. -/
theorem mono (hσ : IsGramSection J V σ) (hS : IsOpen S) (hSV : S ⊆ V) : IsGramSection J S σ :=
  ⟨hS, hσ.measurable, fun ht ↦ hσ.differentiableAt (hSV ht), fun ht ↦ hσ.gramCoords_eq (hSV ht),
    fun ht ↦ hσ.isUnit (hSV ht)⟩

omit [IsHermitianInvolution J] in
/-- Multiplying the values of a linear map `D` on the left by `P` multiplies its Jacobian, read in
the coordinates `skewAddHerm.symm`, by `‖det P‖ ^ (2 r)`, where `r` is the size of the matrices. -/
theorem abs_det_skewAddHerm_mulLeft_comp (P : Matrix ι ι ℂ)
    (D : Matrix ι ι ℝ × Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℂ) :
    |(skewAddHerm.symm.toLinearMap ∘ₗ LinearMap.mulLeft ℝ P ∘ₗ D).det| =
      ‖P.det‖ ^ (2 * card ι) * |(skewAddHerm.symm.toLinearMap ∘ₗ D).det| := by
  let L : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ := mulRightLinearMap ι ℝ 1 ∘ₗ mulLeftLinearMap ι ℝ P
  have h_factor : skewAddHerm.symm.toLinearMap ∘ₗ LinearMap.mulLeft ℝ P ∘ₗ D =
      (skewAddHerm.symm.toLinearMap ∘ₗ L ∘ₗ skewAddHerm.toLinearMap) *
        (skewAddHerm.symm.toLinearMap ∘ₗ D) :=
    LinearMap.ext fun p ↦ by simp [L]
  have h_conj : (skewAddHerm.symm.toLinearMap ∘ₗ L ∘ₗ skewAddHerm.toLinearMap).det = L.det :=
    LinearMap.det_conj L skewAddHerm.symm
  rw [h_factor, map_mul, h_conj, det_mulLeft_mulRight_real]
  simp

/-- Let `σ` be a differentiable section of the Gram map over the open set `V` (`IsGramSection`), and
let `γ = cayleyChart J`, with `cayleyDenom J y` invertible. At `t ∈ V`, let
`T(t', s) = σᴴ (γᴴ J dγ_y s) σ + σᴴ J dσ_t t'`. In coordinates via `skewAddHerm.symm`
(`Z ↦ (Z + Zᴴ, (Z - Zᴴ)/2)`), `|det T| = ‖det σ t‖ ^ (2 card ι) · cayleyDensity J y`. -/
theorem abs_det_skewAddHerm_symm_comp (hσ : IsGramSection J V σ) {t y : Matrix ι ι ℝ}
    (ht : t ∈ V) (hy : (cayleyDenom J y).det ≠ 0)
    {T : Matrix ι ι ℝ × Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℂ}
    (hT : ∀ p : Matrix ι ι ℝ × Matrix ι ι ℝ, T p =
      (σ t)ᴴ * logDerivU (cayleyChart J) y p.2 * σ t + (σ t)ᴴ * J * fderiv ℝ σ t p.1) :
    |(skewAddHerm.symm.toLinearMap ∘ₗ T).det| =
      ‖(σ t).det‖ ^ (2 * card ι) * cayleyDensity J y := by
  -- The first summand is skew-hermitian and the hermitian part of the second is `dt / 2`.
  obtain ⟨h_diff, h_density⟩ := abs_det_logDerivU_cayleyChart hy
  let W (v : Matrix ι ι ℝ) : Matrix ι ι ℂ := (σ t)ᴴ * logDerivU (cayleyChart J) y v * σ t
  have h_skew (v : Matrix ι ι ℝ) : (W v)ᴴ = -W v := by
    simp [W, conjTranspose_logDerivU h_diff, Matrix.mul_assoc]
  have h_herm (p : Matrix ι ι ℝ × Matrix ι ι ℝ) : (skewAddHerm.symm (T p)).1 = p.1 := by
    have h_sum : T p + (T p)ᴴ =
        (σ t)ᴴ * J * fderiv ℝ σ t p.1 + (fderiv ℝ σ t p.1)ᴴ * J * σ t := by
      rw [hT, conjTranspose_add, h_skew]
      simp only [W, conjTranspose_mul, conjTranspose_conjTranspose,
        IsHermitianInvolution.isHermitian.eq, Matrix.mul_assoc]
      abel
    rw [skewAddHerm_symm_apply, h_sum]
    exact hσ.skewCoords_fderiv_gram ht p.1
  let B : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ := skewCoords ∘ₗ LinearMap.mulLeftRight ℝ ((σ t)ᴴ, σ t) ∘ₗ
    skewOfReal ∘ₗ skewCoords ∘ₗ logDerivU (cayleyChart J) y
  have h_second (v : Matrix ι ι ℝ) : (skewAddHerm.symm (T (0, v))).2 = B v := by
    have h_half : (2⁻¹ : ℂ) • (T (0, v) - (T (0, v))ᴴ) = W v := by
      simp [hT, h_skew, ← two_smul ℂ, smul_smul, W]
    simp [B, W, skewAddHerm_symm_apply, h_half,
      skewOfReal_skewCoords (conjTranspose_logDerivU h_diff v)]
  rw [Haar.det_eq_mul_of_fst_eq_of_snd_eq LinearMap.id B h_herm h_second, LinearMap.det_id,
    one_mul, ← h_density]
  exact abs_det_skew_congruence (.refl ℝ (Matrix ι ι ℝ)) (σ t)
    (skewCoords ∘ₗ logDerivU (cayleyChart J) y)

/-- Let `J` be a hermitian involution, `σ` a section of the Gram map over `V`, `t ∈ V`, and `y` real
with `det (cayleyDenom J y) ≠ 0`. Then the map `(t, y) ↦ γ(y) σ(t)`, with `γ = cayleyChart J` the
Cayley chart, is differentiable at `(t, y)`. The absolute value of its Jacobian is the density
`New.cayleyDensity J y`, which is the absolute Jacobian of `J γ⁻¹ dγ`. The Jacobian is read in the
real coordinates `skewAddHerm.symm`, which send a complex matrix `Z` to the coordinates of the
hermitian matrix `Z + Zᴴ` and of the skew-hermitian matrix `(Z - Zᴴ) / 2`. -/
theorem exists_hasFDerivAt_cayleyChart_mul (hσ : IsGramSection J V σ) {t y : Matrix ι ι ℝ}
    (ht : t ∈ V) (hy : (cayleyDenom J y).det ≠ 0) :
    ∃ D : (Matrix ι ι ℝ × Matrix ι ι ℝ) →L[ℝ] Matrix ι ι ℂ,
      HasFDerivAt
        (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ (cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1) D
        (t, y) ∧
      |(skewAddHerm.symm.toLinearMap ∘ₗ D.toLinearMap).det| = cayleyDensity J y := by
  -- Multiplication by `Yᴴ J`, with `Y = γ(y) σ(t)`, has the Jacobian `‖det σ‖ ^ (2 r)`, which is
  -- also the factor in the Jacobian of `Yᴴ J dY`.
  let g : Matrix ι ι ℂ := cayleyChart J y
  have h_fst := (hσ.differentiableAt ht).hasFDerivAt.comp (f := Prod.fst) (t, y) hasFDerivAt_fst
  have h_snd := (differentiableAtU_cayleyChart hy).hasFDerivAt.comp (f := Prod.snd) (t, y)
    hasFDerivAt_snd
  obtain ⟨D, hD, hD_apply⟩ : ∃ D, HasFDerivAt
      (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ (cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1) D (t, y) ∧
      ∀ p, D p = g * fderiv ℝ σ t p.1 +
        fderiv ℝ (fun x ↦ (cayleyChart J x : Matrix ι ι ℂ)) y p.2 * σ t :=
    ⟨_, h_snd.mul' h_fst, fun _ ↦ rfl⟩
  refine ⟨D, hD, ?_⟩
  set P : Matrix ι ι ℂ := (g * σ t)ᴴ * J
  have h_tangent (p : Matrix ι ι ℝ × Matrix ι ι ℝ) : P * D p =
      (σ t)ᴴ * logDerivU (cayleyChart J) y p.2 * σ t + (σ t)ᴴ * J * fderiv ℝ σ t p.1 := by
    rw [hD_apply, Matrix.mul_add, U.gram_invariant, add_comm]
    -- By definition the logarithmic derivative is v ↦ γᴴ * J * dγ v.
    simp [P, g, logDerivU, conjTranspose_mul, Matrix.mul_assoc]
  have h_block : |(skewAddHerm.symm.toLinearMap ∘ₗ LinearMap.mulLeft ℝ P ∘ₗ D.toLinearMap).det| =
      ‖(σ t).det‖ ^ (2 * card ι) * cayleyDensity J y :=
    hσ.abs_det_skewAddHerm_symm_comp ht hy h_tangent
  rw [abs_det_skewAddHerm_mulLeft_comp,
    show ‖P.det‖ = ‖(σ t).det‖ by simp [P, g, IsHermitianInvolution.norm_det]] at h_block
  have h_det : (σ t).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (hσ.isUnit ht)).ne_zero
  exact mul_left_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 h_det)) h_block

/-- Let `J` be a hermitian involution, and let `σ` be a differentiable section over the open set `V`
of the Gram map `gramCoords J` (the real coordinates of `Yᴴ J Y`), whose values `σ t` are
invertible. Then every complex matrix `Y` with `t = gramCoords J Y` in `V` is `γ σ(t)` for some `γ`
in `U(J)`. -/
theorem exists_mul_eq (hσ : IsGramSection J V σ) {Y : Matrix ι ι ℂ} (hY : gramCoords J Y ∈ V) :
    ∃ γ : U J, (γ : Matrix ι ι ℂ) * σ (gramCoords J Y) = Y := by
  set Z : Matrix ι ι ℂ := σ (gramCoords J Y)
  have h_unit : IsUnit Z.det := (isUnit_iff_isUnit_det Z).1 (hσ.isUnit hY)
  have h_gram : Yᴴ * J * Y = Zᴴ * J * Z := by
    simp only [← hermOfReal_gramCoords IsHermitianInvolution.isHermitian, Z, hσ.gramCoords_eq hY]
  have h_mem : (Y * Z⁻¹)ᴴ * J * (Y * Z⁻¹) = J :=
    calc (Y * Z⁻¹)ᴴ * J * (Y * Z⁻¹) = Z⁻¹ᴴ * (Yᴴ * J * Y) * Z⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Z * Z⁻¹)ᴴ * J * (Z * Z⁻¹) := by simp only [h_gram, conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by simp [mul_nonsing_inv Z h_unit]
  exact ⟨U.of IsHermitianInvolution.isUnit _ h_mem, nonsing_inv_mul_cancel_right Z Y h_unit⟩

/-- Let `J` be a hermitian involution (`Jᴴ = J`, `J² = 1`). Let `σ` be a section of the Gram map
`gramCoords J` over the open set `V`: a differentiable map with invertible values, where
`gramCoords J Y` is the real coordinates, in the sense of `hermOfReal`, of `Yᴴ J Y`. For
Lebesgue-almost every complex matrix `Y` with `t = gramCoords J Y` in `V`, written `Y = γ σ(t)` with
`γ` in `U(J)`, the matrix `Y + σ(t) = (γ + 1) σ(t)` is invertible; that is, `γ` has no eigenvalue
`-1`. -/
theorem ae_isUnit_add (hσ : IsGramSection J V σ) :
    ∀ᵐ Y : Matrix ι ι ℂ, gramCoords J Y ∈ V → IsUnit (Y + σ (gramCoords J Y)) := by
  -- For each `Y` the claim holds at `g Y` for almost every `g` in `U(J)`. By Fubini's theorem it
  -- holds at almost every `g Y` for some `g`, and `g` preserves Lebesgue measure.
  let B : Set (Matrix ι ι ℂ) := {Y | gramCoords J Y ∈ V → IsUnit (Y + σ (gramCoords J Y))}
  have h_gram : Measurable (gramCoords J) := (continuous_gramCoords (n := ι) J).measurable
  have hB : MeasurableSet B := (h_gram hσ.isOpen.measurableSet).imp
    ((measurable_id.add (hσ.measurable.comp h_gram)) Units.isOpen.measurableSet)
  have h_orbit (Y : Matrix ι ι ℂ) : ∀ᵐ g : U J, (g : Matrix ι ι ℂ) * Y ∈ B := by
    by_cases hY : gramCoords J Y ∈ V
    · obtain ⟨γ, hγ⟩ := hσ.exists_mul_eq hY
      have h_translate : ∀ᵐ g : U J, IsUnit (((g * γ : U J) : Matrix ι ι ℂ) + 1) :=
        (measurePreserving_mul_right volume γ).quasiMeasurePreserving.ae ae_isUnit_add_one
      filter_upwards [h_translate] with g hg _
      have h_factor : (g : Matrix ι ι ℂ) * Y + σ (gramCoords J Y) =
          (((g * γ : U J) : Matrix ι ι ℂ) + 1) * σ (gramCoords J Y) := by
        simp [Matrix.add_mul, Matrix.mul_assoc, hγ]
      rw [gramCoords_U_mul, h_factor]
      exact hg.mul (hσ.isUnit hY)
    · simp [B, gramCoords_U_mul, hY]
  have h_comm : ∀ᵐ g : U J, ∀ᵐ Y : Matrix ι ι ℂ, (g : Matrix ι ι ℂ) * Y ∈ B :=
    (ae_ae_comm (p := fun Y (g : U J) ↦ (g : Matrix ι ι ℂ) * Y ∈ B)
      (((isClosedEmbedding_U.measurable.comp measurable_snd).mul measurable_fst) hB)).1
        (.of_forall h_orbit)
  obtain ⟨g, hg⟩ := h_comm.exists
  rw [← (measurePreserving_U_mul g).map_eq]
  exact (ae_map_iff (measurePreserving_U_mul g).measurable.aemeasurable hB).2 hg

/-- On `V` times the domain of the Cayley chart the map `(t, y) ↦ γ(y) σ(t)`, with `γ` the Cayley
chart, is injective. -/
theorem injOn_cayleyChart_mul (hσ : IsGramSection J V σ) :
    (V ×ˢ {y : Matrix ι ι ℝ | (cayleyDenom J y).det ≠ 0}).InjOn
      fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ (cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1 := by
  rintro ⟨t, y⟩ ⟨ht, hy⟩ ⟨t', y'⟩ ⟨ht', hy'⟩ h_image
  obtain rfl : t = t' := by
    simpa only [gramCoords_U_mul, hσ.gramCoords_eq ht, hσ.gramCoords_eq ht'] using
      congrArg (gramCoords J) h_image
  exact Prod.ext rfl (cayleyChart_injOn hy hy'
    (Subtype.ext (Units.ext ((hσ.isUnit ht).mul_right_cancel h_image))))

/-- Up to a null set, the matrices `Y` with `gramCoords J Y` in `V` are the products `γ(y) σ(t)`
with `t` in `V` and `y` in the domain of the Cayley chart `γ`. -/
theorem preimage_gramCoords_ae_eq_image (hσ : IsGramSection J V σ) :
    gramCoords J ⁻¹' V =ᵐ[volume]
      (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ (cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1) ''
        (V ×ˢ {y : Matrix ι ι ℝ | (cayleyDenom J y).det ≠ 0}) := by
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hσ.ae_isUnit_add] with Y h_unit
  refine ⟨fun hY ↦ ?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := hσ.exists_mul_eq hY
    have hγ_unit : IsUnit ((γ : Matrix ι ι ℂ) + 1) :=
      isUnit_of_mul_isUnit_left (y := σ (gramCoords J Y))
        (by simpa only [Matrix.add_mul, hγ, Matrix.one_mul] using h_unit hY)
    obtain ⟨h_dom, h_chart⟩ := cayleyChart_cayleyChartInv γ hγ_unit
    exact ⟨(gramCoords J Y, cayleyChartInv γ), ⟨hY, h_dom⟩, by simp only [h_chart, hγ]⟩
  · rintro ⟨⟨t, y⟩, ⟨ht, -⟩, rfl⟩
    simpa only [Set.mem_preimage, gramCoords_U_mul, hσ.gramCoords_eq ht] using ht

/-- The polar formula in the Cayley chart. Let `J` be a hermitian involution, `gramCoords J Y` the
real coordinates of the Gram matrix `Yᴴ J Y`, and `σ` a section of the Gram map over `V`. For
measurable `K ≥ 0`, the integral of `K` over all of `gramCoords J ⁻¹' V` equals `2 ^ (-r)`, with
`r = card ι`, times the integral of `cayleyDensity J y * K (cayleyChart J y * σ t)` over `t ∈ V` and
`y` with `det (cayleyDenom J y) ≠ 0`. Here `cayleyDensity J y` is the Jacobian of the Cayley chart
`γ = cayleyChart J`. -/
theorem lintegral_eq_cayleyChart_mul (hσ : IsGramSection J V σ) {K : Matrix ι ι ℂ → ℝ≥0∞}
    (hK : Measurable K) :
    ∫⁻ Y : Matrix ι ι ℂ in gramCoords J ⁻¹' V, K Y =
      (2 ^ card ι)⁻¹ * ∫⁻ p : Matrix ι ι ℝ × Matrix ι ι ℝ in
          V ×ˢ {y : Matrix ι ι ℝ | (cayleyDenom J y).det ≠ 0},
        ENNReal.ofReal (cayleyDensity J p.2) * K ((cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1) := by
  -- The map `(t, y) ↦ γ(y) σ(t)` is injective on `A` and its image is the domain of integration up
  -- to a null set. Change variables along it, in the coordinates `skewAddHerm.symm`.
  set A : Set (Matrix ι ι ℝ × Matrix ι ι ℝ) := V ×ˢ {y | (cayleyDenom J y).det ≠ 0}
  let Φ (p : Matrix ι ι ℝ × Matrix ι ι ℝ) : Matrix ι ι ℂ :=
    (cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1
  have hA : MeasurableSet A :=
    (hσ.isOpen.prod continuous_cayleyDenom.matrix_det.isOpen_support).measurableSet
  have h_inj : A.InjOn Φ := hσ.injOn_cayleyChart_mul
  have h_jac : ∀ p ∈ A, ∃ D : (Matrix ι ι ℝ × Matrix ι ι ℝ) →L[ℝ] Matrix ι ι ℂ,
      HasFDerivAt Φ D p ∧
      |(skewAddHerm.symm.toLinearMap ∘ₗ D.toLinearMap).det| = cayleyDensity J p.2 :=
    fun _ ⟨ht, hy⟩ ↦ hσ.exists_hasFDerivAt_cayleyChart_mul ht hy
  choose! D hD hD_det using h_jac
  let e : Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℝ × Matrix ι ι ℝ := skewAddHerm.symm.toContinuousLinearEquiv
  calc ∫⁻ Y in gramCoords J ⁻¹' V, K Y = ∫⁻ Y in Φ '' A, K Y :=
        setLIntegral_congr hσ.preimage_gramCoords_ae_eq_image
    _ = (2 ^ card ι)⁻¹ * ∫⁻ p in (e ∘ Φ) '' A, K (e.symm p) := by
      have h_meas : MeasurableSet (Φ '' A) := hA.image_of_continuousOn_injOn
        (fun p hp ↦ (hD p hp).continuousAt.continuousWithinAt) h_inj
      rw [← lintegral_indicator h_meas, lintegral_eq_comp_skewAddHerm (hK.indicator h_meas),
        Set.image_comp, e.image_eq_preimage_symm,
        ← lintegral_indicator (e.symm.continuous.measurable h_meas)]
      simp only [← Function.comp_def K, Set.indicator_comp_right]
      rfl
    _ = (2 ^ card ι)⁻¹ * ∫⁻ p in A, ENNReal.ofReal (cayleyDensity J p.2) * K (Φ p) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA (fun p hp ↦
        (e.hasFDerivAt.comp p (hD p hp)).hasFDerivWithinAt) (e.injective.comp_injOn h_inj)]
      congr 1
      refine setLIntegral_congr_fun hA fun p hp ↦ ?_
      rw [← hD_det p hp, Function.comp_apply, e.symm_apply_apply]
      -- The two determinants are those of one linear map, once as a continuous map.
      rfl

/-- The polar formula. Let `J` be a hermitian involution, let `σ` be a differentiable section with
invertible values over the open set `V` of the Gram map `gramCoords J` (the real coordinates, in the
sense of `hermOfReal`, of `Yᴴ J Y`), and let `K ≥ 0` be measurable. On the matrices `Y = γ σ(t)`
with `γ` in `U(J)` and `t = gramCoords J Y` in `V`, Lebesgue measure is
`dY = (vol U(r) / 2 ^ r) dγ dt`, where `r` is the size of the matrices, `vol U(r) = New.volU r` and
`dγ` is the compact dual Haar measure `New.haarU J`, the `volume` of `U J`; that is,
`∫ Y in gramCoords J ⁻¹' V, K Y` equals that constant times `∫ t in V, ∫ γ, K (γ σ(t))`. -/
theorem lintegral_eq (hσ : IsGramSection J V σ) {K : Matrix ι ι ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ Y : Matrix ι ι ℂ in gramCoords J ⁻¹' V, K Y =
      ENNReal.ofReal (volU (card ι) / 2 ^ card ι) *
        ∫⁻ t : Matrix ι ι ℝ in V, ∫⁻ g : U J, K ((g : Matrix ι ι ℂ) * σ t) := by
  have hσ_meas : Measurable σ := hσ.measurable
  have h_const (x : ℝ) : (2 ^ card ι)⁻¹ * ENNReal.ofReal x =
      ENNReal.ofReal (volU (card ι) / 2 ^ card ι) * ENNReal.ofReal (x / volU (card ι)) := by
    have h_vol : 0 < volU (card ι) := volU_pos _
    rw [← ENNReal.ofReal_mul (by positivity),
      show volU (card ι) / 2 ^ card ι * (x / volU (card ι)) = x / 2 ^ card ι by field_simp,
      ENNReal.ofReal_div_of_pos (by positivity)]
    simp [ENNReal.div_eq_inv_mul]
  have h_inner (t : Matrix ι ι ℝ) :
      (2 ^ card ι)⁻¹ * ∫⁻ y : Matrix ι ι ℝ in {y | (cayleyDenom J y).det ≠ 0},
          ENNReal.ofReal (cayleyDensity J y) * K ((cayleyChart J y : Matrix ι ι ℂ) * σ t) =
        ENNReal.ofReal (volU (card ι) / 2 ^ card ι) *
          ∫⁻ g : U J, K ((g : Matrix ι ι ℂ) * σ t) := by
    simp (disch := finiteness) only [lintegral_eq_cayleyChart, ← lintegral_const_mul',
      ← mul_assoc, h_const]
  rw [hσ.lintegral_eq_cayleyChart_mul hK, volume_eq_prod, ← prod_restrict,
    lintegral_prod _ (by fun_prop)]
  simp (disch := finiteness) only [← lintegral_const_mul', h_inner]

end IsGramSection

end New

end
