import New.Spanning.Bessel.LargeFunction

/-!
# Schur's bound for a Bessel function and its derivatives

Let `l = 2λ` be a doubled Harish-Chandra parameter of large gap and `c_λ` the coefficient `dsCoeff`
on `U(diag ε)` of its discrete series; the same letter stands for its pullback
`New.HCParam.dsCoeffInFrame` to `G₁` by the frame. Let `deg` be the formal degree
`New.HCParam.formalDegree`. Write `(F * k) y = ∫ k a⁻¹ • F (y a)` and `e = deg · c_λ`; as
`e a⁻¹ = deg · conj (c_λ a)`, the condition `F * e = F` says that `F` is fixed by the idempotent of
the discrete series. Such a bounded function has right derivatives of all orders, and they are
convolutions with kernels of controlled norm. Schur's bound in `L²(𝖴 ∖ G₁)` follows, `𝖴` being the
unipotent group `besselU`.

Notions from other files:
* `l : New.HCParam ε` is twice a Harish-Chandra parameter; `HasLargeGap A` bounds its gaps below.
* `p : UnitarySignFrame 𝔰 ε` is a unitary frame in which the form of `G₁` is `diag ε`.
* `frameEquiv : G₁ ≃ₜ* U(diag ε)` is conjugation by the frame.
* `Bumps ε` are the smooth compactly supported functions on `U(diag ε)`; `smear f` sends a bump `β`
  to the convolution of the continuous function `f` with `β`.
* `bumpDeriv` is the action of matrices on bumps by differentiation, `adTwist g` precomposes it with
  conjugation by `g`, and `word w` applies the action of the matrix units of the word `w`.
* `New.IsBesselFunction rep F`: `F` is bounded, measurable and transforms by a character under
  `besselU` and by `rep` under `U(κ)`.
* `𝔰.r` is the number of indices `BesselIndex` of `G₁`, and `𝔰.n` is one more than the number of
  hyperbolic planes of the shape `𝔰`.
* `RealPlace.HasSchurBound F rep B C`: `F` has right derivatives of all orders that are again Bessel
  functions, those of order `s ≤ 2 n ^ 2` satisfying Schur's `L²` bound with `B ^ (2 s) C`.
* `besselQuotMeasure` is the measure on `G₁` that represents integration over `besselU ∖ G₁`.

## Relation to the literature

Known result: Smoothness and Schur's orthogonality relations for vectors of a discrete series
representation (Harish-Chandra).
-/

namespace New

open Matrix MeasureTheory ENNReal Norms.L2Operator Fintype CStarRing Set DiscreteSeries
  InnerProductSpace

variable {𝔰 : Shape} {I : Type} {ε : 𝔰.BesselIndex → ℤˣ} [Fintype I] [DecidableEq I]
  [p : UnitarySignFrame 𝔰 ε]

section Kernels

variable {l : HCParam ε} {A L : ℕ}

/-- Let `l = 2λ` be a doubled Harish-Chandra parameter of large gap, `c_λ = l.dsCoeffInFrame` the
coefficient on `G₁` of its discrete series and `deg = l.formalDegree` the formal degree. Then
`deg · c_λ` is bounded and measurable. -/
lemma isBoundedMeasurable_formalDegree_mul_dsCoeffInFrame (h_gap : l.HasLargeGap A) :
    IsBoundedMeasurable fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g := by
  refine .of_continuous ⟨_, fun g ↦ (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
    (norm_dsCoeff_le_one h_gap _) (norm_nonneg _))⟩
      (isIdempotentKernel_dsCoeffInFrame h_gap).continuous

/-- For the unitary frame `p`, each matrix unit `Matrix.single i j 1` conjugated by it,
`p.matrix⁻¹ * Matrix.single i j 1 * p.matrix`, has norm one. -/
lemma norm_frame_conj_single (i j : 𝔰.BesselIndex) :
    ‖p.matrix⁻¹.val * Matrix.single i j (1 : ℂ) * p.matrix.val‖ = 1 := by
  rw [Units.inv_eq_of_mul_eq_one_left (Unitary.star_mul_self_of_mem p.mem_unitary),
    norm_mul_mem_unitary _ p.mem_unitary,
    norm_mem_unitary_mul _ (Unitary.star_mem p.mem_unitary)]
  simp [l2_opNorm_single]

/-- Let `l = 2λ` be a doubled Harish-Chandra parameter with `l.HasLargeGap A` (gap `500 r³ + A`) and
entries bounded by `L`. Let `β` be a bump function whose convolution (`smear`) with `c_λ` is `c_λ`,
the generator of `U(𝔤) c_λ = l.DsModule`. Let `w` be a word of length `s` in the matrix units,
acting through `adTwist p.matrix⁻¹`. The convolution of `c_λ` with the derivative of `β` along `w`
is a vector `x` of step `s` of the filtration of `U(𝔤) c_λ`, with
`‖x‖ ≤ ((r + 1) ^ 4 (L + r + 1 + s)) ^ s`. Here `r = 𝔰.r` is the size of the matrices, and `‖x‖` is
the `L²` norm of `x` times the square root of the formal degree. -/
lemma exists_mem_filtration_smear_word (h_gap : l.HasLargeGap A)
    (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) {β : Bumps ε}
    (hβ : (smear l.dsCoeffSmooth.val) β = (l.dsGenerator : USign ε → ℂ))
    (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) :
    ∃ x ∈ l.dsAction.filtration ε l.dsGenerator w.length,
      ‖x‖ ≤ ((𝔰.r + 1) ^ 4 * (L + 𝔰.r + 1 + w.length)) ^ w.length ∧
      (smear l.dsCoeffSmooth.val) ((bumpDeriv.adTwist p.matrix⁻¹).word w β) =
        (x : USign ε → ℂ) := by
  -- A matrix of norm one moves step `s` of the filtration to step `s + 1` and multiplies the norm
  -- by at most `(r + 1) ^ 4 (L + r + 1 + s)`, since `L + r` bounds the lowest `K`-type.
  induction w with
  | nil => exact ⟨_, GlModule.self_mem_filtration, h_gap.norm_dsGenerator.le, hβ⟩
  | cons q w ih =>
    obtain ⟨x, x_mem, x_le, x_eq⟩ := ih
    -- Apply the conjugated matrix unit of the first letter of the word to `x`.
    let M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := p.matrix⁻¹.val * .single q.1 q.2 1 * p.matrix
    obtain ⟨step_mem,
      (step_le : ‖l.dsAction M x‖ ≤ (𝔰.r + 1) ^ 4 * ((L + 𝔰.r : ℕ) + 1 + w.length) * ‖M‖ * ‖x‖)⟩ :=
      (isKHighest_dsGenerator h_gap).norm_apply_le_of_mem_filtration h_gap.isUnitaryCasimirGe
        (abs_lowestKType_le h_gap hL) x_mem M
    refine ⟨l.dsAction M x, step_mem, step_le.trans ?_, rightDeriv_smear _ _ x_eq M⟩
    rw [show ‖M‖ = 1 from norm_frame_conj_single q.1 q.2, mul_one, List.length_cons,
      pow_succ' _ w.length]
    push_cast
    grw [x_le]
    gcongr <;> linarith

/-- Let `l = 2λ` be a doubled Harish-Chandra parameter of large gap, `c_λ = l.dsCoeffInFrame` the
coefficient on `G₁` of its discrete series and `deg = l.formalDegree` the formal degree. Then
`deg · c_λ` is idempotent under convolution on `G₁`. -/
lemma convolve_formalDegree_mul_dsCoeffInFrame_self (h_gap : l.HasLargeGap A) :
    convolve (fun g : 𝔰.G₁ ↦ (l.formalDegree : ℂ) * l.dsCoeffInFrame g)
        (fun g : 𝔰.G₁ ↦ (l.formalDegree : ℂ) * l.dsCoeffInFrame g) =
      fun g : 𝔰.G₁ ↦ (l.formalDegree : ℂ) * l.dsCoeffInFrame g := by
  set idem : 𝔰.G₁ → ℂ := fun g ↦ l.formalDegree * l.dsCoeffInFrame g
  have idem_ker : IsIdempotentKernel idem := isIdempotentKernel_dsCoeffInFrame h_gap
  ext y
  have h_repro : ∫ a : 𝔰.G₁, idem a⁻¹ * idem (y * (a * 1)) = idem y / idem 1 * idem 1 :=
    idem_ker.integral_inv_mul_translate y 1
  rw [div_mul_cancel₀ _ idem_ker.apply_one_ne_zero] at h_repro
  simpa only [mul_one, convolve, smul_eq_mul] using h_repro

/-- Let `l = 2λ` be a doubled Harish-Chandra parameter, `c_λ = l.dsCoeff` its coefficient on
`U(diag ε)`, `deg = l.formalDegree` the inverse of `∫ |c_λ| ^ 2`, and `β` a bump function on
`U(diag ε)`. The convolution on `G₁` of the pullbacks of `deg · c_λ` and `β` by the frame is the
pullback of `deg` times the convolution (`smear`) of `c_λ` with `β` on `U(diag ε)`. -/
lemma convolve_formalDegree_mul_dsCoeffInFrame_comp_frameEquiv (l : HCParam ε) (β : Bumps ε) :
    convolve (fun g : 𝔰.G₁ ↦ (l.formalDegree : ℂ) * l.dsCoeffInFrame g)
        (fun g : 𝔰.G₁ ↦ (β : USign ε → ℂ) (frameEquiv g)) =
      fun g : 𝔰.G₁ ↦
        (l.formalDegree : ℂ) * (smear l.dsCoeffSmooth.val) β (frameEquiv g) := by
  -- The frame carries the Haar measure of `G₁` to that of `U(diag ε)`.
  let π : 𝔰.G₁ ≃ₜ* USign ε := frameEquiv
  ext y
  calc ∫ a : 𝔰.G₁, (β : USign ε → ℂ) (π a⁻¹) • ((l.formalDegree : ℂ) * l.dsCoeff (π (y * a)))
    _ = l.formalDegree *
        ∫ a : 𝔰.G₁, (β : USign ε → ℂ) (π a)⁻¹ • l.dsCoeff (π y * π a : USign ε) := by
      simp only [← integral_const_mul, map_mul, map_inv, mul_smul_comm]
    _ = l.formalDegree * (smear l.dsCoeffSmooth.val) β (π y) := by
      simp [smear_apply, π, ← integral_comp_frameEquiv (J := 𝔰.J₁)]

omit [UnitarySignFrame 𝔰 ε] in
/-- Let `l = 2λ` be a doubled Harish-Chandra parameter of large gap, `c_λ` the coefficient on
`U(diag ε)` of its discrete series and `deg = l.formalDegree` the formal degree. The squared norm
of a vector `x` of `U(𝔤) c_λ = l.DsModule`, a space of smooth functions on `U(diag ε)`, is `deg`
times the integral of `|x| ^ 2`. -/
lemma HCParam.HasLargeGap.norm_sq_eq_formalDegree_mul_integral (h_gap : l.HasLargeGap A)
    (x : l.DsModule) :
    ‖x‖ ^ 2 = l.formalDegree * ∫ g : USign ε, ‖(x : USign ε → ℂ) g‖ ^ 2 := by
  have h_inner : ⟪h_gap.toL2 x, rightRegularL2 1 (h_gap.toL2 x)⟫_ℂ = l.formalDegree *
      ∫ g : USign ε, (x : USign ε → ℂ) (g * 1) * starRingEnd ℂ ((x : USign ε → ℂ) g) :=
    h_gap.inner_toL2_rightRegularL2 x x 1
  -- The norm of `U(𝔤) c_λ` is by definition that of the image in `L²`.
  show ‖h_gap.toL2 x‖ ^ 2 = _
  simpa [Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal] using
    congrArg Complex.re h_inner

omit [DecidableEq I] in
/-- Let `l = 2λ` be a doubled Harish-Chandra parameter of large gap with entries bounded by `L`,
`c_λ = l.dsCoeffInFrame` the coefficient on `G₁` of its discrete series, `deg = l.formalDegree` the
formal degree, and `r = 𝔰.r` the size of the matrices of `G₁`. To each word `w` in the matrix units
belongs an integrable kernel `X w`, with `X [] = deg · c_λ` and `X [] * X w = X w`. For a word of
length `s` the number `‖X w‖₂ ^ 2 / deg` is at most `((r + 1) ^ 4 (L + r + 1 + s)) ^ (2 s)`. For
every bounded measurable `F` with `F * X [] = F` the functions `F * X w` are the right derivatives
of `F`: along a curve `γ` with `γ' t = γ t · Z`, the derivative of `F * X w` at `t` is
`∑ Z a b • (F * X ((a, b) :: w)) (γ t)`. -/
theorem exists_derivative_kernels (h_gap : l.HasLargeGap A)
    (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) :
    ∃ X : List (𝔰.BesselIndex × 𝔰.BesselIndex) → 𝔰.G₁ → ℂ,
      (X [] = fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) ∧
      (∀ w : List (𝔰.BesselIndex × 𝔰.BesselIndex), Integrable (X w)) ∧
      (∀ w : List (𝔰.BesselIndex × 𝔰.BesselIndex), convolve (X []) (X w) = X w) ∧
      (∀ w : List (𝔰.BesselIndex × 𝔰.BesselIndex),
        (∫ g : 𝔰.G₁, ‖X w g‖ ^ 2) / l.formalDegree ≤
          ((𝔰.r + 1) ^ 4 * (L + 𝔰.r + 1 + w.length)) ^ (2 * w.length)) ∧
      ∀ F : 𝔰.G₁ → EuclideanSpace ℂ I, IsBoundedMeasurable F → convolve F (X []) = F →
        ∀ (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) (γ : ℝ → 𝔰.G₁)
          (Z : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (t : ℝ),
          HasDerivAt (fun s : ℝ ↦ (γ s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)) (γ t * Z) t →
          HasDerivAt (convolve F (X w) ∘ γ)
            (∑ a : 𝔰.BesselIndex, ∑ b : 𝔰.BesselIndex,
              Z a b • convolve F (X ((a, b) :: w)) (γ t)) t := by
  -- A bump `β` reproduces `c_λ`. Let `bump w` be its derivative along `w`, and
  -- `X w = idem * bump w` with `idem = deg · c_λ`. Then `X w / deg` is a vector of `U(𝔤) c_λ`,
  -- whose norm is bounded letter by letter.
  let idem : 𝔰.G₁ → ℂ := fun g ↦ l.formalDegree * l.dsCoeffInFrame g
  obtain ⟨β, hβ : (smear l.dsCoeffSmooth.val) β = (l.dsGenerator : USign ε → ℂ)⟩ :=
    exists_smear_dsCoeffSmooth_eq h_gap l.dsGenerator
  have idem_int : Integrable idem := (isIdempotentKernel_dsCoeffInFrame h_gap).integrable
  have idem_bdd : IsBoundedMeasurable idem :=
    isBoundedMeasurable_formalDegree_mul_dsCoeffInFrame h_gap
  let π : 𝔰.G₁ ≃ₜ* USign ε := frameEquiv
  let bump (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) : Bumps ε :=
    (bumpDeriv.adTwist p.matrix⁻¹).word w β
  let smearCoeff : Bumps ε →ₗ[ℂ] USign ε → ℂ := smear l.dsCoeffSmooth.val
  let X (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) (g : 𝔰.G₁) : ℂ :=
    l.formalDegree * smearCoeff (bump w) (π g)
  have bump_int (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) :
      Integrable ((bump w : USign ε → ℂ) ∘ π) :=
    measurePreserving_frameEquiv.integrable_comp_of_integrable (bump w).prop.integrable
  have X_eq (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) :
      convolve idem ((bump w : USign ε → ℂ) ∘ π) = X w :=
    convolve_formalDegree_mul_dsCoeffInFrame_comp_frameEquiv l (bump w)
  -- The generator is `dsCoeff`, whose pullback by the frame is `dsCoeffInFrame` by definition.
  have X_nil : X [] = idem := funext fun g ↦ congrArg (_ * ·) (congrFun hβ (π g))
  refine ⟨X, X_nil, fun w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_, fun F hF F_conv w γ Z t hZ ↦ ?_⟩
  · rw [← X_eq]
    exact integrable_convolve idem_int (bump_int w)
  · rw [X_nil, ← X_eq, ← idem_bdd.convolve_assoc idem_int (bump_int w),
      convolve_formalDegree_mul_dsCoeffInFrame_self h_gap]
  · obtain ⟨x, -, x_le, x_eq : smearCoeff (bump w) = (x : USign ε → ℂ)⟩ :=
      exists_mem_filtration_smear_word (p := p) h_gap hL hβ w
    have norm_sq : ‖x‖ ^ 2 = (∫ g : 𝔰.G₁, ‖X w g‖ ^ 2) / l.formalDegree := by
      rw [h_gap.norm_sq_eq_formalDegree_mul_integral, ← integral_comp_frameEquiv (J := 𝔰.J₁)]
      simp [X, π, x_eq, field, mul_pow, integral_const_mul]
    grw [← norm_sq, x_le, pow_mul']
  · -- `F * X w = F * bump w`; differentiate the bump and expand `Z` in matrix units.
    rw [X_nil] at F_conv
    have F_cont : Continuous (F ∘ π.invFun) := by
      simpa only [F_conv] using (hF.continuous_convolve idem_int).comp π.continuous_invFun
    have FX_eq (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) :
        convolve F (X w) = smear (F ∘ π.invFun) F_cont (bump w) ∘ π := by
      rw [← X_eq, ← hF.convolve_assoc idem_int (bump_int w), F_conv]
      simp [funext_iff, π, convolve, ← integral_comp_frameEquiv]
    rw [FX_eq w]
    refine .congr_deriv (hasDerivAt_smear _ _ F_cont (X := p.matrix⁻¹.val * Z * p.matrix) ?_) ?_
    · simpa [π, frameEquiv, U.conj, mul_assoc] using (hZ.const_mul p.matrix⁻¹.val).mul_const
        p.matrix.val
    · -- Conjugating by the frame twists the action; the letter `(a, b)` acts by a matrix unit.
      show smear _ F_cont (bumpDeriv.adTwist p.matrix⁻¹ Z (bump w)) (π (γ t)) = _
      rw [(bumpDeriv.adTwist p.matrix⁻¹).apply_eq_sum Z]
      simp only [FX_eq, Function.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
        map_smul, Finset.sum_apply, Pi.smul_apply]
      rfl

end Kernels

/-- Let `l = 2λ` satisfy `l.HasLargeGap A` (gap `500 r³ + A`), with coefficient `c_λ` on `G₁` and
formal degree `deg`. Let `rep` be a unitary representation of `U(κ)` on `ℂ^I`. Let `F` be a Bessel
function for `rep`, integrable over `𝖴 ∖ G₁` (`besselQuotMeasure`) and fixed by convolution with
`deg · c_λ`. The squared norm in `L²(G₁)` of the matrix coefficient `g ↦ ∫ ⟪F y, F (y g)⟫` is
`‖F‖₂ ^ 4 / deg`, as this coefficient is `c_λ` times `‖F‖₂ ^ 2`. The integral in `y` and the norm
`‖F‖₂` are taken over `𝖴 ∖ G₁`. -/
theorem IsBesselFunction.lintegral_enorm_sq_integral_inner_translate
    {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ} {l : HCParam ε} {A : ℕ}
    (h_gap : l.HasLargeGap A) {F : 𝔰.G₁ → EuclideanSpace ℂ I} (hF : IsBesselFunction rep F)
    (F_int : Integrable F besselQuotMeasure)
    (F_conv : convolve F (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) = F) :
    ∫⁻ g : 𝔰.G₁, ‖∫ y : 𝔰.G₁, ⟪F y, F (y * g)⟫_ℂ ∂besselQuotMeasure‖ₑ ^ 2 =
      ENNReal.ofReal l.formalDegree⁻¹ *
        (∫⁻ y : 𝔰.G₁, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure) ^ 2 := by
  have h_deg : 0 < l.formalDegree := formalDegree_pos h_gap
  -- The matrix coefficient of `F` is `c_λ` times its squared norm.
  have h_coeff (g : 𝔰.G₁) : ∫ y, ⟪F y, F (y * g)⟫_ℂ ∂besselQuotMeasure =
      l.dsCoeffInFrame g * (∫ y, ‖F y‖ ^ 2 ∂besselQuotMeasure : ℝ) := by
    have h_inner : ∫ y, ⟪F (y * 1), F (y * g)⟫_ℂ ∂besselQuotMeasure =
        l.formalDegree * l.dsCoeffInFrame (1⁻¹ * g) / l.formalDegree *
          (∫ y, ‖F y‖ ^ 2 ∂besselQuotMeasure : ℝ) :=
      hF.integral_inner_translate rfl (by simp) hF.map_unipotent_mul F_int
        (isIdempotentKernel_dsCoeffInFrame h_gap) (by simp [HCParam.dsCoeffInFrame]) F_conv 1 g
    simpa [h_deg.ne'] using h_inner
  have h_norm : ∫⁻ g : 𝔰.G₁, ‖l.dsCoeffInFrame g‖ₑ ^ 2 = .ofReal l.formalDegree⁻¹ := by
    have h_int : Integrable (l.dsCoeffInFrame : 𝔰.G₁ → ℂ) := (integrable_const_mul_iff
      (by simp [h_deg.ne']) _).1 (isIdempotentKernel_dsCoeffInFrame h_gap).integrable
    rw [lintegral_enorm_sq h_int
      (IsBoundedMeasurable.of_continuous ⟨1, fun _ ↦ norm_dsCoeff_le_one h_gap _⟩).memLp_top,
      HCParam.formalDegree, inv_inv, ← integral_comp_frameEquiv (J := 𝔰.J₁)]
    -- `formalDegree` is the inverse of the integral of `‖dsCoeff‖ ^ 2`.
    rfl
  simp_rw [h_coeff, enorm_mul, mul_pow, lintegral_mul_const' _ _ (pow_ne_top enorm_ne_top)]
  rw [h_norm, lintegral_enorm_sq F_int hF.memLp_top, ← ofReal_norm,
    Complex.norm_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)]

/-- Let `F` be a Bessel function on `G₁` for the unitary representation `rep` of `U(κ)`: bounded,
measurable, and transforming on the left by a character under `besselU` and by `rep` under `U(κ)`.
Its convolution with an integrable kernel `k` on `G₁` is again a Bessel function for `rep`. -/
lemma IsBesselFunction.convolve_of_integrable
    {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ} {F : 𝔰.G₁ → EuclideanSpace ℂ I}
    (hF : IsBesselFunction rep F) {k : 𝔰.G₁ → ℂ} (k_int : Integrable k) :
    IsBesselFunction rep (convolve F k) := by
  -- Left translations commute with the convolution, and so does each scalar or linear map.
  refine ⟨hF.convolve_right k_int, fun n hn y ↦ ?_, fun h y ↦ ?_⟩
  · simp [convolve, mul_assoc, hF.map_unipotent_mul n hn, smul_comm (k _), integral_smul]
  · simp [convolve, mul_assoc, hF.map_unitary_mul, ← ContinuousLinearMap.integral_comp_comm,
      hF.integrable_smul k_int.comp_inv]

/-- **Schur's bound for a Bessel function.** Let `l = 2λ` be a doubled Harish-Chandra parameter with
gap `500 r ^ 3 + A` (`l.HasLargeGap A`) and entries bounded by `L`. Its coefficient is
`c_λ = l.dsCoeffInFrame` on `G₁`, and its formal degree is `deg = l.formalDegree`. Let `rep` be a
unitary representation on `ℂ^I` of `U(κ)`, the unitary group of the positive definite middle part.
Let `F` be a Bessel function for `rep`, integrable over `𝖴 ∖ G₁` and fixed by convolution with
`deg · c_λ`. Let `B ≥ (r + 1) ^ 4 (L + r + 1 + 2 n ^ 2)`. Then `F` has right derivatives `V w` along
the words `w` in the matrix units, which are again Bessel functions for `rep`. Take
`s = |w| ≤ 2 n ^ 2` and `φ` integrable on `G₁`. Then the function `g ↦ ∫ φ y • V w (g y)` has
squared norm at most `B ^ (2 s) ‖F‖₂ ^ 2 ‖φ‖₂ ^ 2 / deg` in `L²(𝖴 ∖ G₁)`, with `‖F‖₂` taken over
`𝖴 ∖ G₁`. -/
theorem IsBesselFunction.hasSchurBound_of_convolve_eq
    {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ} {l : HCParam ε} {A L : ℕ}
    (h_gap : l.HasLargeGap A) (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L)
    {F : 𝔰.G₁ → EuclideanSpace ℂ I} (hF : IsBesselFunction rep F)
    (F_int : Integrable F besselQuotMeasure) (B : ℝ)
    (F_conv : convolve F (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) = F)
    (hB : (𝔰.r + 1) ^ 4 * (L + 𝔰.r + 1 + (2 * 𝔰.n ^ 2 : ℕ)) ≤ B) :
    RealPlace.HasSchurBound F rep B
      (ENNReal.ofReal l.formalDegree⁻¹ * ∫⁻ y : 𝔰.G₁, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure) := by
  let idem : 𝔰.G₁ → ℂ := fun g ↦ l.formalDegree * l.dsCoeffInFrame g
  -- The derivatives are the convolutions of `F` with the kernels `X w`.
  obtain ⟨X, (X_nil : X [] = idem), X_int, X_conv, X_norm, X_deriv⟩ :=
    exists_derivative_kernels (I := I) h_gap hL
  have F_conv_nil : convolve F (X []) = F := by rw [X_nil, F_conv]
  refine ⟨fun w ↦ ⟨convolve F (X w), hF.continuous_convolve (X_int w)⟩, F_conv_nil.symm,
    fun w ↦ ⟨?_, X_deriv F hF.toIsBoundedMeasurable F_conv_nil w, fun hw φ φ_int ↦ ?_⟩⟩
  · exact hF.convolve_of_integrable (X_int w)
  · have idem_conv : convolve idem (X w) = X w := by rw [← X_nil, X_conv]
    have norm_le : (∫ g, ‖X w g‖ ^ 2) / l.formalDegree ≤ B ^ (2 * w.length) :=
      calc (∫ g, ‖X w g‖ ^ 2) / l.formalDegree
        _ ≤ ((𝔰.r + 1) ^ 4 * (L + 𝔰.r + 1 + w.length)) ^ (2 * w.length) := X_norm w
        _ ≤ B ^ (2 * w.length) := by grw [← hB, ← hw]
    -- Schur orthogonality bounds the integral by the norms of `X w`, `F` and `φ`.
    calc ∫⁻ g, ‖∫ y, φ y • convolve F (X w) (g * y)‖ₑ ^ 2 ∂besselQuotMeasure
      _ = ∫⁻ y, ‖convolve (convolve F (X w)) (fun a ↦ φ a⁻¹) y‖ₑ ^ 2 ∂besselQuotMeasure := by
        simp only [convolve.eq_1 (convolve F (X w)), inv_inv]
      _ ≤ .ofReal ((∫ g, ‖X w g‖ ^ 2) / l.formalDegree) *
          (.ofReal l.formalDegree⁻¹ * ∫⁻ y, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure) * ∫⁻ y, ‖φ y‖ₑ ^ 2 :=
        hF.lintegral_sq_convolve_convolve_le rfl (by simp) hF.map_unipotent_mul F_int (X_int w)
          (isIdempotentKernel_dsCoeffInFrame h_gap) (by simp [HCParam.dsCoeffInFrame]) F_conv
          (isBoundedMeasurable_formalDegree_mul_dsCoeffInFrame h_gap) idem_conv φ_int
      _ ≤ _ := by grw [norm_le]

end New
