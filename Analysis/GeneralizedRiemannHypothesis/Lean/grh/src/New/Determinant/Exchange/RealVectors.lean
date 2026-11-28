import New.Determinant.Exchange.LargeTriple

/-!
# Smooth local Witt theorem and the exchange identity for `V' ⊕ W₁` and `V'`

Construction of the data at the real places for the identity `New.Exchange.RowColExchangeIdentity`
between the theta integrals of the pairs `(X, V' ⊕ W₁)` and `(X, V')`, where `X` splits over `W₁`.

* `New.Exchange.exists_isSchwartzVector_realSlice_eq`: a Schwartz Fock vector whose slices are a
  bump function times `realWeil 1 v`, scaled so that its slice at 0 for the opposite splitting is
  `v`.
* `New.Exchange.exists_contDiff_witt`: a local form of Witt's theorem for spans: frames near a
  nondegenerate frame `x` lie in the span of a unitary image of `x` that depends smoothly on them.
* `New.Exchange.exists_rowColExchangeIdentity_sum`: two vectors for which
  `New.Exchange.RowColExchangeIdentity` holds for these two pairs, one of them with a prescribed
  slice at 0.

Notions from other files:
* `New.Space.Splitting`: a decomposition V = (lE^p ⊕ kE^p) ⊥ iV₀ with dual isotropic frames l, k and
  an isometric embedding i of V₀; `New.Space.Splitting.symm` exchanges k and l. It is adapted
  (`New.Exchange.IsBaseAdapted`) if the frames are orthonormal at the infinite places and integral
  at the finite ones.
* `New.PairFock E s t`: the Fock space of matrices whose `(i, j)` coordinate has the sign
  `t i * s j`, repeated at every infinite place. These signs are `New.homSigns s t`, and repeating
  them at every place is `New.realSigns`.
* `New.realPairWeil γ γ'`: the Weil representation on this Fock space, restricted to a pair of
  unitary groups at the infinite places, twisted by the powers of the determinants with exponents
  `γ` on the second and `-γ'` on the first.
* `New.Exchange.IsSchwartzVector`: all moments of the Fock vector are finite.
* `New.Exchange.realSlice`: the slice of a vector in the mixed Schrödinger–Fock model of an adapted
  splitting.
* `New.Exchange.RowColExchangeIdentity`: two theta integrals are proportional on admissible data,
  with a formula for the absolute value of the factor.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work. See
`Lib.Adelic.Witt.IwasawaDecomposition` for sources.
-/

namespace New.Exchange

open Matrix NumberField MeasureTheory Complex Fock Space Filter ContDiff Norms.Elementwise Finset
  Function Splitting Measure MixedModel GeneralLinearGroup ENNReal IsHermitianInvolution U

variable {E n a b m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
  {s : n → ℤˣ} {r : m → ℤˣ} {X : Space E m r} {W₁ : Space E n s}

/-- Let `τ ≥ 0` be smooth, compactly supported and nonzero at some `y`, and let `v` be a Schwartz
vector for `(W₁, V')`. Then there are a complex number `κ` and a Schwartz vector `Λ` for `(X, V')`
whose slice at each `x` is `τ x • κ` times `realWeil 1 v`, and whose slice at `0` for `D.symm`, the
splitting with the two isotropic frames exchanged, is `v`. -/
lemma exists_isSchwartzVector_realSlice_eq (D : X.Splitting W₁ b) [IsBaseAdapted D] {t' : a → ℤˣ}
    (V' : Space E a t') (τ : (InfinitePlace E × a × b → ℂ) → ℝ) (hτ : ContDiff ℝ ∞ τ)
    {v : fockSpace (realSigns E (homSigns s t'))} (hv : IsSchwartzVector v)
    (hsupp : HasCompactSupport τ) (hτ₀ : 0 ≤ τ) (y : InfinitePlace E × a × b → ℂ) (hy : τ y ≠ 0) :
    ∃ (κ : ℂ) (Λ : fockSpace (realSigns E (homSigns r t'))),
      IsSchwartzVector Λ ∧
      realSlice D.symm V' 0 Λ = v ∧
      ∀ x : InfinitePlace E × a × b → ℂ,
        (isAdapted_homSource D V').mixedModel.slice x Λ = (τ x • κ) • realWeil 1 v := by
  -- Choose `κ` so that `τ κ` and the Gaussian slices of the vacuum have the same integral. The
  -- slice at `0` for `D.symm` is the integral of all slices, so the section `τ κ • v` gives `v`.
  have hpos : 0 < ∫ x, τ x ∂normalizedVolume _ :=
    hτ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hτ₀ hy
  set 𝓜 := (isAdapted_homSource D V').mixedModel
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ,
      ∫ x, 𝓜.slice x Fock.vacVector 0 ∂normalizedVolume _ = (∫ x, τ x ∂normalizedVolume _ : ℝ) *
        κ :=
    ⟨_, (mul_div_cancel₀ _ (ofReal_ne_zero.2 hpos.ne')).symm⟩
  obtain ⟨Λ, hΛ, hslice⟩ := 𝓜.exists_isSchwartzVector_slice_eq (hτ.smul_const κ) hsupp.smul_right
    (u := fun _ ↦ 1) contDiff_const hv
  -- It is enough to compare the two vectors after tensoring with zero terms.
  refine ⟨κ, Λ, hΛ, eq_of_integrated_zeroTerm_eq (isAdapted_homSource D.symm V') fun f ↦ ?_, hslice⟩
  -- Both sides are integrals of slices for `volume`, which is a multiple of the Haar measure
  -- `vacuumMeasure` moved by `star g`, for the change of frame `g`.
  let g : GL (a × b) (𝔸 E) := adaptedHomBasis b V'
  have : MeasurableConstSMul (GL (a × b) (𝔸 E)) (a × b → 𝔸 E) :=
    ContinuousConstSMul.toMeasurableConstSMul
  let ν : Measure (a × b → 𝔸 E) := DomMulAct.mk (star g) • vacuumMeasure
  obtain ⟨c, hc⟩ : ∃ c : NNReal, volume = c • ν := ⟨_, isAddLeftInvariant_eq_smul volume ν⟩
  let term (x : a × b → 𝔸 E) : 𝒮 (X.hom V') → 𝒮 (W₁.hom V') :=
    (D.homSource V').slice ((g⁻¹ : GL (a × b) (𝔸 E)).valᴴ *ᵥ x)
  suffices h : ∫ x, term x ((X.hom V').integrated Λ f) ∂vacuumMeasure =
      ∫ x, (W₁.hom V').integrated v (term x ((X.hom V').projReal f)) ∂vacuumMeasure by
    calc _ = (D.symm.homSource V').zeroTerm ((X.hom V').integrated Λ f) :=
        (zeroTerm_integrated (isAdapted_homSource D.symm V') Λ f).symm
      _ = ∫ x, (D.homSource V').slice x ((X.hom V').integrated Λ f) :=
        symm_homSource_zeroTerm_eq_integral D V' _
      _ = ∫ x,
          (W₁.hom V').integrated v ((D.homSource V').slice x ((X.hom V').projReal f)) := by
        simpa [hc, ν, term, integral_domSMul, star, -coe_units_inv] using congrArg (c • ·) h
      _ = (W₁.hom V').integrated v ((D.symm.homSource V').zeroTerm ((X.hom V').projReal f)) := by
        rw [symm_homSource_zeroTerm_eq_integral,
          ← (integrated _ v).integral_comp_comm (by fun_prop)]
  -- In real and finite coordinates, both integrands are a function of the real variable times the
  -- same function `ψ` of the finite one.
  have term_eq (Φ : PairFock E r t') (x : a × b → 𝔸 E) : term x ((X.hom V').integrated Φ f) =
      (W₁.hom V').integrated (𝓜.slice (realCoord x) Φ) ((D.homSource V').slice
        (g⁻¹.valᴴ *ᵥ fun i ↦ (0, (x i).2)) ((X.hom V').projReal f)) :=
    slice_integrated (isAdapted_homSource D V') x Φ f
  let ψ (x : a × b → 𝔸f E) : 𝒮 (W₁.hom V') :=
    (W₁.hom V').integrated v ((D.homSource V').slice
      (g.val⁻¹ᴴ *ᵥ fun i ↦ (0, (WeilData.scaleIdele E).val.2 * x i)) ((X.hom V').projReal f))
  let μ := (normalizedVolume (InfinitePlace E × a × b)).prod (latticeMeasure E (a × b))
  -- Split off the real integrals (Fubini) and compare them by `hκ`.
  have h : ∫ x, ((τ x.1 : ℂ) * κ) • ψ x.2 ∂μ = ∫ x, 𝓜.slice x.1 Fock.vacVector 0 • ψ x.2 ∂μ := by
    rw [integral_prod_smul (fun x ↦ (τ x : ℂ) * κ) ψ, integral_mul_const, integral_complex_ofReal,
      integral_prod_smul (fun x ↦ 𝓜.slice x Fock.vacVector 0) ψ, hκ]
  -- Here `projReal` is `integrated` at the vacuum, so `term_eq` applies to both sides.
  simp only [term_eq]
  -- Insert the slice of `Λ` and split the adelic variable into real and finite parts.
  simpa [g, (adelicSum E 1).integral_eq_integral_prod, adelicSum, realCoord.eq_unfold, hslice]
    using h

/-- Taking the slice at `0` is onto on Schwartz vectors. Every Schwartz vector `v` (all moments
finite) in the Fock space `PairFock E s t'` of `(W₁, V')` is the slice at `0` of a Schwartz vector
in the Fock space `PairFock E r t'` of `(X, V')`. -/
lemma exists_isSchwartzVector_realSlice_zero_eq (A : X.Splitting W₁ b) [IsBaseAdapted A]
    {t' : a → ℤˣ} (V' : Space E a t') {v : PairFock E s t'} (hv : IsSchwartzVector v) :
    ∃ w : PairFock E r t', IsSchwartzVector w ∧ realSlice A V' 0 w = v := by
  -- Prescribe the slices along `A.symm`, with the standard smooth bump function. The splitting
  -- opposite to `A.symm` is `A` by definition.
  let τ : (InfinitePlace E × a × b → ℂ) → ℝ := ExistsContDiffBumpBase.u
  have hτ_zero : τ 0 ≠ 0 := (ExistsContDiffBumpBase.u_support _).ge (by simp)
  obtain ⟨-, w, hw, hw_zero, -⟩ := exists_isSchwartzVector_realSlice_eq A.symm V' τ
    (ExistsContDiffBumpBase.u_smooth _) hv (ExistsContDiffBumpBase.u_compact_support _)
    ExistsContDiffBumpBase.u_nonneg 0 hτ_zero
  exact ⟨w, hw, hw_zero⟩

/-- A smooth local form of Witt's theorem, for spans. Let `J` be Hermitian and `x` a frame
(a matrix of column vectors) with invertible Gram matrix `xᴴ * J * x`. There are elements `k y` of
the unitary group `U J`, indexed by all frames `y`, such that the matrix of `k y` is a smooth
function of `y` and, for `y` near `x`, the columns of `y` are linear combinations of those of
`k y * x`. -/
theorem exists_contDiff_witt {J : Matrix m m ℂ} (hJ : Jᴴ = J) {x : Matrix m b ℂ}
    (hdet : (xᴴ * J * x).det ≠ 0) :
    ∃ k : Matrix m b ℂ → U J,
      ContDiff ℝ ∞ (fun y : Matrix m b ℂ ↦ (k y : Matrix m m ℂ)) ∧
      ∀ᶠ y : Matrix m b ℂ in nhds x, ∃ c : Matrix b b ℂ, (k y : Matrix m m ℂ) * x * c = y := by
  -- `L a` lies in the Lie algebra of `U J`, and `a - L a` keeps the span of `x`. The map
  -- `T a = exp (L a) * (a - L a)` has derivative the identity at `1`, so it has a local inverse
  -- `A`; apply `A` to a matrix `z y` near `1` with `z y * x = y`.
  let w : Matrix b m ℂ := (xᴴ * J * x)⁻¹ * xᴴ
  have hw (y : Matrix m b ℂ) : y * w * J * x = y := by
    rw [Matrix.mul_assoc] at hdet
    simp [w, hdet, Matrix.mul_assoc]
  let L (a : Matrix m m ℂ) : Matrix m m ℂ := (a * x * w - x * w * aᴴ) * J
  have hL (a : Matrix m m ℂ) : L a ∈ unitaryLie J := by
    simp [unitaryLie, L, w, hJ, conjTranspose_nonsing_inv, Matrix.mul_assoc, sub_mul, mul_sub]
  have hL_span (a : Matrix m m ℂ) : (a - L a) * x = x * (w * aᴴ * J * x) := by
    simp only [L, Matrix.sub_mul, hw, _root_.sub_sub_cancel, Matrix.mul_assoc x]
  let T (a : Matrix m m ℂ) : Matrix m m ℂ := NormedSpace.exp (L a) * (a - L a)
  have hL₁ : L 1 = 0 := by simp [L]
  have hT₁ : T 1 = 1 := by simp [T, hL₁]
  have hT' : HasFDerivAt T (ContinuousLinearEquiv.refl ℝ _).toContinuousLinearMap 1 := by
    obtain ⟨L', hL'⟩ := (by fun_prop : ContDiff ℝ 1 L).differentiable_one 1
    open Norms.L2Operator in
      -- The product rule gives `(id - L') + L'`.
      refine ((HasFDerivAt.comp 1 (by simpa [hL₁] using hasFDerivAt_exp_zero) hL').fun_mul'
        ((hasFDerivAt_id 1).fun_sub hL')).congr_fderiv ?_
      simp only [hL₁, NormedSpace.exp_zero, sub_zero, id, one_smul, MulOpposite.op_one]
      exact sub_add_cancel _ L'
  obtain ⟨A, hA, hTA⟩ : ∃ A, ContDiff ℝ ∞ A ∧ ∀ᶠ z in nhds 1, T (A z) = z := by
    have hT : ContDiffAt ℝ ω T 1 := by fun_prop
    obtain ⟨A, hA, h_eq⟩ := exists_contDiff_eventuallyEq (hT.to_localInverse hT' (by simp))
    rw [← hT₁]
    exact ⟨A, hA, (h_eq.fun_comp T).trans (HasStrictFDerivAt.eventually_right_inverse _)⟩
  let z (y : Matrix m b ℂ) : Matrix m m ℂ := 1 - (x - y) * w * J
  have hz : Tendsto z (nhds x) (nhds 1) := Continuous.tendsto' (by fun_prop) _ _ (by simp [z])
  refine ⟨fun y ↦ expU ⟨L (A (z y)), hL _⟩, by fun_prop,
    (hz.eventually hTA).mono fun y hy ↦ ⟨w * (A (z y))ᴴ * J * x, ?_⟩⟩
  calc NormedSpace.exp (L (A (z y))) * x * (w * (A (z y))ᴴ * J * x)
    _ = T (A (z y)) * x := by rw [Matrix.mul_assoc, ← hL_span, ← Matrix.mul_assoc]
    _ = z y * x := by rw [hy]
    _ = y := by simp [z, Matrix.sub_mul, hw]

/-- The external product `realBoxProd he v w` of two Schwartz Fock vectors (all moments finite), for
a splitting `e` of the coordinates compatible with the signs, is a Schwartz vector. -/
lemma isSchwartzVector_realBoxProd {ι ι₁ ι₂ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι₁]
    [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] {ε : ι → ℤˣ} {ε₁ : ι₁ → ℤˣ} {ε₂ : ι₂ → ℤˣ}
    {e : ι₁ ⊕ ι₂ ≃ ι}
    (he : ε ∘ e = ε₁ ⊕ᵥ ε₂) {v : fockSpace ε₁} {w : fockSpace ε₂} (hv : IsSchwartzVector v)
    (hw : IsSchwartzVector w) : IsSchwartzVector (realBoxProd he v w) := by
  -- `realBoxProd he v w` is an iterated integral of translates of the vacuum, against `w` and then
  -- `v`; padding a vector with zeros does not increase its maximum norm.
  intro N
  have pad_left (x : ι₁ → ℂ) : ‖(realCoordSum he).equiv (x, 0)‖ₑ ≤ ‖x‖ₑ := by
    simp [realCoordSum, enorm, pi_nnnorm_le_iff, e.surjective.forall, nnnorm_le_pi_nnnorm]
  have pad_right (y : ι₂ → ℂ) : ‖(realCoordSum he).equiv (0, y)‖ₑ ≤ ‖y‖ₑ := by
    simp [realCoordSum, enorm, pi_nnnorm_le_iff, e.surjective.forall, nnnorm_le_pi_nnnorm]
  let inner : fockSpace ε := ∫ y, w y • realHeisenbergOp ((realCoordSum he).equiv (0, y))
    Fock.vacVector
    ∂normalizedVolume ι₂
  have inner_le : fockMoment N inner ≤
      fockMoment N (Fock.vacVector : fockSpace ε) * fockMoment N w := by
    refine (fockMoment_integral_le _).trans (lintegral_fockMoment_smul_le fun y ↦ ?_)
    grw [fockMoment_realHeisenbergOp_le, pad_right, mul_comm]
  have outer_le : fockMoment N (realBoxProd he v w) ≤
      fockMoment N (Fock.vacVector : fockSpace ε) * fockMoment N w * fockMoment N v := by
    refine (fockMoment_integral_le _).trans (lintegral_fockMoment_smul_le fun x ↦ ?_)
    change fockMoment N (realHeisenbergOp ((realCoordSum he).equiv (x, 0)) inner) ≤ _
    grw [fockMoment_realHeisenbergOp_le, pad_left, inner_le, mul_comm]
  exact ne_top_of_le_ne_top (mul_ne_top (mul_ne_top (isSchwartzVector_vacVector N) (hw N)) (hv N))
    outer_le

/-- Matrix inversion agrees, near a matrix `A₀` of nonzero determinant, with a function that is
smooth on all matrices. -/
lemma exists_contDiff_eventuallyEq_inv {A₀ : Matrix b b ℂ} (hdet : A₀.det ≠ 0) :
    ∃ γ : Matrix b b ℂ → Matrix b b ℂ,
      ContDiff ℝ ∞ γ ∧ γ =ᶠ[nhds A₀] fun A : Matrix b b ℂ ↦ A⁻¹ := by
  -- The inverse is the adjugate, a polynomial in the entries, divided by the determinant.
  have det_smooth : ContDiffAt ℝ ω (fun A : Matrix b b ℂ ↦ A.det) A₀ := by
    simp only [det_apply]
    fun_prop
  have adjugate_smooth : ContDiffAt ℝ ω (fun A : Matrix b b ℂ ↦ A.adjugate) A₀ := by
    refine contDiffAt_pi.2 fun i : b ↦ contDiffAt_pi.2 fun j : b ↦ ?_
    simp only [adjugate_apply, det_apply, updateRow_apply, prod_ite]
    fun_prop
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact exists_contDiff_eventuallyEq ((det_smooth.inv hdet).smul adjugate_smooth)

/-- If `x * A` has an invertible Gram matrix for `J` and equals `g * x₀ * c` with `g` in the unitary
group `U J`, then `x` has the same form `g * x₀ * c'`, and `c'` carries the Gram matrix of `x₀` to
that of `x`. -/
lemma exists_mul_mul_eq_and_gram_eq {J : Matrix m m ℂ} (g : U J) {x₀ x : Matrix m b ℂ}
    {A c : Matrix b b ℂ}
    (hc : (g : Matrix m m ℂ) * x₀ * c = x * A) (hdet : ((x * A)ᴴ * J * (x * A)).det ≠ 0) :
    ∃ c' : Matrix b b ℂ,
      (g : Matrix m m ℂ) * x₀ * c' = x ∧ c'ᴴ * (x₀ᴴ * J * x₀) * c' = xᴴ * J * x := by
  rw [gram_mul, det_mul] at hdet
  have hx : (g : Matrix m m ℂ) * x₀ * (c * A⁻¹) = x := by
    simp [← Matrix.mul_assoc, hc, right_ne_zero_of_mul hdet]
  exact ⟨c * A⁻¹, hx, by conv_rhs => rw [← hx, gram_mul, U.gram_invariant]⟩

/-- Smooth data for Witt's theorem near a frame `x₀`, for a form `J`: a function `γ` on square
matrices, unitary elements `k y` indexed by frames `y`, and a bump function `σ` on families of
frames. For each member `y` of a family at which `σ` does not vanish, `γ` inverts the Gram matrix of
`y` and `y` lies in the span of `k y * x₀`. -/
structure IsWittBump {ι : Type*} [Fintype ι] (J : Matrix m m ℂ) (x₀ : Matrix m b ℂ)
    (γ : Matrix b b ℂ → Matrix b b ℂ) (k : Matrix m b ℂ → U J) (σ : (ι → Matrix m b ℂ) → ℝ) :
    Prop where
  /-- `γ` is smooth. -/
  contDiff_inv : ContDiff ℝ ∞ γ
  /-- `γ` inverts the Gram matrix of `x₀`. -/
  inv_gram_base : γ (x₀ᴴ * J * x₀) = (x₀ᴴ * J * x₀)⁻¹
  /-- The matrix of `k y` is a smooth function of `y`. -/
  contDiff_unitary : ContDiff ℝ ∞ fun y : Matrix m b ℂ ↦ (k y : Matrix m m ℂ)
  /-- `σ` is smooth. -/
  contDiff_bump : ContDiff ℝ ∞ σ
  /-- `σ` has compact support. -/
  hasCompactSupport_bump : HasCompactSupport σ
  /-- `σ` is nonnegative. -/
  bump_nonneg : ∀ x : ι → Matrix m b ℂ, 0 ≤ σ x
  /-- `σ` is `1` at the constant family `x₀`. -/
  bump_base : σ (fun _ : ι ↦ x₀) = 1
  /-- Where `σ` does not vanish, each frame `y` lies in the span of `k y * x₀`. -/
  exists_mul_eq : ∀ x : ι → Matrix m b ℂ, σ x ≠ 0 → ∀ i : ι,
    ∃ c : Matrix b b ℂ, (k (x i) : Matrix m m ℂ) * x₀ * c = x i
  /-- Where `σ` does not vanish, `γ` inverts the Gram matrix of each frame. -/
  inv_gram : ∀ x : ι → Matrix m b ℂ, σ x ≠ 0 → ∀ i : ι,
    γ ((x i)ᴴ * J * x i) = ((x i)ᴴ * J * x i)⁻¹
  /-- Where `σ` does not vanish, the Gram matrix of each frame is invertible. -/
  det_gram_ne_zero : ∀ x : ι → Matrix m b ℂ, σ x ≠ 0 → ∀ i : ι, ((x i)ᴴ * J * x i).det ≠ 0

/-- For `J` Hermitian and a frame `x₀` with invertible Gram matrix there are a smooth function `γ`,
elements `k y` of `U J` depending smoothly on the frame `y` and a bump function `σ`, equal to 1 at
the constant family `x₀`, such that for each member `y` of a family where `σ` is nonzero `γ` inverts
the invertible Gram matrix of `y` and `y` lies in the span of `k y * x₀` (`IsWittBump`). -/
lemma exists_contDiff_witt_and_bump {ι : Type*} [Fintype ι] {J : Matrix m m ℂ} (hJ : Jᴴ = J)
    {x₀ : Matrix m b ℂ} (hdet : (x₀ᴴ * J * x₀).det ≠ 0) :
    ∃ (γ : Matrix b b ℂ → Matrix b b ℂ) (k : Matrix m b ℂ → U J) (σ : (ι → Matrix m b ℂ) → ℝ),
      IsWittBump J x₀ γ k σ := by
  obtain ⟨γ, γ_smooth, γ_inv⟩ := exists_contDiff_eventuallyEq_inv hdet
  obtain ⟨k, k_smooth, span_near⟩ := exists_contDiff_witt hJ hdet
  have gram_near : ∀ᶠ y : Matrix m b ℂ in nhds x₀,
      γ (yᴴ * J * y) = (yᴴ * J * y)⁻¹ ∧ (yᴴ * J * y).det ≠ 0 :=
    Continuous.tendsto (f := fun y : Matrix m b ℂ ↦ yᴴ * J * y) (by fun_prop) x₀
      (γ_inv.and (ContinuousAt.eventually_ne (by fun_prop) hdet))
  obtain ⟨σ, σ_supp, σ_cpt, σ_smooth, σ_range, σ_one⟩ :=
    exists_contDiff_tsupport_subset
      (nhds_pi.le (eventually_pi fun _ : ι ↦ span_near.and gram_near))
  have near (x : ι → Matrix m b ℂ) (hx : σ x ≠ 0) (i : ι) :
      (∃ c : Matrix b b ℂ, (k (x i) : Matrix m m ℂ) * x₀ * c = x i) ∧
        γ ((x i)ᴴ * J * x i) = ((x i)ᴴ * J * x i)⁻¹ ∧ ((x i)ᴴ * J * x i).det ≠ 0 :=
    σ_supp (subset_closure hx) i
  simp only [forall_and] at near
  obtain ⟨span_supp, inv_supp, det_supp⟩ := near
  exact ⟨γ, k, σ, γ_smooth, γ_inv.eq_of_nhds, k_smooth, σ_smooth, σ_cpt,
    fun x ↦ (σ_range ⟨x, rfl⟩).1, σ_one, span_supp, inv_supp, det_supp⟩

omit [DecidableEq m] in
/-- The `J`-orthogonal projection `x * (xᴴ * J * x)⁻¹ * xᴴ * J * x₀` of `x₀` to the span of a frame
`x` does not change when `x` is multiplied on the right by an invertible matrix. -/
lemma mul_gram_inv_mul_of_isUnit_det (J : Matrix m m ℂ) (x x₀ : Matrix m b ℂ) {C : Matrix b b ℂ}
    (hC : IsUnit C.det) :
    x * C * (((x * C)ᴴ * J * (x * C))⁻¹ * ((x * C)ᴴ * J * x₀)) =
      x * ((xᴴ * J * x)⁻¹ * (xᴴ * J * x₀)) := by
  have hC' : IsUnit Cᴴ.det := by simpa using hC
  rw [gram_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev, conjTranspose_mul]
  simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hC,
    nonsing_inv_mul_cancel_left _ _ hC']

/-- Let `g`, `k` be unitary for the diagonal form with signs `t' ⊕ᵥ s` and `u` unitary for the form
with signs `t'`. If `k * x₀ * u = g⁻¹ * x₀`, where `x₀ = fromRows 1 0` is the frame of the first
summand, then `g * k * diag(u, 1)` fixes `x₀` and so is `diag(1, q)` with `q` unitary for `s`. -/
lemma exists_sum_one_eq_mul_mul_sum {t' : b → ℤˣ}
    {g k : U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    {u : U (signMatrix t' : Matrix b b ℂ)}
    (h_frame : (k : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) *
        (u : Matrix b b ℂ) =
      (↑g⁻¹ : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ)) :
    ∃ q : U (signMatrix s : Matrix n n ℂ),
      U.sum (signMatrix_sum t' s) (1, q) = g * k * U.sum (signMatrix_sum t' s) (u, 1) := by
  refine (mem_range_sum_right (signMatrix_sum t' s) isUnit).2 ?_
  have h_fix : (g : Matrix (b ⊕ n) (b ⊕ n) ℂ) * ((k : Matrix (b ⊕ n) (b ⊕ n) ℂ) *
      fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) * (u : Matrix b b ℂ)) = fromRows 1 0 := by
    simp [h_frame, ← Matrix.mul_assoc]
  simpa [U.sum, ← fromCols_fromRows_eq_fromBlocks, Matrix.mul_assoc] using h_fix

/-- The coordinates at the infinite places of an `a × b` matrix, read as one complex matrix for each
place. -/
noncomputable def placeMatrices (E a b : Type) [Field E] [CMType E] [Fintype a] [Fintype b] :
    (InfinitePlace E × a × b → ℂ) ≃L[ℝ] InfinitePlace E → Matrix a b ℂ :=
  (LinearEquiv.curry ℝ ℂ (InfinitePlace E) (a × b) ≪≫ₗ LinearEquiv.piCongrRight
    fun _ : InfinitePlace E ↦ LinearEquiv.curry ℝ ℂ a b).toContinuousLinearEquiv

/-- The real slice at an adelic matrix `x` is the slice at its coordinates at infinity. -/
lemma realSlice_eq_slice_placeMatrices_symm (D : X.Splitting W₁ b) [IsBaseAdapted D] {t : a → ℤˣ}
    (V : Space E a t) (x : Matrix a b (𝔸 E)) :
    realSlice D V x =
      (isAdapted_homSource D V).mixedModel.slice ((placeMatrices E a b).symm (atRealPlace x)) :=
  rfl

/-- For a function `γ` that inverts Gram matrices, the projection of the frame `fromRows 1 0` of the
first summand to the span of the frame `x`, orthogonal for the form with signs `t' ⊕ᵥ s`. -/
def frameProjection {t' : b → ℤˣ} (γ : Matrix b b ℂ → Matrix b b ℂ) (x : Matrix (b ⊕ n) b ℂ) :
    Matrix (b ⊕ n) b ℂ :=
  x * (γ (xᴴ * signMatrix (t' ⊕ᵥ s) * x) * (xᴴ * signMatrix (t' ⊕ᵥ s) * fromRows 1 0))

/-- The family `x` of frames moved by the inverses of the unitary elements `k (y v)`. -/
def unitaryMovedFrame {t' : b → ℤˣ}
    (k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ))
    (y x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) : InfinitePlace E → Matrix (b ⊕ n) b ℂ :=
  fun v : InfinitePlace E ↦ (↑(k (y v))⁻¹ : Matrix (b ⊕ n) (b ⊕ n) ℂ) * x v

/-- For families `y`, `x` of frames, one for each infinite place `w`, unitary elements `k y` indexed
by frames, a constant `κ` and vectors `v`, `v₁` in the Fock spaces `PairFock` of the signs `(s, t')`
and `(s, s)`, the vector `(σ y * σ x' * κ * ∏ w, conj (det (x' w)₁) ^ (2 * M w)) • ω (1, k ∘ y) (v ⊠
v₁)`, where `x' w = (k (y w))⁻¹ * x w` (`unitaryMovedFrame`), `(x' w)₁` is its upper square block,
`ω` is the real Weil representation `realPairWeil` twisted by `det ^ (j - M w)` on the unitary group
of `t' ⊕ᵥ s`, and `⊠` is the external product `realBoxProd`. In the applications `t'` and `s` are
the signs of spaces `V'` and `W₁`, `j` is half the rank of `W₁`, `M` is the weight of a character,
and this vector is a prescribed slice for the pair `(X, V' ⊕ W₁)`. -/
noncomputable def exchangeSection {t' : b → ℤˣ}
    (σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ)
    (k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ))
    (j : ℕ) (M : InfinitePlace E → ℕ) (κ : ℂ) (v : PairFock E s t') (v₁ : PairFock E s s)
    (y x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) : PairFock E s (t' ⊕ᵥ s) :=
  ((σ y * σ (unitaryMovedFrame k y x)) •
      ((∏ w : InfinitePlace E, (unitaryMovedFrame k y x w).toRows₁ᴴ.det ^ (M w * 2)) * κ)) •
    realPairWeil (fun w : InfinitePlace E ↦ (j : ℤ) - M w) 0 (1, k ∘ y)
      (realBoxProd (realSigns_comp_split (homSigns_sum_target signs_comp_refl)) v v₁)

/-- Let `σ ≥ 0` be a smooth compactly supported function on families of frames in `V' ⊕ W₁`, equal
to 1 at the frame `(1, 0)` of `V'`, let `N` be a family of exponents and `v` a Schwartz vector (all
moments finite) in the Fock space `PairFock E s t'` of `(W₁, V')`. There are `κ` and a Schwartz
vector `Λ` for `(X, V')` whose slice at an adelic matrix with infinite components `x w`
(`atRealPlace`) is `σ (x, 0) * ‖∏ w, det (x w) ^ N w‖ ^ 2 * κ` times `v`, and whose slice at 0 for
`D.symm`, the splitting with the two isotropic frames exchanged, is `v`. -/
lemma exists_isSchwartzVector_realSlice_bump (D : X.Splitting W₁ b) [IsBaseAdapted D] {t' : b → ℤˣ}
    (V' : Space E b t') (N : InfinitePlace E → ℕ)
    {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (hσ_cpt : HasCompactSupport σ) (hσ₀ : ∀ x : InfinitePlace E → Matrix (b ⊕ n) b ℂ, 0 ≤ σ x)
    (hσ₁ : σ (fun _ : InfinitePlace E ↦ fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ)) = 1)
    {v : PairFock E s t'} (hv : IsSchwartzVector v) :
    ∃ (κ : ℂ) (Λ : PairFock E r t'),
      IsSchwartzVector Λ ∧
      realSlice D.symm V' 0 Λ = v ∧
      ∀ x : Matrix b b (𝔸 E), realSlice D V' x Λ =
        ((σ (fun w : InfinitePlace E ↦ fromRows (1 : Matrix b b ℂ) 0 * atRealPlace x w) *
          ‖∏ w : InfinitePlace E, (atRealPlace x w).det ^ N w‖ ^ 2) • κ) • v := by
  let C := placeMatrices E b b
  let τ (x : InfinitePlace E → Matrix b b ℂ) : ℝ :=
    σ (fun w ↦ fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) * x w) * ‖∏ w, (x w).det ^ N w‖ ^ 2
  have τ_smooth : ContDiff ℝ ∞ (τ ∘ C) := by
    refine .mul (by fun_prop) (.norm_sq ℂ ?_)
    simp only [det_apply]
    fun_prop
  -- `x` is recovered from the frame `(x, 0)`, which lies in the support of `σ`.
  have τ_cpt : HasCompactSupport (τ ∘ C) := by
    refine (hσ_cpt.image_of_continuous (C.symm ∘ fun (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) w ↦
      (fromRows 1 0 : Matrix (b ⊕ n) b ℂ)ᴴ * x w)).closure_of_subset fun x hx ↦
      ⟨fun w ↦ fromRows 1 0 * C x w, subset_closure (left_ne_zero_of_mul hx), ?_⟩
    simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  obtain ⟨κ, Λ, hΛ, hΛ₀, hΛ_slice⟩ := exists_isSchwartzVector_realSlice_eq D V' (τ ∘ C) τ_smooth hv
    τ_cpt
    (fun _ ↦ mul_nonneg (hσ₀ _) (sq_nonneg _)) (C.symm fun _ ↦ 1) (by simp [τ, hσ₁])
  exact ⟨κ, Λ, hΛ, hΛ₀, fun x ↦ by simp [realSlice_eq_slice_placeMatrices_symm, hΛ_slice, τ, C]⟩

/-- Let `σ` be smooth with compact support, `z` and `k` smooth maps on frames, and `v`, `v₁`
Schwartz vectors (all moments finite) in the Fock spaces `PairFock` of `(W₁, V')` and `(W₁, W₁)`.
Then some Schwartz vector `Φ` in the Fock space of `(X, V' ⊕ W₁)` has slice
`exchangeSection σ k j M κ v v₁ y x` at every adelic matrix with infinite components `x`, for
`y = z ∘ x`. -/
lemma exists_isSchwartzVector_exchangeSection (D : X.Splitting W₁ b) [IsBaseAdapted D] {t' : b → ℤˣ}
    (V' : Space E b t') {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (hσ_cpt : HasCompactSupport σ)
    {k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    (hk : ContDiff ℝ ∞ fun y : Matrix (b ⊕ n) b ℂ ↦ (k y : Matrix (b ⊕ n) (b ⊕ n) ℂ))
    {z : Matrix (b ⊕ n) b ℂ → Matrix (b ⊕ n) b ℂ} (hz : ContDiff ℝ ∞ z)
    (j : ℕ) (M : InfinitePlace E → ℕ) (κ : ℂ) {v : PairFock E s t'} {v₁ : PairFock E s s}
    (hv : IsSchwartzVector v) (hv₁ : IsSchwartzVector v₁) :
    ∃ Φ : fockSpace (realSigns E (homSigns r (t' ⊕ᵥ s))),
      IsSchwartzVector Φ ∧
      ∀ x : Matrix (b ⊕ n) b (𝔸 E), realSlice D (V'.sum W₁) x Φ =
        exchangeSection σ k j M κ v v₁ (z ∘ atRealPlace x) (atRealPlace x) := by
  let C := placeMatrices E (b ⊕ n) b
  let S (y : Matrix (b ⊕ n) b ℂ) : Matrix (b ⊕ n) (b ⊕ n) ℂ := k y
  replace hk : ContDiff ℝ ∞ S := hk
  let w (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) := unitaryMovedFrame k (z ∘ x) x
  -- The scalar of the section, times the determinant factor of `realPairWeil`.
  let τ (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) : ℂ := (σ (z ∘ x) * σ (w x)) •
    ((∏ p, star (w x p).toRows₁.det ^ (M p * 2)) * κ *
      ((∏ p, (S (z (x p))).det ^ j) * ∏ p, star (S (z (x p))).det ^ M p))
  have section_eq (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) :
      exchangeSection σ k j M κ v v₁ (z ∘ x) x = τ x • realWeil (pairHomInf (1, k ∘ z ∘ x))
        (realBoxProd (realSigns_comp_split (homSigns_sum_target signs_comp_refl)) v v₁) := by
    simp [exchangeSection, τ, w, S, realPairWeil, ← smul_assoc, -real_smul, zpow_sub₀, division_def,
      inv_eq_conj, GeneralLinearGroup.det_ne_zero, prod_mul_distrib]
  -- `τ` is `σ * σ` times a polynomial in the entries of `x` and `k (z x)` and their conjugates.
  have τ_smooth : ContDiff ℝ ∞ (τ ∘ C) := by
    have w_eq (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) : w x = fun p ↦
        signMatrix (t' ⊕ᵥ s) * (S (z (x p)))ᴴ * signMatrix (t' ⊕ᵥ s) * x p :=
      funext fun p ↦ congrArg (· * x p) (U.coe_inv IsHermitianInvolution.mul_self _)
    simp [τ, w_eq, comp_def, det_apply, -real_smul, Matrix.mul_assoc]
    fun_prop
  -- On the support, `x = k y * w x` with `y = z ∘ x` and `w x` in the support of `σ`.
  have τ_cpt : HasCompactSupport (τ ∘ C) := by
    refine ((hσ_cpt.prod hσ_cpt).image_of_continuous
      (C.symm ∘ fun (p, q) v ↦ S (p v) * q v)).closure_of_subset fun x hx ↦ ?_
    have hσ_ne : σ (z ∘ C x) ≠ 0 ∧ σ (w (C x)) ≠ 0 := mul_ne_zero_iff.1 (left_ne_zero_of_smul hx)
    exact ⟨(z ∘ C x, w (C x)), closure_prod_eq.le (subset_closure hσ_ne),
      by simp [S, w, unitaryMovedFrame]⟩
  -- The entries of the unitary matrix are entries of `k (z x)` or `0`.
  have u_smooth : ContDiff ℝ ∞ fun x ↦ (pairHomInf (1, k ∘ z ∘ C x) : USign
      (realSigns E (homSigns s (t' ⊕ᵥ s)))).val.val := by
    refine contDiff_pi' fun p ↦ contDiff_pi' fun q ↦ ?_
    suffices ContDiff ℝ ∞ fun x ↦
        if p.1 = q.1 then if p.2.2 = q.2.2 then S (z (C x p.1)) p.2.1 q.2.1 else 0 else 0 by
      simpa [pairHomInf, blockDiagonal_apply, pairHom, S, Matrix.one_apply]
    split_ifs <;> fun_prop
  obtain ⟨Φ, hΦ, hΦ_slice⟩ := exists_isSchwartzVector_slice_eq
    (isAdapted_homSource D (V'.sum W₁)).mixedModel
    τ_smooth τ_cpt u_smooth (isSchwartzVector_realBoxProd _ hv hv₁)
  refine ⟨Φ, hΦ, fun x ↦ ?_⟩
  rw [realSlice_eq_slice_placeMatrices_symm, hΦ_slice, section_eq, Function.comp_apply,
    C.apply_symm_apply]

omit [WeilData E] in
/-- For families `y`, `x` of frames, one for each infinite place `w`, and vectors `v₀`, `v₁` in the
Fock spaces `PairFock` of the signs `(s, t')` and `(s, s)`, the value `exchangeSection σ k j M κ v₀
v₁ y x` is `(σ y * σ x' * κ * ∏ w, conj (det (x' w)₁) ^ (2 * M w)) • ω (1, k ∘ y) (v₀ ⊠ v₁)`, where
`x' w = (k (y w))⁻¹ * x w` (`unitaryMovedFrame`), `(x' w)₁` is its upper square block, `ω` is the
real Weil representation `realPairWeil` twisted by `det ^ (j - M w)` on the unitary group of `t' ⊕ᵥ
s`, and `⊠` is the external product `realBoxProd`. Write `frameProjection γ x` for the projection of
the frame `(1, 0)` to the span of the frame `x`, with `γ` in the place of the inversion of the Gram
matrix. If `γ` inverts the Gram matrices of the frames on which `σ` is nonzero and of each `x w`,
then in the section with second argument `A w = x w * C w` (`C w` invertible) and first argument the
projections for `A`, these may be replaced by the projections for `x`. -/
lemma exchangeSection_frameProjection_mul {t' : b → ℤˣ}
    {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ} {γ : Matrix b b ℂ → Matrix b b ℂ}
    (k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ))
    (hγ_supp : ∀ y : InfinitePlace E → Matrix (b ⊕ n) b ℂ, σ y ≠ 0 → ∀ w : InfinitePlace E,
      γ ((y w)ᴴ * signMatrix (t' ⊕ᵥ s) * y w) = ((y w)ᴴ * signMatrix (t' ⊕ᵥ s) * y w)⁻¹)
    (j : ℕ) (M : InfinitePlace E → ℕ) (κ : ℂ) (v₀ : PairFock E s t') (v₁ : PairFock E s s)
    (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) (C : InfinitePlace E → GL b ℂ)
    (hγx : ∀ w : InfinitePlace E,
      γ ((x w)ᴴ * signMatrix (t' ⊕ᵥ s) * x w) = ((x w)ᴴ * signMatrix (t' ⊕ᵥ s) * x w)⁻¹) :
    exchangeSection σ k j M κ v₀ v₁
        (frameProjection (t' := t') (s := s) γ ∘ fun w : InfinitePlace E ↦ x w * (C w).val)
        (fun w : InfinitePlace E ↦ x w * (C w).val) =
      exchangeSection σ k j M κ v₀ v₁ (frameProjection (t' := t') (s := s) γ ∘ x)
        (fun w : InfinitePlace E ↦ x w * (C w).val) := by
  set A : InfinitePlace E → Matrix (b ⊕ n) b ℂ := fun w ↦ x w * (C w).val
  rcases forall_or_exists_not fun y ↦ σ (unitaryMovedFrame k y A) = 0 with hσ_zero | ⟨y, hy⟩
  · simp [exchangeSection, hσ_zero]
  -- It is enough to see that `A w` and `x w` give the same projection.
  congr 1
  funext w
  have hγA : γ ((A w)ᴴ * signMatrix (t' ⊕ᵥ s) * A w) = ((A w)ᴴ * signMatrix (t' ⊕ᵥ s) * A w)⁻¹ := by
    simpa only [unitaryMovedFrame, U.gram_invariant] using hγ_supp _ hy w
  simp only [Function.comp_apply, frameProjection, hγA, hγx, A]
  exact mul_gram_inv_mul_of_isUnit_det _ (x w) _ (isUnits_det_units _)

omit [CMType E] [WeilData E] in
/-- If each frame `(h v)⁻¹ * fromRows 1 0` is `k v * fromRows 1 0 * c` with `c` carrying the form
with signs `t'` to its Gram matrix, then `c` is a unitary `u v`, and for some unitary `q v` one has
`diag(u v, (q v)⁻¹) * h v * k v = 1`. -/
lemma exists_unitary_pair_of_frame {t' : b → ℤˣ}
    (h k : InfinitePlace E → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ))
    (hframe : ∀ v : InfinitePlace E, ∃ c : Matrix b b ℂ,
      (k v : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) * c =
        (↑(h v)⁻¹ : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) ∧
      cᴴ * signMatrix t' * c = signMatrix t') :
    ∃ (u : InfinitePlace E → U (signMatrix t' : Matrix b b ℂ))
      (q : InfinitePlace E → U (signMatrix s : Matrix n n ℂ)),
      ∀ v : InfinitePlace E,
        (k v : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) *
            (u v : Matrix b b ℂ) =
          (↑(h v)⁻¹ : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) ∧
        U.sum (signMatrix_sum t' s) (u v, (q v)⁻¹) * h v * k v = 1 := by
  choose c hc c_gram using hframe
  choose u hu_eq using fun v ↦ exists_U_coe_eq (c_gram v)
  simp only [← hu_eq] at hc
  choose q hq using fun v ↦ exists_sum_one_eq_mul_mul_sum (hc v)
  refine ⟨u, q, fun v ↦ ⟨hc v, ?_⟩⟩
  have hhk : h v * k v = U.sum (signMatrix_sum t' s) ((1, q v) * (u v, 1)⁻¹) := by
    rw [map_mul, map_inv, hq, mul_inv_cancel_right]
  simp [mul_assoc, hhk, ← map_mul, Prod.mk_one_one]

omit [WeilData E] in
/-- Let `𝔠` be a tame character (`SplitTameChar`) of weight `μ ≥ 0` with automorphic character
`ν = 𝔠.character` of the norm-one ideles, so that `ν` has weight `μ w` at each infinite place `w`,
and let `z` be the idele with infinite part `ζ` and finite part 1. Then the product of the
`conj (ζ w) ^ (2 μ w)` is `‖∏ ζ w ^ (j + μ w)‖ ^ 2 / (ν(z / z̄) |z| ^ j)`. -/
lemma prod_conj_pow_eq_norm_div {μ : InfinitePlace E → ℕ}
    (𝔠 : SplitTameChar E fun w : InfinitePlace E ↦ (μ w : ℤ)) (j : ℕ) (ζ : (InfinitePlace E → ℂ)ˣ) :
    ∏ w : InfinitePlace E, star (ζ.val w) ^ (μ w * 2) =
      (‖∏ w : InfinitePlace E, ζ.val w ^ (j + μ w)‖ ^ 2 : ℝ) /
        ((𝔠.character.baseChange.val (ζ.map (MonoidHom.inl (InfinitePlace E → ℂ) (𝔸f E))) : ℂ) *
          √(ideleAbs (ζ.map (MonoidHom.inl (InfinitePlace E → ℂ) (𝔸f E)))) ^ (2 * j)) := by
  set z := ζ.map (MonoidHom.inl (InfinitePlace E → ℂ) (𝔸f E))
  set P : ℂ := ∏ w, ζ.val w with hP
  set Q : ℂ := ∏ w, ζ.val w ^ μ w with hQ
  have hP₀ : (‖P‖ : ℂ) ≠ 0 := by simp [hP, prod_eq_zero_iff, (ζ.isUnit.apply _).ne_zero]
  have hQ₀ : Q ≠ 0 := by simp [hQ, prod_eq_zero_iff, (ζ.isUnit.apply _).ne_zero]
  have h_char : (𝔠.character.baseChange.val z : ℂ) = Q ^ 2 / ‖Q‖ ^ 2 := by
    simp [z, hQ, 𝔠.hasWeight.baseChange_apply_inf, _root_.zpow_mul, div_pow, ← prod_pow,
      pow_right_comm _ 2]
  have h_abs : √(ideleAbs z) = ‖P‖ := by
    simp [z, hP, ideleAbs_eq_prod_of_v_eq_one, prod_pow, prod_nonneg]
  have h_lhs : ∏ w, star (ζ.val w) ^ (μ w * 2) = star Q ^ 2 := by simp [hQ, pow_mul, prod_pow]
  have h_num : ∏ w, ζ.val w ^ (j + μ w) = P ^ j * Q := by
    simp [hP, hQ, pow_add, prod_mul_distrib, prod_pow]
  have h_conj : star Q = ‖Q‖ ^ 2 / Q := by rw [eq_div_iff hQ₀, star_def, conj_mul']
  push_cast [h_lhs, h_char, h_abs, h_num, h_conj, norm_mul, norm_pow]
  field

omit [WeilData E] in
/-- For families `y`, `x` of frames, one for each infinite place `w`, and vectors `v`, `v₁` in the
Fock spaces `PairFock` of the signs `(s, t')` and `(s, s)`, the value `exchangeSection σ k j M κ v
v₁ y x` is `(σ y * σ x' * κ * ∏ w, conj (det (x' w)₁) ^ (2 * M w)) • ω (1, k ∘ y) (v ⊠ v₁)`, where
`x' w = (k (y w))⁻¹ * x w` (`unitaryMovedFrame`), `(x' w)₁` is its upper square block, `ω` is the
real Weil representation `realPairWeil` twisted by `det ^ (j - M w)` on the unitary group of `t' ⊕ᵥ
s`, and `⊠` is the external product `realBoxProd` (its first argument is the proof that the signs
split accordingly). Suppose that `g * (k ∘ y) = 1` and `x' = (B, 0)` whenever `σ y ≠ 0`. Then `ω (1,
g)` carries this value to `σ y * σ (B, 0) * κ * ∏ w, conj (det (B w)) ^ (2 * M w)` times `v ⊠ v₁`.
-/
lemma realPairWeil_exchangeSection {t' : b → ℤˣ} {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ}
    {k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    (j : ℕ) (M : InfinitePlace E → ℕ) (κ : ℂ) (v : PairFock E s t') (v₁ : PairFock E s s)
    {y x : InfinitePlace E → Matrix (b ⊕ n) b ℂ} {g : GInf E (t' ⊕ᵥ s)}
    {B : InfinitePlace E → Matrix b b ℂ} (hg : σ y ≠ 0 → g * (k ∘ y) = 1)
    (hx : σ y ≠ 0 → unitaryMovedFrame k y x = fun w : InfinitePlace E ↦ fromRows (B w) 0) :
    realPairWeil (fun w : InfinitePlace E ↦ (j : ℤ) - M w) 0 (1, g)
        (exchangeSection σ k j M κ v v₁ y x) =
      ((σ y * σ fun w : InfinitePlace E ↦ fromRows (B w) 0) •
          ((∏ w : InfinitePlace E, star (B w).det ^ (M w * 2)) * κ)) •
        realBoxProd (realSigns_comp_split (homSigns_sum_target signs_comp_refl)) v v₁ := by
  by_cases hσ : σ y = 0
  · simp [exchangeSection, hσ]
  rw [exchangeSection, map_smul, ← mul_apply_eq_comp, ← map_mul, hx hσ]
  simp [hg hσ, Prod.mk_one_one]

omit [WeilData E] in
/-- Let `h` be a point of `GInf E (t' ⊕ᵥ s)`, the unitary group for the signs `t' ⊕ᵥ s` at the
infinite places. Let `u`, `q` be points of `GInf E t'` and `GInf E s`. All three are completed by
`1` at the finite places to adelic points, and `G.sum` is the block sum of `u` and `q`. At each
infinite place `w`, the adelic matrix `(diag(u, q) * h)⁻¹ * fromRows B 0` has component
`h⁻¹ * fromRows 1 0 * u⁻¹ * B`. -/
lemma atRealPlace_inv_sum_mul_fromRows {t' : b → ℤˣ} (u : GInf E t') (q : GInf E s)
    (h : GInf E (t' ⊕ᵥ s)) (B : Matrix b b (𝔸 E)) (w : InfinitePlace E) :
    atRealPlace (G.adeleMatrix ((G.sum ((u, 1), q, 1)).1 * h, 1)⁻¹ * fromRows (m₂ := n) B 0) w =
      (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) *
        ((↑(u⁻¹ w) : Matrix b b ℂ) * atRealPlace B w) := by
  rw [← Matrix.mul_assoc]
  ext
  -- `↓`: expand the products into sums of entries before the factors are rewritten.
  simp [G.sum, ↓mul_apply, Prod.fst_sum, U.sum, blockGL, Matrix.one_apply]

/-- The Gram matrix of the frame `fromRows 1 0` of the first summand, for the form with signs
`t' ⊕ᵥ s`, is the form with signs `t'`. -/
lemma gram_signMatrix_fromRows_one_zero (t' : b → ℤˣ) (s : n → ℤˣ) :
    (fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ))ᴴ * signMatrix (t' ⊕ᵥ s) *
      fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) = signMatrix t' := by
  simp [← signMatrix_sum, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromBlocks, fromCols_mul_fromRows]

omit [WeilData E] in
/-- Let `γ`, `k`, `σ` be smooth Witt data near `x₀ = fromRows 1 0` for the form with signs `t' ⊕ᵥ s`
(`IsWittBump`): for each member `z` of a family of frames where the bump function `σ` is nonzero,
`γ` inverts the Gram matrix of `z` and `z` lies in the span of `k z * x₀`, with `k z` unitary. Let
`y w = frameProjection γ (x w)` be the projection of `x₀` to the span of the frame `x w`, with `γ`
in the place of the inverse Gram matrix. If `σ y ≠ 0`, then `x w = k (y w) * x₀ * c` for a matrix
`c` that carries the form with signs `t'` to the Gram matrix of `x w`. -/
lemma IsWittBump.exists_mul_fromRows_mul_eq_of_ne_zero
    {t' : b → ℤˣ} {γ : Matrix b b ℂ → Matrix b b ℂ}
    {k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ}
    (hW : IsWittBump (signMatrix (t' ⊕ᵥ s)) (fromRows 1 0) γ k σ)
    {x : InfinitePlace E → Matrix (b ⊕ n) b ℂ}
    (hx : σ (frameProjection (t' := t') (s := s) γ ∘ x) ≠ 0) (w : InfinitePlace E) :
    ∃ c : Matrix b b ℂ,
      (k (frameProjection (t' := t') (s := s) γ (x w)) : Matrix (b ⊕ n) (b ⊕ n) ℂ) *
        fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) * c = x w ∧
      cᴴ * signMatrix t' * c = (x w)ᴴ * signMatrix (t' ⊕ᵥ s) * x w := by
  obtain ⟨c, hc⟩ := hW.exists_mul_eq _ hx w
  rw [← gram_signMatrix_fromRows_one_zero t' s]
  exact exists_mul_mul_eq_and_gram_eq _ hc (hW.det_gram_ne_zero _ hx w)

omit [WeilData E] in
/-- Let `γ`, `k`, `σ` be smooth Witt data near `x₀ = fromRows 1 0` for the form with signs `t' ⊕ᵥ s`
(`IsWittBump`); in particular `γ` inverts the Gram matrix of `x₀` and the bump function `σ` is `1`
at the constant family `x₀`. For `h` near `1` in `GInf`, the product of the unitary groups of the
form over the infinite places, `σ` does not vanish at the family of projections `frameProjection γ`
of `x₀` to the spans of the frames `(h w)⁻¹ * x₀`, formed with `γ` in the place of the inverse Gram
matrix. -/
lemma IsWittBump.eventually_bump_frameProjection_ne_zero
    {t' : b → ℤˣ} {γ : Matrix b b ℂ → Matrix b b ℂ}
    {k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ}
    (hW : IsWittBump (signMatrix (t' ⊕ᵥ s)) (fromRows 1 0) γ k σ) :
    ∀ᶠ h : GInf E (t' ⊕ᵥ s) in nhds 1,
      σ (frameProjection (t' := t') (s := s) γ ∘ fun w : InfinitePlace E ↦
        (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * (fromRows 1 0 : Matrix (b ⊕ n) b ℂ)) ≠ 0 := by
  have γ_smooth : ContDiff ℝ ∞ γ := hW.contDiff_inv
  have σ_smooth : ContDiff ℝ ∞ σ := hW.contDiff_bump
  let x₀ : Matrix (b ⊕ n) b ℂ := fromRows 1 0
  have proj_base : frameProjection (t' := t') (s := s) γ x₀ = x₀ := by
    change x₀ * (γ (x₀ᴴ * signMatrix (t' ⊕ᵥ s) * x₀) * (x₀ᴴ * signMatrix (t' ⊕ᵥ s) * x₀)) = x₀
    rw [hW.inv_gram_base, gram_signMatrix_fromRows_one_zero]
    simp [IsHermitianInvolution.det_ne_zero]
  refine (Continuous.tendsto (by fun_prop [frameProjection]) 1).eventually_ne ?_
  simp [comp_def, x₀, proj_base, hW.bump_base]

/-- Let `γ`, `k`, `σ` be smooth Witt data near `x₀ = fromRows 1 0` (`IsWittBump`): for frames `y`
where the bump function `σ` is nonzero, `y` lies in the span of `k y * x₀` with `k y` unitary, and
`γ` inverts the Gram matrix of `y`; `frameProjection γ x` is the projection of `x₀` to the span of
`x`, formed with `γ`. Let `D` be an adapted Witt decomposition of the Hermitian space `X` as `W₁`
plus `card b` hyperbolic planes, let `W₁` have rank `2 j` and split off a hyperbolic plane by `D₁`,
let `V'` have rank `card b`, and let `𝔠` be a tame character of weight `μ`, with automorphic
character `ν = 𝔠.character`. Let `v₁` be a Schwartz vector (all moments finite). Suppose that the
slice of `Φ` at `x` is `exchangeSection` at `x` and `y = frameProjection γ ∘ x`, namely
`(σ y * σ x' * κ * ∏ w, conj (det (x' w)₁) ^ (2 * μ w)) • ω (1, k ∘ y) (v ⊠ v₁)`, where
`x' w = (k (y w))⁻¹ * x w` (`unitaryMovedFrame`), `(x' w)₁` is its upper square block, `ω` is the
real Weil representation `realPairWeil` twisted by `det ^ (j - μ w)` on the unitary group of
`t' ⊕ᵥ s`, and `⊠` is the external product `realBoxProd`, and that the slice of `Λ` at `x` is
`σ (x, 0) * ‖∏ w, det (x w) ^ (j + μ w)‖ ^ 2 * κ` times `v`. Then `IsPeriodIdentity` holds: for each
`h` at infinity there is `p` in `U V' × U W₁` such that for all invertible `B` the theta functional
of the slice of `Φ` at `(p h)⁻¹ (B, 0)`, moved by `p h` and integrated over the adelic quotient of
`U W₁`, is `ρ h * I₀ / (ν(z / z̄) |z| ^ j)` times the theta functional of the slice of `Λ` at `B`.
Here `z` is the idele with infinite part `det B` and finite part 1, `ρ h` is `σ` at the projections
of `x₀` to the spans of `(h w)⁻¹ * x₀`, and the period `I₀` is the value at `1` of the theta
integral `thetaLarge` over `U W₁` with real part `v₁` and, at the ramified places of `𝔠`, the
function `stdColDatum`. -/
lemma IsWittBump.isPeriodIdentity {t' : b → ℤˣ} {γ : Matrix b b ℂ → Matrix b b ℂ}
    {k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ}
    (hW : IsWittBump (signMatrix (t' ⊕ᵥ s)) (fromRows 1 0) γ k σ)
    (D : X.Splitting W₁ b) [IsBaseAdapted D] {t : a → ℤˣ} {W : Space E a t}
    (D₁ : W₁.Splitting W Unit) [IsBaseAdapted D₁] (V' : Space E b t') {j : ℕ}
    (hj : Fintype.card n = 2 * j) {μ : InfinitePlace E → ℕ}
    (𝔠 : SplitTameChar E fun w : InfinitePlace E ↦ (μ w : ℤ)) {κ : ℂ} {v : PairFock E s t'}
    {v₁ : PairFock E s s} (hv₁ : IsSchwartzVector v₁) {Φ : PairFock E r (t' ⊕ᵥ s)}
    {Λ : PairFock E r t'}
    (hΦ : ∀ x : Matrix (b ⊕ n) b (𝔸 E), realSlice D (V'.sum W₁) x Φ = exchangeSection σ k j μ κ v v₁
      (frameProjection (t' := t') (s := s) γ ∘ atRealPlace x) (atRealPlace x))
    (hΛ : ∀ x : Matrix b b (𝔸 E), realSlice D V' x Λ =
      ((σ (fun w : InfinitePlace E ↦ fromRows (1 : Matrix b b ℂ) 0 * atRealPlace x w) *
        ‖∏ w : InfinitePlace E, (atRealPlace x w).det ^ (j + μ w)‖ ^ 2) • κ) • v) :
    IsPeriodIdentity X D V' 𝔠 Φ Λ
      (fun h : GInf E (t' ⊕ᵥ s) ↦ σ (frameProjection (t' := t') (s := s) γ ∘
        fun w : InfinitePlace E ↦ (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) *
          fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ)))
      (thetaLarge W₁ W₁ 𝔠 v₁ (stdColDatum 𝔠.semilocalChar 1) 1) := by
  -- Fix `h` and let `y` be these projections. If `σ y ≠ 0`, then `h * k y` keeps the span of `x₀`,
  -- so it is block diagonal. Its blocks give a point at which the moved slice of `Φ` is a multiple
  -- of the product vector of `v` and `v₁`.
  intro h
  let x₀ : Matrix (b ⊕ n) b ℂ := fromRows 1 0
  let x₁ (w : InfinitePlace E) : Matrix (b ⊕ n) b ℂ := (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * x₀
  have gram₁ (w : InfinitePlace E) : (x₁ w)ᴴ * signMatrix (t' ⊕ᵥ s) * x₁ w = signMatrix t' := by
    rw [U.gram_invariant, gram_signMatrix_fromRows_one_zero]
  have γ_inv (w : InfinitePlace E) : γ ((x₁ w)ᴴ * signMatrix (t' ⊕ᵥ s) * x₁ w) =
      ((x₁ w)ᴴ * signMatrix (t' ⊕ᵥ s) * x₁ w)⁻¹ := by
    rw [gram₁, ← gram_signMatrix_fromRows_one_zero t' s, hW.inv_gram_base]
  let y : InfinitePlace E → Matrix (b ⊕ n) b ℂ := frameProjection (t' := t') (s := s) γ ∘ x₁
  obtain ⟨u, q, huq⟩ : ∃ (u : GInf E t') (q : GInf E s), σ y ≠ 0 → ∀ w : InfinitePlace E,
      (k (y w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * x₀ * (u w : Matrix b b ℂ) = x₁ w ∧
        U.sum (signMatrix_sum t' s) (u w, (q w)⁻¹) * h w * k (y w) = 1 := by
    by_cases hσ : σ y = 0
    · simp [hσ]
    have hframe (w : InfinitePlace E) : ∃ c : Matrix b b ℂ,
        (k (y w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * x₀ * c = x₁ w ∧
          cᴴ * signMatrix t' * c = signMatrix t' :=
      (hW.exists_mul_fromRows_mul_eq_of_ne_zero hσ w).imp fun c hc ↦
        hc.imp_right (·.trans (gram₁ w))
    obtain ⟨u, q, huq⟩ := exists_unitary_pair_of_frame h (k ∘ y) hframe
    exact ⟨u, q, fun _ ↦ huq⟩
  refine ⟨((u, 1), q⁻¹, 1), fun B β f x g y' ↦ ?_⟩
  -- The slice of `Φ` is read at `A = h⁻¹ x₀ u⁻¹ B`, which spans the same space as `x₁ = h⁻¹ x₀`.
  let C (w : InfinitePlace E) : GL b ℂ := (u⁻¹ w).val * B.map (evalInf w)
  have C_val (w : InfinitePlace E) :
      (C w).val = (↑(u⁻¹ w) : Matrix b b ℂ) * atRealPlace B.val w := rfl
  let p : GInf E (t' ⊕ᵥ s) := (G.sum ((u, 1), q⁻¹, 1)).1 * h
  have re_A : atRealPlace (G.adeleMatrix (p, 1)⁻¹ * fromRows (m₂ := n) B.val 0) =
      fun w ↦ x₁ w * (C w).val := funext (atRealPlace_inv_sum_mul_fromRows u q⁻¹ h B.val)
  -- The group elements cancel, the moved frame is `(B, 0)`, and the period splits off `v₁`.
  have cancel (hσ : σ y ≠ 0) : p * (k ∘ y) = 1 := funext fun w ↦ (huq hσ w).2
  have moved_frame (hσ : σ y ≠ 0) : unitaryMovedFrame k y (fun w ↦ x₁ w * (C w).val) =
      fun w ↦ fromRows (atRealPlace B.val w) 0 :=
    funext fun w ↦ by simp [unitaryMovedFrame, C_val, ← (huq hσ w).1, Matrix.mul_assoc, x₀]
  have weight_eq : (fun w ↦ (Fintype.card n : ℤ) / 2 - μ w) = fun w ↦ (j : ℤ) - μ w := by simp [hj]
  rw [hΦ, hΛ, re_A, exchangeSection_frameProjection_mul k hW.inv_gram j μ κ v v₁ x₁ C γ_inv,
    weight_eq, realPairWeil_exchangeSection j μ κ v v₁ cancel moved_frame]
  simp only [map_smul, smul_eq_mul, integral_const_mul, thetaOnRealData_boxProd_eq_mul]
  -- The factor of `v₁` integrates to a theta integral that does not depend on `g`.
  rw [← thetaLarge_eq_apply_one_of_even_rank D₁ 𝔠 (Dvd.intro j hj.symm) hv₁ g]
  simp only [thetaIntegral, ← infiniteDet_apply, y, x₁, x₀, prod_conj_pow_eq_norm_div 𝔠 j, hj,
    real_smul, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
  push_cast
  ring

/-- Let `D` be an adapted Witt decomposition of the Hermitian space `X` (signs `r`) as `W₁` (signs
`s`) plus `card b` hyperbolic planes, where `W₁` has even rank and an adapted splitting `D₁` along
an isotropic line, and let `V'` be a space with basis indexed by `b` and signs `t'`. Let `v` and
`v₁` be Schwartz vectors for `(W₁, V')` and `(W₁, W₁)`. Then there are vectors `Φ` for
`(X, V' ⊕ W₁)` and `Λ` for `(X, V')` with two properties. The slice `realSlice` of `Λ` at `0`, its
value at `0` in the mixed Schrödinger–Fock model of the splitting `D.symm` with the isotropic frames
exchanged, is `v`. And `RowColExchangeIdentity` holds: `Φ`, `Λ` are Schwartz and there is a real `C`
such that for each tame character `𝔠` of weight `μ` some `c : ℂ` has `C * ‖c‖ ^ 2 = lValueProdInt 𝔠
(rk (V' ⊕ W₁) - rk X / 2) * equalRankThetaRatio W₁ 𝔠 v₁`, and for all integral `z` the theta
integral of `Φ` and the row datum of `z` is `c` times that of `Λ` and the column datum of `z`. With
`χ` the character of `𝔠` at its ramified places, these data are `x ↦ χ⁻¹ (det)` of the matrix with
the rows of `z` and `x` ordered by `e`, and `x ↦ χ⁻¹ (det (z * x))`. -/
theorem exists_rowColExchangeIdentity_sum (D : X.Splitting W₁ b) [IsBaseAdapted D] {t : a → ℤˣ}
    {t' : b → ℤˣ} {W : Space E a t} (D₁ : W₁.Splitting W Unit) [IsBaseAdapted D₁]
    (V' : Space E b t') (e : b ⊕ b ⊕ n ≃ m) (hn : 2 ∣ Fintype.card n) (μ : InfinitePlace E → ℤ)
    {v : PairFock E s t'} {v₁ : PairFock E s s} (hv : IsSchwartzVector v)
    (hv₁ : IsSchwartzVector v₁) :
    ∃ (Φ : fockSpace (realSigns E (homSigns r (t' ⊕ᵥ s)))) (Λ : PairFock E r t'),
      realSlice D.symm V' 0 Λ = v ∧
      RowColExchangeIdentity X (V'.sum W₁) V' μ e Φ Λ fun 𝔠 : SplitTameChar E μ ↦
        equalRankThetaRatio W₁ 𝔠 v₁ := by
  -- A smooth unitary `k y` moves the span of `x₀ = fromRows 1 0` onto that of a nearby frame `y`.
  -- The vectors have bump functions as slices, the one for `V' ⊕ W₁` twisted by `k`, and
  -- `rowColExchangeIdentity_of_periods` compares periods.
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Fintype.card n = 2 * j := exists_eq_mul_right_of_dvd hn
  obtain ⟨γ, k, σ, hW⟩ := exists_contDiff_witt_and_bump (ι := InfinitePlace E)
    (J := signMatrix (t' ⊕ᵥ s)) (x₀ := fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ)) isHermitian
    (by simp [gram_signMatrix_fromRows_one_zero, IsHermitianInvolution.det_ne_zero])
  let z : Matrix (b ⊕ n) b ℂ → Matrix (b ⊕ n) b ℂ := frameProjection (t' := t') (s := s) γ
  have γ_smooth : ContDiff ℝ ∞ γ := hW.contDiff_inv
  have z_smooth : ContDiff ℝ ∞ z := by fun_prop [frameProjection]
  let M : InfinitePlace E → ℕ := Int.toNat ∘ μ
  obtain ⟨κ, Λ, hΛ, Λ_zero, Λ_slice⟩ :=
    exists_isSchwartzVector_realSlice_bump D V' (fun w ↦ j + M w)
      hW.contDiff_bump hW.hasCompactSupport_bump hW.bump_nonneg hW.bump_base hv
  obtain ⟨Φ, hΦ, Φ_slice⟩ := exists_isSchwartzVector_exchangeSection D V' hW.contDiff_bump
    hW.hasCompactSupport_bump hW.contDiff_unitary z_smooth j M κ hv hv₁
  -- Where the slice of `Φ` is nonzero, the frame is `k x₀ c`, and `c` represents its Gram matrix.
  have h_vanish : SlicesVanishOutside D (V'.sum W₁) t' Φ := fun x hx w ↦ by
    have hσ : σ (z ∘ atRealPlace x) ≠ 0 := fun h₀ ↦ hx (by simp [Φ_slice, exchangeSection, h₀])
    obtain ⟨c, -, hc⟩ := hW.exists_mul_fromRows_mul_eq_of_ne_zero hσ w
    exact ⟨c, hc.trans (gram_atRealPlace _ w)⟩
  let ρ (h : GInf E (t' ⊕ᵥ s)) : ℝ := σ (z ∘ fun w ↦
    (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * (fromRows 1 0 : Matrix (b ⊕ n) b ℂ))
  have h_period (𝔠 : SplitTameChar E μ) :
      IsPeriodIdentity X D V' 𝔠 Φ Λ ρ (thetaLarge W₁ W₁ 𝔠 v₁ (stdColDatum 𝔠.semilocalChar 1)
        1) := by
    lift μ to InfinitePlace E → ℕ using fun w ↦ (𝔠.weight_pos w).le
    exact hW.isPeriodIdentity D D₁ V' hj 𝔠 hv₁ Φ_slice Λ_slice
  exact ⟨Φ, Λ, Λ_zero, rowColExchangeIdentity_of_periods X D D₁ V' _ hn (fun _ ↦ hW.bump_nonneg _)
    hW.eventually_bump_frameProjection_ne_zero hΦ hΛ h_period (.inl h_vanish)⟩

end New.Exchange
