import New.Spanning.Bessel.OpenCellBound

/-!
# One pairing on the open cell, at all places together

Let `X` be a finite family of Bessel systems (`New.BesselSystem`), `W` the tensor product of their
Bessel functions and `W♭` that of their cuts. Let `φ` be a function of `z` of modulus at most `1`,
left invariant under the fixers of the frames and not necessarily a product over the places, such
that `φ (z) W♭ (γ z) ⊗ W♭ (z)^*` vanishes outside boxes. The integral of this product is bounded by
the root of the product of the local bounds `New.pairingBoundSq`, plus the integral of `‖φ‖` times
the norm of the difference between the uncut and cut kernels.

The operator bounds of `New.BesselSystem.exists_isOpenCellBound` multiply over the places, and one
shift that is no worse than the mean gives the bound for `W`.

Notions from other files:
* `BesselSystem`: two continuous functions on the group `G₁`, `besselFn .full` and its cut
  `besselFn .cut`, with values in `ℂ^I`, parameters `b` and `f`, and a degree `deg`.
* `frameBox ρ`: the `y` with `‖y⁻¹ f_a‖ ≤ ρ` for every vector `f_a` of the frame; `besselFixer` is
  the subgroup that fixes these vectors.
* `besselLength y`: the infimum of `‖s y‖ + 1` over `s` in the Bessel subgroup.
* `realFrameGram γ`: the matrix of products `h(f_a, γ f_b)` for the hermitian form `h`;
  `gramDiscReal Z` is `|det Z| ^ 2 - |D| ^ 2`, with `D` the leading minor one size smaller.
* `pairingBoundSq γ deg ρ d`: the square of the bound of the open cell at one place, a power of
  `ρ ^ (9 n) / 𝗀` times `d ^ 2 / (deg * openCellConst * (𝗀 / 2) ^ (k - 1))`, where
  `𝗀 = gramDiscReal (realFrameGram γ)`, `n = 𝔰.n` and `k = 𝔰.k`.

## Main definitions and results

* `New.BesselSystem.pairKernel`: the matrix of `W (y) ⊗ W (γ⁻¹ y)^*`. Its adjoint is the matrix of
  `W (γ⁻¹ y) ⊗ W (y)^*`, which is `New.BesselSystem.piKernel` at `γ⁻¹`.
* `New.BesselSystem.enorm_integral_pairKernel_cut_le`: compact support and the bound for the pairing
  of the cut functions.

## Relation to the literature

See `New.Spanning.Bessel.FillingData` for related work.
-/

open Finset Fintype New.RealPlace MeasureTheory ENNReal Measure ComplexConjugate

namespace New.BesselSystem

variable {ι : Type} [Fintype ι] {𝔰 : Shape} {b : ℝ} {f : ℕ}

/-- The matrix of the operator `W (γ z) ⊗ W (z)^*`, as a vector with the Hilbert–Schmidt norm. Here
`W` is the tensor product, over a finite family `X` of Bessel systems, of the Bessel functions
(`σ = .full`) or of their cuts (`σ = .cut`). The adjoint of `piKernel X σ γ⁻¹ y` is
`pairKernel X σ γ y`. -/
noncomputable def piKernel (X : ι → BesselSystem 𝔰 b f) (σ : FullOrCut) (γ z : ι → 𝔰.G₁) :
    EuclideanSpace ℂ (((v : ι) → (X v).Index) × ((v : ι) → (X v).Index)) :=
  WithLp.toLp 2 fun i ↦ ∏ v : ι, (X v).besselFn σ (γ v * z v) (i.1 v) * conj
    ((X v).besselFn σ (z v) (i.2 v))

lemma continuous_piKernel (X : ι → BesselSystem 𝔰 b f) (σ : FullOrCut) (γ : ι → 𝔰.G₁) :
    Continuous (piKernel X σ γ) := by
  fun_prop [piKernel]

/-- The parameter `b` of a Bessel system is at least `1`, being at least eight times the rank. -/
lemma one_le_b (X : BesselSystem 𝔰 b f) : 1 ≤ b := by
  have h_rank : (𝔰.r : ℝ) = 𝔰.ϱ + (card 𝔰.κ + 1 + 𝔰.ϱ) := by simp
  linarith [X.eight_mul_rank_le]

/-- Where `piKernel X .cut γ z`, the matrix of the cut kernel `W♭ (γ z) ⊗ W♭ (z)^*`, is not zero,
every component of `γ z` satisfies `InCut`: its `besselLength` is at most `b ^ (6 n + 2)`, where
`n = 𝔰.n` is the number of vectors in the frame. -/
lemma inCut_of_piKernel_ne_zero (X : ι → BesselSystem 𝔰 b f) {γ z : ι → 𝔰.G₁}
    (h_ne : piKernel X .cut γ z ≠ 0) (v : ι) : InCut (γ v * z v) b := by
  have h_W : (X v).besselFn .cut (γ v * z v) ≠ 0 := fun h_zero ↦
    h_ne (PiLp.ext fun i ↦ prod_eq_zero (mem_univ v) (by simp [h_zero]))
  exact (X v).isCutPair.inCut_of_ne_zero _ h_W

variable [DecidableEq ι]

/-- For either side `σ` (uncut or cut), the product of `piKernel X σ γ` and a measurable function of
modulus at most `1`, both translated by `t`, is integrable on every compact set. -/
lemma integrableOn_smul_piKernel (X : ι → BesselSystem 𝔰 b f) (σ : FullOrCut) (γ t : ι → 𝔰.G₁)
    {φ : (ι → 𝔰.G₁) → ℂ} (hφ_meas : Measurable φ) (hφ_le : ∀ z : ι → 𝔰.G₁, ‖φ z‖ ≤ 1)
    {A : Set (ι → 𝔰.G₁)} (hA : IsCompact A) :
    IntegrableOn (fun z : ι → 𝔰.G₁ ↦ φ (t * z) • piKernel X σ γ (t * z)) A := by
  have h_cont : Continuous fun z : ι → 𝔰.G₁ ↦ piKernel X σ γ (t * z) :=
    (continuous_piKernel X σ γ).comp (continuous_const_mul t)
  exact (h_cont.continuousOn.integrableOn_compact hA).bdd_smul 1
    (hφ_meas.comp (measurable_const_mul t)).aestronglyMeasurable (.of_forall fun z ↦ hφ_le (t * z))

/-- Let `X v` be Bessel systems with size parameter `b`, one for each place `v`, and `W` the tensor
product of their Bessel functions. Let the frame Gram matrix of each `γ v` have `0 < gramDiscReal`,
and let some `y` have both `y v` and `(γ v)⁻¹ * y v` in `frameBox (ρ v)`, where `b ≤ ρ v`. Let `φ`
be measurable, of modulus at most `1`, and left invariant under the fixer `besselFixer` of the frame
at each place. There are a compact set `A` and a point `t` of the fixer such that the integral over
`A` of `φ` times the kernel `piKernel X .full γ`, the matrix of `W (γ z) ⊗ W (z)^*`, both translated
by `t`, has Hilbert–Schmidt norm at most the root of the product of the local bounds
`pairingBoundSq` at the places; and `A` contains every `z` in the boxes for which the components `x`
of `γ t z` have `besselLength` at most the corresponding `ρ v`. -/
lemma exists_isCompact_enorm_integral_piKernel_le (X : ι → BesselSystem 𝔰 b f)
    {γ y : ι → 𝔰.G₁} {ρ : ι → ℝ} (h_disc : ∀ v : ι, 0 < gramDiscReal (realFrameGram (γ v)))
    (hy_box : ∀ v : ι, y v ∈ frameBox (ρ v)) (hγy_box : ∀ v : ι, (γ v)⁻¹ * y v ∈ frameBox (ρ v))
    (h_radius : ∀ v : ι, b ≤ ρ v) {φ : (ι → 𝔰.G₁) → ℂ} (hφ_meas : Measurable φ)
    (hφ_le : ∀ z : ι → 𝔰.G₁, ‖φ z‖ ≤ 1)
    (hφ_inv : ∀ s z : ι → 𝔰.G₁, (∀ v : ι, s v ∈ besselFixer) → φ (s * z) = φ z) :
    ∃ (A : Set (ι → 𝔰.G₁)) (t : ι → 𝔰.G₁),
      IsCompact A ∧
      (∀ v : ι, t v ∈ besselFixer) ∧
      (∀ z : ι → 𝔰.G₁, (∀ v : ι, z v ∈ frameBox (ρ v)) →
        (∀ v : ι, besselLength (γ v * t v * z v) ≤ ρ v) → z ∈ A) ∧
      ‖∫ z in A, φ (t * z) • piKernel X .full γ (t * z)‖ₑ ≤
        .ofReal √(∏ v : ι, pairingBoundSq (γ v) (X v).deg (ρ v) (card (X v).Index)) := by
  -- At each place `exists_isOpenCellBound` gives a compact `A v`, a finite measure `ν v` and a
  -- probability measure `m v` on the parameters of the shifts `t v` (see `IsOpenCellBound`). The
  -- operator bounds multiply, and some shift does as well as the mean over shifts.
  choose A ν m t h_cell using fun v : ι ↦
    (X v).exists_isOpenCellBound (h_disc v) (hy_box v) (hγy_box v) (h_radius v)
  have ht (v : ι) : Measurable (t v) := (h_cell v).measurable
  have h_prob (v : ι) : IsProbabilityMeasure (m v) := (h_cell v).isProbabilityMeasure
  have h_finite (v : ι) : IsFiniteMeasure (ν v) := (h_cell v).isFiniteMeasure
  have h_mass (v : ι) : (ν v).real .univ ≤ pairingBoundSq (γ v) (X v).deg (ρ v)
    (card (X v).Index) :=
    (h_cell v).measureReal_univ_le
  -- `N x` is the squared Hilbert–Schmidt norm of the pairing with the shifts `t v (x v)`.
  let N (x : ι → 𝔰.FixerFactors) : ℝ≥0∞ :=
    ∑ i : (v : ι) → (X v).Index × (X v).Index, ‖∫ z : ι → 𝔰.G₁, φ z * ∏ v : ι,
      (X v).besselFn .full (γ v * t v (x v) * z v) (i v).1 * conj
        ((X v).besselFn .full (t v (x v) * z v) (i v).2)
        ∂Measure.pi fun v ↦ volume.restrict (A v)‖ₑ ^ 2
  have h_mean : ∫⁻ x, N x ∂Measure.pi m ≤ ∫⁻ z, ‖φ z‖ₑ ^ 2 ∂Measure.pi ν :=
    IsL2Contraction.pi (by fun_prop)
      (fun v i x ↦ ContinuousOn.integrableOn_compact (h_cell v).isCompact (by fun_prop))
      (fun v ↦ (h_cell v).isL2Contraction) φ 1 hφ_meas hφ_le
  have h_ae : ∀ᵐ x : ι → 𝔰.FixerFactors ∂Measure.pi m, ∀ v : ι, ∀ z ∈ frameBox (ρ v),
      besselLength (γ v * t v (x v) * z) ≤ ρ v → z ∈ A v :=
    ae_pi_le_pi (Filter.eventually_pi fun v ↦ (h_cell v).ae_mem_of_besselLength_le)
  obtain ⟨x, hx_mem, hx_le⟩ :=
    exists_notMem_null_le_lintegral (by fun_prop : Measurable N).aemeasurable h_ae
  let s : ι → 𝔰.G₁ := fun v ↦ t v (x v)
  have hx_good : ∀ v : ι, ∀ z ∈ frameBox (ρ v), besselLength (γ v * s v * z) ≤ ρ v → z ∈ A v :=
    not_not.1 hx_mem
  have hs (v : ι) : s v ∈ besselFixer := (h_cell v).mem_besselFixer (x v)
  have h_compact : IsCompact (Set.univ.pi A) := isCompact_univ_pi fun v ↦ (h_cell v).isCompact
  refine ⟨Set.univ.pi A, s, h_compact, hs,
    fun z hz hγz v _ ↦ hx_good v (z v) (hz v) (hγz v), ?_⟩
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero]
  calc
    _ = N x := by
      rw [euclidean_enorm_sq_eq_sum, ← (Equiv.arrowProdEquivProdArrow ..).sum_comp]
      simp only [eval_integral_piLp
        (integrableOn_smul_piKernel X .full γ s hφ_meas hφ_le h_compact).eval_piLp]
      simp [← restrict_pi_pi, volume_pi, piKernel, mul_assoc, N, s, hφ_inv s _ hs]
    _ ≤ ∫⁻ z, ‖φ z‖ₑ ^ 2 ∂Measure.pi ν := hx_le.trans h_mean
    _ ≤ ∫⁻ _, 1 ∂Measure.pi ν :=
      lintegral_mono fun z ↦ pow_le_one' (by simpa [← ofReal_norm] using hφ_le z) 2
    _ = .ofReal (∏ v : ι, (ν v).real .univ) := by simp [Measure.pi_univ, ofReal_prod_of_nonneg]
    _ ≤ .ofReal (∏ v : ι, pairingBoundSq (γ v) (X v).deg (ρ v) (card (X v).Index)) :=
      ofReal_le_ofReal (prod_le_prod₀ (fun v _ ↦ measureReal_nonneg) fun v _ ↦ h_mass v)
    _ = _ := by rw [← ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (prod_nonneg fun v _ ↦ measureReal_nonneg.trans (h_mass v))]

/-- Let `X v` be Bessel systems with size parameter `b`, one for each place `v`, and `W`, `W♭` the
tensor products of their Bessel functions and of their cuts. Let the frame Gram matrix of each `γ v`
have `0 < gramDiscReal`, and let some `y` have both `y v` and `(γ v)⁻¹ * y v` in `frameBox (ρ v)`,
where `b ^ (6 n + 2) ≤ ρ v` and `n = 𝔰.n` is the number of vectors in the frame. Let `φ` be
measurable, of modulus at most `1`, left invariant under the fixer `besselFixer` of the frame at
each place, and such that `φ` times the cut kernel `piKernel X .cut γ`, the matrix of
`W♭ (γ z) ⊗ W♭ (z)^*`, vanishes unless `z` lies in the boxes. Then this product has compact support,
and the Hilbert–Schmidt norm of its integral is at most the root of the product of the local bounds
`pairingBoundSq` at the places, plus the integral of `‖φ‖` times the norm of the difference of the
uncut kernel `W (γ z) ⊗ W (z)^*` and the cut kernel. -/
lemma hasCompactSupport_and_enorm_integral_piKernel_le (X : ι → BesselSystem 𝔰 b f)
    {γ y : ι → 𝔰.G₁} {ρ : ι → ℝ} (h_disc : ∀ v : ι, 0 < gramDiscReal (realFrameGram (γ v)))
    (hy_box : ∀ v : ι, y v ∈ frameBox (ρ v)) (hγy_box : ∀ v : ι, (γ v)⁻¹ * y v ∈ frameBox (ρ v))
    (h_radius : ∀ v : ι, b ^ (6 * 𝔰.n + 2) ≤ ρ v) {φ : (ι → 𝔰.G₁) → ℂ}
    (hφ_meas : Measurable φ) (hφ_le : ∀ z : ι → 𝔰.G₁, ‖φ z‖ ≤ 1)
    (hφ_inv : ∀ s z : ι → 𝔰.G₁, (∀ v : ι, s v ∈ besselFixer) → φ (s * z) = φ z)
    (hφ_box : ∀ z : ι → 𝔰.G₁, φ z • piKernel X .cut γ z ≠ 0 → ∀ v : ι, z v ∈ frameBox (ρ v)) :
    HasCompactSupport (fun z : ι → 𝔰.G₁ ↦ φ z • piKernel X .cut γ z) ∧
    ‖∫ z : ι → 𝔰.G₁, φ z • piKernel X .cut γ z‖ₑ ≤
      .ofReal √(∏ v : ι, pairingBoundSq (γ v) (X v).deg (ρ v) (card (X v).Index)) +
        ∫⁻ z : ι → 𝔰.G₁, ‖φ z‖ₑ * ‖piKernel X .full γ z - piKernel X .cut γ z‖ₑ := by
  -- After a translation by `t` the cut integrand lives on the compact set `A`. There compare it
  -- with the uncut one.
  have hb_radius (v : ι) : b ≤ ρ v :=
    (le_self_pow₀ (X v).one_le_b (Nat.succ_ne_zero _)).trans (h_radius v)
  obtain ⟨A, t, hA, ht, h_mem, h_full⟩ := exists_isCompact_enorm_integral_piKernel_le X h_disc
    hy_box hγy_box hb_radius hφ_meas hφ_le hφ_inv
  let F (σ : FullOrCut) (z : ι → 𝔰.G₁) :
      EuclideanSpace ℂ (((v : ι) → (X v).Index) × ((v : ι) → (X v).Index)) := φ z • piKernel X σ γ z
  have h_supp (z : ι → 𝔰.G₁) (hz : z ∉ A) : F .cut (t * z) = 0 := by
    by_contra h_ne
    refine hz (h_mem z (fun (v : ι) (a : Fin (𝔰.ϱ + 1)) ↦ ?_) fun v ↦ ?_)
    · simpa [frameVector_mul_of_mem_besselFixer (ht v)] using hφ_box (t * z) h_ne v a
    · have h_inCut : InCut (γ v * (t * z) v) b :=
        inCut_of_piKernel_ne_zero X (right_ne_zero_of_smul h_ne) v
      simpa [mul_assoc] using h_inCut.trans (h_radius v)
  have h_int (σ : FullOrCut) : IntegrableOn (fun z ↦ F σ (t * z)) A :=
    integrableOn_smul_piKernel X σ γ t hφ_meas hφ_le hA
  have h_diff : ‖∫ z in A, F .full (t * z) - F .cut (t * z)‖ₑ ≤
      ∫⁻ z, ‖φ z‖ₑ * ‖piKernel X .full γ z - piKernel X .cut γ z‖ₑ := by
    rw [← lintegral_mul_left_eq_self _ t]
    refine ((enorm_integral_le_lintegral_enorm _).trans (setLIntegral_le_lintegral A _)).trans_eq ?_
    simp only [F, ← smul_sub, enorm_smul]
  refine ⟨.intro (hA.image (continuous_const_mul t)) fun z hz ↦ ?_, ?_⟩
  · simpa [F] using h_supp (t⁻¹ * z) fun h_memA ↦ hz ⟨t⁻¹ * z, h_memA, mul_inv_cancel_left t z⟩
  · have h_translate : ∫ z, F .cut z = ∫ z in A, F .cut (t * z) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_supp,
        integral_mul_left_eq_self (F .cut) t]
    calc ‖∫ z, F .cut z‖ₑ
      _ = ‖(∫ z in A, F .full (t * z)) - ∫ z in A, F .full (t * z) - F .cut (t * z)‖ₑ := by
        rw [h_translate, integral_sub (h_int .full) (h_int .cut), _root_.sub_sub_cancel]
      _ ≤ _ := enorm_sub_le.trans (add_le_add h_full h_diff)

/-- The matrix of the operator `W (y) ⊗ W (γ⁻¹ y)^*`, as a vector with the Hilbert–Schmidt norm.
Here `W` is the tensor product, over a finite family `X` of Bessel systems, of the Bessel functions
(`σ = .full`) or of their cuts (`σ = .cut`). It is the adjoint of `piKernel X σ γ⁻¹ y`, the matrix
of `W (γ⁻¹ y) ⊗ W (y)^*`. -/
noncomputable def pairKernel (X : ι → BesselSystem 𝔰 b f) (σ : FullOrCut) (γ y : ι → 𝔰.G₁) :
    EuclideanSpace ℂ (((v : ι) → (X v).Index) × ((v : ι) → (X v).Index)) :=
  WithLp.toLp 2 fun i ↦ ∏ v : ι, (X v).besselFn σ (y v) (i.1 v) * conj
    ((X v).besselFn σ ((γ v)⁻¹ * y v) (i.2 v))

/-- The passage to the adjoint (conjugate transpose) of a complex matrix indexed by `I × I`, a real
linear isometry for the Hilbert–Schmidt norm. -/
noncomputable def adjointIsometry (I : Type) [Fintype I] :
    EuclideanSpace ℂ (I × I) →ₗᵢ[ℝ] EuclideanSpace ℂ (I × I) where
  toFun x := WithLp.toLp 2 fun i ↦ conj (x i.swap)
  map_add' x x' := by ext; simp
  map_smul' r x := by ext; simp
  norm_map' x := by
    simpa [EuclideanSpace.norm_eq] using
      congrArg (√·) ((Equiv.prodComm I I).sum_comp fun i ↦ ‖x i‖ ^ 2)

/-- **One pairing.** Let `X v` be Bessel systems with size parameter `b`, one for each place `v`,
and `W`, `W♭` the tensor products of their Bessel functions and of their cuts. Let the frame Gram
matrix of each `γ v` have `0 < gramDiscReal`, and let some `y'` have both `y' v` and
`(γ v)⁻¹ * y' v` in `frameBox (ρ v)`, where `b ^ (6 n + 2) ≤ ρ v` and `n = 𝔰.n` is the number of
vectors in the frame. Let `φ` be measurable, of modulus at most `1`, left invariant under the fixer
`besselFixer` of the frame at each place, and such that `φ` times the cut kernel
`pairKernel X .cut γ`, the matrix of `W♭ (y) ⊗ W♭ (γ⁻¹ y)^*`, vanishes unless `y` lies in the boxes.
Then this product has compact support, and the Hilbert–Schmidt norm of its integral is at most the
root of the product of the local bounds `pairingBoundSq`, plus the integral of `‖φ‖` times the norm
of the difference of the uncut kernel `W (y) ⊗ W (γ⁻¹ y)^*` and the cut kernel. -/
theorem enorm_integral_pairKernel_cut_le (X : ι → BesselSystem 𝔰 b f)
    {γ y' : ι → 𝔰.G₁} {ρ : ι → ℝ} (h_disc : ∀ v : ι, 0 < gramDiscReal (realFrameGram (γ v)))
    (hy_box : ∀ v : ι, y' v ∈ frameBox (ρ v)) (hγy_box : ∀ v : ι, (γ v)⁻¹ * y' v ∈ frameBox (ρ v))
    (h_radius : ∀ v : ι, b ^ (6 * 𝔰.n + 2) ≤ ρ v) {φ : (ι → 𝔰.G₁) → ℂ}
    (hφ_meas : Measurable φ) (hφ_le : ∀ y : ι → 𝔰.G₁, ‖φ y‖ ≤ 1)
    (hφ_inv : ∀ s y : ι → 𝔰.G₁, (∀ v : ι, s v ∈ besselFixer) → φ (s * y) = φ y)
    (hφ_box : ∀ y : ι → 𝔰.G₁, φ y • pairKernel X .cut γ y ≠ 0 → ∀ v : ι, y v ∈ frameBox (ρ v)) :
    HasCompactSupport (fun y : ι → 𝔰.G₁ ↦ φ y • pairKernel X .cut γ y) ∧
    ‖∫ y : ι → 𝔰.G₁, φ y • pairKernel X .cut γ y‖ₑ ≤
      .ofReal √(∏ v : ι, pairingBoundSq (γ v) (X v).deg (ρ v) (card (X v).Index)) +
        ∫⁻ y : ι → 𝔰.G₁, ‖φ y‖ₑ * ‖pairKernel X .full γ y - pairKernel X .cut γ y‖ₑ := by
  -- The kernel is the adjoint of `W (γ⁻¹ y) ⊗ W (y)^*`, and `γ⁻¹` has the same `gramDiscReal`.
  let T := adjointIsometry ((v : ι) → (X v).Index)
  have h_kernel (σ : FullOrCut) (y : ι → 𝔰.G₁) : pairKernel X σ γ y = T (piKernel X σ γ⁻¹ y) := by
    ext; simp [T, adjointIsometry, pairKernel, piKernel, mul_comm]
  have h_adjoint (y : ι → 𝔰.G₁) :
      φ y • pairKernel X .cut γ y = T (conj (φ y) • piKernel X .cut γ⁻¹ y) := by
    ext; simp [h_kernel, T, adjointIsometry]
  have h_disc_inv (v : ι) :
      gramDiscReal (realFrameGram (γ⁻¹ v)) = gramDiscReal (realFrameGram (γ v)) := by
    rw [Pi.inv_apply, realFrameGram, Filling.frameGram_inv]
    simp [gramDiscReal, frameDisc, leadingMinor, ← Matrix.conjTranspose_submatrix]
  obtain ⟨h_support, h_bound⟩ := hasCompactSupport_and_enorm_integral_piKernel_le X (γ := γ⁻¹)
    (y := γ⁻¹ * y')
    (φ := fun y ↦ conj (φ y)) (fun v ↦ by simpa only [h_disc_inv] using h_disc v) hγy_box
    (fun v ↦ by simpa using hy_box v) h_radius (Complex.continuous_conj.measurable.comp hφ_meas)
    (by simpa using hφ_le) (fun s y hs ↦ by rw [hφ_inv s y hs])
    fun y hy ↦ hφ_box y (by rwa [h_adjoint, map_ne_zero_iff T T.injective])
  simp only [h_adjoint]
  refine ⟨h_support.comp_left (map_zero T), ?_⟩
  rw [T.integral_comp_comm, T.enorm_map]
  simpa only [h_kernel, ← map_sub, T.enorm_map, pairingBoundSq, h_disc_inv,
    RCLike.enorm_conj] using h_bound

end New.BesselSystem
