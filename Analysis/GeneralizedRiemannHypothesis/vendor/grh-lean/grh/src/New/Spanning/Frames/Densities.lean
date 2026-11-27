import New.Spanning.Bessel.Basic
import New.Spanning.Frames.Depth

/-!
# The densities as integrals over pairs of frames

For a cut Bessel function `W` and two heads (sequences of units `p`, `q`), the form of floor `j` is
a density times an integral, over a position `x` and two frames, of a weighted product of two
correlations. The file defines these forms and their majorants, and proves the descent from one
floor to the next.

Notions from other files:
* `F : PlaceData ι T m` is the data of a place: the measures of the floors, the level `F.levelUnit`
  and the compact set `F.boxSet` (the box) of the unitary group `T.G`; a `Gauge F` is a notion of
  size with a number Λ = `Γ.loss` whose powers bound moduli and volumes.
* G^(l) = `floorGroup l` and R^(l) = `partialUnitriangularGroup l` are the subgroups described in
  `New.Spanning.Frames.Lengths`, and 𝖴 = `T.besselU` is the Bessel unipotent group. A point `g` is
  near at `j` (`F.IsNear j g`) if R^(j) g meets the box.
* θ_j = `F.floorMeasure j` is the measure of floor `j`, 𝗆_j = `F.partialGroupMeasure 0 j` the
  convolution of the Heisenberg and floor measures of the floors below `j`, and 𝖬 = `F.groupMeasure`
  that of all floors.
* `F.partialCorrelation j k g y` is the correlation from floor `j` on, the integral of
  `k (σ g) (σ y)` against `F.quotientMeasureFrom j`, the convolution of the θ_l with l ≥ j.
* w_p = `weylElem j p` is the Weyl element of the first `j` hyperbolic pairs with the entries `p a`,
  and `weylRatio j p q` is the diagonal element w_q⁻¹ w_p.

## Main definitions and results

* `New.Floors.PlaceData.IsCut`, `New.Floors.PlaceData.floorForm`,
  `New.Floors.PlaceData.formIntegrandL1Norm`, `New.Floors.PlaceData.formMajorant`: the forms and
  their majorants.
* `New.Floors.Gauge.inner_besselOrbitalIntegral`: the product of two orbital integrals as a double
  integral.
* `New.Floors.Gauge.isPairingKernel_frameCorrelation`: the rules for correlations.
* `New.Floors.PlaceData.floorForm_zero_eq_integral`: the mass: the form of floor 0 is the integral
  of a square.
* `New.Floors.Gauge.integral_weight_mul_floorForm_succ`,
  `New.Floors.Gauge.integral_psi_mul_floorForm_succ`: descent from one floor to the next.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Fintype FloorGroups ComplexConjugate InnerProductSpace
  PlaceData Finset Function RCLike Place

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} {𝔰 : Shape} (j : ℕ)
  {T : 𝔰.Form A} [IsHermitianUnit T.splitGram]
  {F : PlaceData ι T m} (p q : ℕ → Aˣ) {I : Type} [Fintype I]
  (W : T.G → EuclideanSpace ℂ I) (x : T.G) (Γ : Gauge F)

section

/-- The density κ_j of two sequences of units `p`, `q`: the product over `a < j` of
`modulus (p a * q a) ^ (d a / 2)` with `d a = 𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1))`. The power `d a / 2` is
written as the `d a`-th power of a square root. -/
def PlaceData.headDensity (_ : PlaceData ι T m) : ℝ≥0∞ :=
  ∏ a ∈ .range j, (P.modulus (p a * q a) ^ (2⁻¹ : ℝ)) ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))

/-- The correlation `⟨W x, W (d y)⟩` of two points, the second translated by `d`. -/
@[simp] abbrev frameCorrelation (d x y : T.G) : ℂ := ⟪W x, W (d * y)⟫_ℂ

/-- W is a Bessel function of frequency η: bounded, measurable, with W(ux) = ψ(η σ(u))W(x) for u in
𝖴 = `T.besselU`, where σ(u) = `simpleRootSum u` is the superdiagonal sum of the frame block. -/
structure Place.IsBessel (η : Aˣ) : Prop extends IsBoundedMeasurable W where
  /-- Left translation by u in the Bessel unipotent group multiplies W by
  ψ(η · `simpleRootSum u`). -/
  map_unipotent_mul : ∀ u ∈ T.besselU, ∀ x : T.G, W (u * x) = ψ (η * simpleRootSum u) • W x

/-- W is a cut Bessel function for the place datum: Bessel of frequency `F.levelUnit⁻¹`, and zero at
x unless ux lies in the box `F.boxSet` for some u in 𝖴 = `T.besselU`. -/
structure PlaceData.IsCut : Prop extends P.IsBessel W F.levelUnit⁻¹ where
  /-- W vanishes off the translates of the box `F.boxSet` by the Bessel unipotent group. -/
  exists_mul_mem_box : ∀ {x : T.G}, W x ≠ 0 → ∃ u ∈ T.besselU, u * x ∈ F.boxSet

/-- The squared L² norm of the correlation ⟪W x, W y⟫ for the measure `F.quotientMeasureFrom 0` in
both variables, which stands for integration over 𝖴∖G. -/
def PlaceData.pairingNormSq : ℝ≥0∞ :=
  ∫⁻ x : T.G, ∫⁻ y : T.G, ‖⟪W x, W y⟫_ℂ‖ₑ ^ 2 ∂F.quotientMeasureFrom 0 ∂F.quotientMeasureFrom 0

/-- At the position `x`: the correlation from floor `j` on (`F.partialCorrelation j`) of the kernel
⟨W y, W y'⟩ at the points `g`, `g x`, times the conjugate of that of the kernel ⟨W y, W (d y')⟩ at
`w⁻¹ g`, `w⁻¹ g x`. -/
def PlaceData.partialCorrelationProduct (d w g : T.G) : ℂ :=
  F.partialCorrelation j (frameCorrelation W 1) g (g * x) *
    conj (F.partialCorrelation j (frameCorrelation W d) (w⁻¹ * g) (w⁻¹ * g * x))

/-- At the position x and the point g, the double integral ∬ ω(στ⁻¹) k(σg, σgx)
conj(k'(τw_p⁻¹g, τw_p⁻¹gx)) dθ_j(τ) dθ_j(σ). Here θ_j = `F.floorMeasure j`, w_p = `weylElem j p`,
and k, k' are the correlations from floor j + 1 on of
`New.Floors.PlaceData.partialCorrelationProduct` for the twist `weylRatio j p q`. -/
def PlaceData.formIntegrand (ω : T.G → ℂ) (g : T.G) : ℂ :=
  ∫ σ : T.G, ∫ τ : T.G, ω (σ * τ⁻¹) *
    F.partialCorrelationProduct (j + 1) W x (weylRatio j p q) (σ * weylElem j p * τ⁻¹)
      (σ * g) ∂F.floorMeasure j ∂F.floorMeasure j

/-- The form 𝓘_j(p, q; ω): the density κ_j = `F.headDensity j p q` times the integral of the double
integral `New.Floors.PlaceData.formIntegrand` over the position against 𝖬 = `F.groupMeasure` and
over the point against 𝗆_j = `F.partialGroupMeasure 0 j`. -/
def PlaceData.floorForm (ω : T.G → ℂ) : ℂ :=
  (F.headDensity j p q).toReal *
    ∫ z : T.G × T.G, F.formIntegrand j p q W z.1 ω z.2 ∂F.groupMeasure.prod
      (F.partialGroupMeasure 0 j)

/-- The number 𝖥_j(x; ω): at the position x, the integral against 𝗆_j = `F.partialGroupMeasure 0 j`
of the modulus of the double integral `New.Floors.PlaceData.formIntegrand` that defines
`F.floorForm`. -/
def PlaceData.formIntegrandL1Norm (ω : T.G → ℂ) : ℝ≥0∞ :=
  ∫⁻ g : T.G, ‖F.formIntegrand j p q W x ω g‖ₑ ∂F.partialGroupMeasure 0 j

/-- The majorant of the form at the position `x`: the integral against
𝗆_j = `F.partialGroupMeasure 0 j` of the product of two factors `F.pivotL1Norm j`, one for each
kernel, each the integral over floor j of the modulus of the partial correlation from floor j + 1
on. -/
def PlaceData.formMajorant : ℝ≥0∞ :=
  ∫⁻ g : T.G, F.pivotL1Norm j (frameCorrelation W 1) g (g * x) *
    F.pivotL1Norm j (frameCorrelation W (weylRatio j p q)) ((weylElem j p)⁻¹ * g)
      ((weylElem j p)⁻¹ * g * x) ∂F.partialGroupMeasure 0 j

/-- The product of the second moments `F.weightedSquareIntegral` of the two correlations at `x`,
times the constant made of the squared product of `F.floorModulus a (p a)⁻¹` over a < j and of the
cube of `Γ.floorsConst`. A number has the gain `ς` at `x` if its square is at most `ς ^ 2` times
this product; the density `F.headDensity` is not included. -/
def Gauge.weightedSquareProduct : ℝ≥0∞ :=
  (∏ a ∈ .range j, F.floorModulus a (p a)⁻¹) ^ 2 * Γ.floorsConst ^ 3 *
    F.weightedSquareIntegral 0 (frameCorrelation W 1) x * F.weightedSquareIntegral j
      (frameCorrelation W (weylRatio j p q)) x

/-- At the position `x`, the point `y` is active for the heads `p`, `q`: the correlation of `y` and
`y x` is not zero, and both points are near at `j` after the Weyl elements are undone. -/
structure PlaceData.IsActive (y : T.G) : Prop where
  /-- The correlation of the two points is not zero. -/
  inner_ne_zero : ⟪W y, W (y * x)⟫_ℂ ≠ 0
  /-- The point `w_p⁻¹ y` is near at `j`. -/
  isNear_left : F.IsNear j ((weylElem j p)⁻¹ * y)
  /-- The point `w_q⁻¹ y x` is near at `j`. -/
  isNear_right : F.IsNear j ((weylElem j q)⁻¹ * (y * x))

/-- At the position `x`, every active point `y` has a frame vector e_a with `j ≤ a` whose depth
`F.depth a y x` is at least `D`. -/
def PlaceData.HasDeepVector (D : ℝ≥0∞) : Prop :=
  ∀ y : T.G, F.IsActive j p q W x y → ∃ a : Fin 𝔰.ϱ, j ≤ a ∧ D ≤ F.depth a y x

variable {j p q W x}

/-- Every active point `y` at the position `x` has a frame vector e_a with `j ≤ a` of depth at least
`σ⁻¹` if and only if it has such a vector whose set of products `F.stableProducts a y x` has volume
at most `σ`. -/
lemma PlaceData.hasDeepVector_inv_iff {σ : ℝ≥0∞} : F.HasDeepVector j p q W x σ⁻¹ ↔
    ∀ y : T.G, F.IsActive j p q W x y →
      ∃ a : Fin 𝔰.ϱ, j ≤ a ∧ volume (F.stableProducts a y x) ≤ σ := by
  simp only [HasDeepVector, le_depth_iff, inv_inv]

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram] in
/-- For b ≤ ϱ, let x be in both R^(b+1) = `partialUnitriangularGroup (b + 1)` and G^(b) =
`floorGroup b`, so that x fixes the frame vector f_b. Then multiplying y by x on the left or on the
right leaves the diagonal entry h(f_b, y f_b) of Z(y) = `T.frameGram y` unchanged. -/
theorem frameGram_diag_mul {x : T.G} {b : Fin 𝔰.n}
    (h : x ∈ partialUnitriangularGroup (b + 1) ⊓ floorGroup b) (y : T.G) :
    T.frameGram (x * y : T.G) b b = T.frameGram y b b ∧
      T.frameGram (y * x : T.G) b b = T.frameGram y b b := by
  set f : 𝔰.BesselIndex → A := Pi.single (𝔰.besselFrame b) 1
  let mat (z : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := z
  have h_mul (z z' : T.G) : mat (z * z') *ᵥ f = mat z *ᵥ mat z' *ᵥ f := by
    simp [mat, mulVec_mulVec]
  -- The entry is `h(f, z f)`, and `x` fixes the vector `f`.
  have h_entry (z : T.G) :
      T.frameGram z b b = star f ⬝ᵥ T.splitGram *ᵥ mat z *ᵥ f := by
    simp only [f, mat, Shape.Form.frameGram, ← Pi.single_star, star_one, single_one_dotProduct,
      mulVec_single_one]
    rfl
  obtain ⟨h_unitri, h_floor⟩ : x ∈ partialUnitriangularGroup (b + 1) ∧ x ∈ floorGroup b :=
    Subgroup.mem_inf.1 h
  have h_fix : mat x *ᵥ f = f :=
    orbitPoint_eq_iff.1 ((mem_partialUnitriangularGroup_succ_iff h_floor).1 h_unitri)
  constructor
  · calc T.frameGram (x * y : T.G) b b
        = star (mat x *ᵥ f) ⬝ᵥ T.splitGram *ᵥ mat x *ᵥ mat y *ᵥ f := by
          rw [h_fix, h_entry, h_mul]
      _ = T.frameGram y b b := by rw [U.form_mulVec_mulVec, h_entry]
  · rw [h_entry, h_mul, h_fix, h_entry]

end

variable {j p q W x}

/-- The form of floor `j` with the weight `ω` is bounded by its L¹-norm version:
|𝓘_j(p, q; ω)| ≤ κ_j ∫ 𝖥_j(x; ω) d𝖬(x), where 𝓘_j = `F.floorForm j`, κ_j = `F.headDensity j p q`,
𝖥_j = `F.formIntegrandL1Norm j` and 𝖬 = `F.groupMeasure`. -/
theorem PlaceData.enorm_floorForm_le (ω : T.G → ℂ) :
    ‖F.floorForm j p q W ω‖ₑ ≤
      F.headDensity j p q * ∫⁻ x : T.G, F.formIntegrandL1Norm j p q W x ω ∂F.groupMeasure := by
  have h_density : ‖((F.headDensity j p q).toReal : ℂ)‖ₑ ≤ F.headDensity j p q := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg toReal_nonneg]
    exact ofReal_toReal_le
  have h_integral : ‖∫ z : T.G × T.G, F.formIntegrand j p q W z.1 ω z.2
      ∂F.groupMeasure.prod (F.partialGroupMeasure 0 j)‖ₑ ≤
      ∫⁻ x : T.G, F.formIntegrandL1Norm j p q W x ω ∂F.groupMeasure :=
    (enorm_integral_le_lintegral_enorm _).trans (lintegral_prod_le _)
  rw [floorForm, enorm_mul]
  exact mul_le_mul' h_density h_integral

/-- The partial group measure of the last two floors, `ϱ` and `ϱ + 1`, is the convolution of the
Haar measure `F.measureH` of the group H = `besselH`, which is the measure of floor `ϱ + 1`, with
the measure of floor `ϱ`. -/
theorem PlaceData.partialGroupMeasure_top :
    F.partialGroupMeasure 𝔰.ϱ 2 = F.measureH ∗ₘ F.floorMeasure 𝔰.ϱ := by
  simp [descConv]

/-- The elements of the unitary group whose matrix entries have size `j` for the gauge `Γ` form a
compact set. -/
lemma Gauge.isCompact_hasMatrixSize {j : ℕ} (Γ : Gauge F) :
    IsCompact {y : T.G | Γ.HasMatrixSize j (y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A)} :=
  isClosedEmbedding_unitary_coe.isCompact_preimage (Γ.isCompact_ofSize _).matrix

omit [IsHermitianUnit T.splitGram] in
/-- Let `W` be a Bessel function of frequency `η`, so that `W (u * y) = χ(u) • W y` for `u` in the
unipotent group 𝖴 = `T.besselU`, with `χ(u) = ψ (η * simpleRootSum u)`. For a left invariant measure
`μ`, the orbital integral J(γ) = ∫ W(y) ⊗ W(γ⁻¹y)^* dμ(y) (`besselOrbitalIntegral μ W γ`) satisfies
J(u⁻¹γu') = conj χ(u) · χ(u') · J(γ) for `u`, `u'` in 𝖴. -/
theorem Place.IsBessel.besselOrbitalIntegral_besselU_mul {W : T.G → EuclideanSpace ℂ I} {η : Aˣ}
    (hW : P.IsBessel W η) (μ : Measure T.G) [μ.IsMulLeftInvariant] {u u' : T.G}
    (hu : u ∈ T.besselU) (hu' : u' ∈ T.besselU) (γ : T.G) :
    besselOrbitalIntegral μ W (u⁻¹ * γ * u') =
      (conj (P.ψ (η * simpleRootSum u)) * P.ψ (η * simpleRootSum u')) •
        besselOrbitalIntegral μ W γ := by
  let χ (v : T.G) : ℂ := P.ψ (η * simpleRootSum v)
  have h_inv {v : T.G} (hv : v ∈ T.besselU) (y : T.G) : W (v⁻¹ * y) = conj (χ v) • W y := by
    have h_law : W y = χ v • W (v⁻¹ * y) := by
      rw [← hW.map_unipotent_mul v hv, mul_inv_cancel_left]
    rw [h_law, smul_smul, RCLike.conj_mul, P.norm_psi, RCLike.ofReal_one, one_pow, one_smul]
  ext ⟨i, i'⟩
  simp only [besselOrbitalIntegral, PiLp.smul_apply, smul_eq_mul]
  -- Substitute `u⁻¹ * y` for `y`.
  calc ∫ y : T.G, W y i * conj (W ((u⁻¹ * γ * u')⁻¹ * y) i') ∂μ
    _ = ∫ y : T.G, W (u⁻¹ * y) i * conj (W ((u⁻¹ * γ * u')⁻¹ * (u⁻¹ * y)) i') ∂μ :=
      (integral_mul_left_eq_self _ u⁻¹).symm
    _ = ∫ y : T.G, conj (χ u) * χ u' * (W y i * conj (W (γ⁻¹ * y) i')) ∂μ := by
      refine integral_congr_ae (.of_forall fun y : T.G ↦ ?_)
      have h_point : (u⁻¹ * γ * u')⁻¹ * (u⁻¹ * y) = u'⁻¹ * (γ⁻¹ * y) := by group
      simp only [h_point, h_inv hu, h_inv hu', PiLp.smul_apply, smul_eq_mul, map_mul, conj_conj]
      ring
    _ = conj (χ u) * χ u' * ∫ y : T.G, W y i * conj (W (γ⁻¹ * y) i') ∂μ := integral_const_mul _ _

/-- A cut Bessel function `W` vanishes off the points near at `j`, for every `j`: if `W x ≠ 0`, then
`u x` lies in the box `F.boxSet` for some `u` in `partialUnitriangularGroup j`. -/
theorem PlaceData.IsCut.isNear_of_ne_zero (hk : F.IsCut W) (h : W x ≠ 0) : F.IsNear j x := by
  obtain ⟨u, hu, hu_box⟩ : ∃ u ∈ T.besselU, u * x ∈ F.boxSet := hk.exists_mul_mem_box h
  exact ⟨u, mem_partialUnitriangularGroup_of_mem_besselU hu, hu_box⟩

/-- Let `W` be a cut Bessel function for the place datum `F`. If the orbital integral J(γ) = ∫
W(y) ⊗ W(γ⁻¹y)^* dμ(y) is not zero, then all leading minors of the matrix of the products h(f_a, γ
f_b) of the frame vectors (`T.frameGram γ`) have size `9 * 𝔰.n`, that is lie in the set
`Γ.ofSize (9 * 𝔰.n)`, in every gauge `Γ` for `F`. -/
theorem Gauge.leadingMinor_mem_ofSize_of_besselOrbitalIntegral_ne_zero (Γ : Gauge F)
    {W : T.G → EuclideanSpace ℂ I} (hW : F.IsCut W) {μ : Measure T.G} {γ : T.G}
    (hγ : besselOrbitalIntegral μ W γ ≠ 0) (j : Fin (𝔰.n + 1)) :
    leadingMinor (T.frameGram (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A)) j ∈
      Γ.ofSize (9 * 𝔰.n) := by
  obtain ⟨y, hy, hγy⟩ : ∃ y : T.G, W y ≠ 0 ∧ W (γ⁻¹ * y) ≠ 0 := by
    by_contra! h_zero
    refine hγ (PiLp.ext fun i ↦ integral_eq_zero_of_ae (.of_forall fun y ↦ ?_))
    by_cases hy : W y = 0
    · simp only [hy, PiLp.zero_apply, zero_mul, Pi.zero_apply]
    · simp only [h_zero y hy, PiLp.zero_apply, map_zero, mul_zero, Pi.zero_apply]
  exact Γ.leadingMinor_mem_ofSize_of_isNear (hW.isNear_of_ne_zero hy) (hW.isNear_of_ne_zero hγy)
    le_rfl

/-- Let W be a cut Bessel function and |ω| ≤ 1 everywhere. For every floor `j : ℕ`, all sequences of
units `p q : ℕ → Aˣ` and every point x of the group, the L¹ norm 𝖥_j(x; ω) of the form integrand at
x is at most the majorant `F.formMajorant j p q W x`. -/
theorem PlaceData.IsCut.formIntegrandL1Norm_le_formMajorant {W : T.G → EuclideanSpace ℂ I} {x : T.G}
    (hW : F.IsCut W) {ω : T.G → ℂ} (hω_le : ∀ y : T.G, ‖ω y‖ ≤ 1) :
    F.formIntegrandL1Norm j p q W x ω ≤ F.formMajorant j p q W x := by
  have hW_meas : StronglyMeasurable W := hW.stronglyMeasurable
  rw [formIntegrandL1Norm, formMajorant]
  refine lintegral_mono fun g : T.G ↦ ?_
  -- The integrands of the two factors `pivotL1Norm` in `formMajorant`.
  let plain (σ : T.G) : ℝ≥0∞ :=
    ‖F.partialCorrelation (j + 1) (frameCorrelation W 1) (σ * g) (σ * (g * x))‖ₑ
  let twisted (τ : T.G) : ℝ≥0∞ :=
    ‖F.partialCorrelation (j + 1) (frameCorrelation W (weylRatio j p q))
      (τ * ((weylElem j p)⁻¹ * g))
      (τ * ((weylElem j p)⁻¹ * g * x))‖ₑ
  have h_integrand (σ τ : T.G) :
      ‖ω (σ * τ⁻¹) * F.partialCorrelationProduct (j + 1) W x (weylRatio j p q)
        (σ * weylElem j p * τ⁻¹)
        (σ * g)‖ₑ ≤ plain σ * twisted τ := by
    have hω : ‖ω (σ * τ⁻¹)‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      exact ofReal_le_one.2 (hω_le _)
    grw [enorm_mul, hω, one_mul]
    simp [partialCorrelationProduct, plain, twisted, mul_assoc]
  have h_plain_meas : Measurable plain := by fun_prop [partialCorrelation]
  calc ‖F.formIntegrand j p q W x ω g‖ₑ
    _ ≤ ∫⁻ σ : T.G, ∫⁻ τ : T.G, plain σ * twisted τ ∂F.floorMeasure j ∂F.floorMeasure j :=
      (enorm_integral_le_lintegral_enorm _).trans <| lintegral_mono fun σ ↦
        (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono (h_integrand σ))
    _ = ∫⁻ σ : T.G, plain σ * ∫⁻ τ : T.G, twisted τ ∂F.floorMeasure j ∂F.floorMeasure j :=
      lintegral_congr fun σ ↦ lintegral_const_mul' _ _ enorm_ne_top
    _ = (∫⁻ σ : T.G, plain σ ∂F.floorMeasure j) * ∫⁻ τ : T.G, twisted τ ∂F.floorMeasure j :=
      lintegral_mul_const _ h_plain_meas
    _ = F.pivotL1Norm j (frameCorrelation W 1) g (g * x) *
        F.pivotL1Norm j (frameCorrelation W (weylRatio j p q)) ((weylElem j p)⁻¹ * g)
          ((weylElem j p)⁻¹ * g * x) := by rw [pivotL1Norm, pivotL1Norm]

/-- Compact support of the orbital integrals, with a bound. Let W be a cut Bessel function, p a head
of length ϱ for the gauge Γ, with Weyl element w_p = `weylElem 𝔰.ϱ p`, and x in
G^(ϱ) = `floorGroup 𝔰.ϱ`. If W(y) ≠ 0 and W((w_p x)⁻¹y) ≠ 0, then the entries of y have size 60 n²,
where n = `𝔰.n` = ϱ + 1: the unipotent factors that move the two points into the box are solved from
the minors of the head. -/
theorem Gauge.hasMatrixSize_of_ne_zero {p : ℕ → Aˣ} {W : T.G → EuclideanSpace ℂ I} {x : T.G}
    (Γ : Gauge F) (hW : F.IsCut W) {y : T.G} (hp : Γ.IsHead 𝔰.ϱ p) (hx_top : x ∈ floorGroup 𝔰.ϱ)
    (hy : W y ≠ 0) (hy' : W ((weylElem 𝔰.ϱ p * x)⁻¹ * y) ≠ 0) :
    Γ.HasMatrixSize (60 * 𝔰.n ^ 2) (y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by
  obtain ⟨u, hu, hu_box⟩ : ∃ u ∈ T.besselU, u * y ∈ F.boxSet := hW.exists_mul_mem_box hy
  -- The factor `x⁻¹` lies in `floorGroup 𝔰.ϱ`, so it does not affect nearness at the floor `𝔰.ϱ`.
  have h_near_mul : F.IsNear 𝔰.ϱ (x⁻¹ * ((weylElem 𝔰.ϱ p)⁻¹ * y)) := by
    simpa [mul_assoc] using hW.isNear_of_ne_zero hy'
  have h_near : F.IsNear 𝔰.ϱ ((weylElem 𝔰.ϱ p)⁻¹ * y) :=
    h_near_mul.of_floorGroup_mul (inv_mem hx_top)
  have hu_below : u ∈ unipotentBelow 𝔰.ϱ := (unipotentBelow_eq_besselU .refl).ge hu
  have hu_unitri : u ∈ partialUnitriangularGroup 𝔰.ϱ :=
    mem_partialUnitriangularGroup_of_mem_besselU hu
  obtain ⟨hy_size, -⟩ :=
    Size.hasMatrixSize_of_isHead Γ.hasMatrixSize_boxSet .refl h_near ⟨hu_unitri, hu_box⟩ hp hu_below
  exact hy_size

/-- The inner product of two orbital integrals as an integral over two copies of the group. Let Γ be
a gauge for the place datum F and μ a Haar measure. Let W be a continuous cut Bessel function, that
is a Bessel function that vanishes off the 𝖴-translates of the box of F. Let p and q be heads of
length ϱ for Γ, with Weyl elements w_p = `weylElem 𝔰.ϱ p` and w_q, and let x be in the subgroup
G^(ϱ) = `floorGroup 𝔰.ϱ`. Write J(γ) = ∫ W(y) ⊗ W(γ⁻¹y)^* dμ(y) for `besselOrbitalIntegral μ W γ`.
Then ⟨J(w_p x), J(w_q x)⟩ is the μ×μ-integral over (y, y') of ⟨Wy, Wy'⟩ times the conjugate of
⟨W((w_p x)⁻¹y), W((w_q x)⁻¹y')⟩. -/
theorem Gauge.inner_besselOrbitalIntegral {p q : ℕ → Aˣ} {W : T.G → EuclideanSpace ℂ I} {x : T.G}
    (Γ : Gauge F) (hk : F.IsCut W) {μ : Measure T.G} [IsHaarMeasure μ] (hW : Continuous W)
    (hp : Γ.IsHead 𝔰.ϱ p) (hq : Γ.IsHead 𝔰.ϱ q) (hx_top : x ∈ floorGroup 𝔰.ϱ) :
    ⟪besselOrbitalIntegral μ W (weylElem 𝔰.ϱ p * x),
      besselOrbitalIntegral μ W (weylElem 𝔰.ϱ q * x)⟫_ℂ =
      ∫ z : T.G × T.G, ⟪W z.1, W z.2⟫_ℂ *
        conj ⟪W ((weylElem 𝔰.ϱ p * x)⁻¹ * z.1), W ((weylElem 𝔰.ϱ q * x)⁻¹ * z.2)⟫_ℂ ∂μ.prod μ := by
  -- The coordinate `i` of `besselOrbitalIntegral μ W (weylElem 𝔰.ϱ r * x)` is the integral of
  -- `f r i`.
  let f (r : ℕ → Aˣ) (i : I × I) (y : T.G) : ℂ :=
    W y i.1 * conj (W ((weylElem 𝔰.ϱ r * x)⁻¹ * y) i.2)
  -- For a head `r`, `f r i` is continuous by `hW` and lives on the compact set of points of size
  -- 60 n².
  have h_integrable {r : ℕ → Aˣ} (hr : Γ.IsHead 𝔰.ϱ r) (i : I × I) : Integrable (f r i) μ := by
    have h_support : HasCompactSupport (f r i) := by
      refine .intro (Γ.isCompact_hasMatrixSize (j := 60 * 𝔰.n ^ 2)) fun y hy ↦ ?_
      by_contra h_ne
      obtain ⟨h_left, h_right⟩ :
          W y i.1 ≠ 0 ∧ conj (W ((weylElem 𝔰.ϱ r * x)⁻¹ * y) i.2) ≠ 0 := mul_ne_zero_iff.1 h_ne
      refine hy (Γ.hasMatrixSize_of_ne_zero hk hr hx_top (fun h_zero ↦ ?_) fun h_zero ↦ ?_)
      · exact h_left (by rw [h_zero, PiLp.zero_apply])
      · exact h_right (by rw [h_zero, PiLp.zero_apply, map_zero])
    exact h_support.integrable
  have h_integrable_prod (i : I × I) :
      Integrable (fun z : T.G × T.G ↦ conj (f p i z.1) * f q i z.2) (μ.prod μ) :=
    (Complex.conjCLE.integrable_comp_iff.2 (h_integrable hp i)).mul_prod (h_integrable hq i)
  calc ⟪besselOrbitalIntegral μ W (weylElem 𝔰.ϱ p * x),
         besselOrbitalIntegral μ W (weylElem 𝔰.ϱ q * x)⟫_ℂ
    _ = ∑ i : I × I, conj (∫ y : T.G, f p i y ∂μ) * ∫ y : T.G, f q i y ∂μ := by
      simp only [PiLp.inner_apply, inner_apply', besselOrbitalIntegral, f]
    _ = ∑ i : I × I, ∫ z : T.G × T.G, conj (f p i z.1) * f q i z.2 ∂μ.prod μ := by
      simp only [← integral_conj, ← integral_prod_mul]
    _ = ∫ z : T.G × T.G, ∑ i : I × I, conj (f p i z.1) * f q i z.2 ∂μ.prod μ :=
      (integral_finsetSum _ fun i _ ↦ h_integrable_prod i).symm
    _ = ∫ z : T.G × T.G, ⟪W z.1, W z.2⟫_ℂ * conj ⟪W ((weylElem 𝔰.ϱ p * x)⁻¹ * z.1),
        W ((weylElem 𝔰.ϱ q * x)⁻¹ * z.2)⟫_ℂ ∂μ.prod μ := by
      refine integral_congr_ae (.of_forall fun z : T.G × T.G ↦ ?_)
      simp only [f, PiLp.inner_apply, inner_apply', sum_prod_type, Finset.sum_mul_sum,
        _root_.map_sum, map_mul, conj_conj]
      exact sum_congr rfl fun i _ ↦ sum_congr rfl fun i' _ ↦ by ring

/-- Let `W` be a cut Bessel function for the place datum `F`, which has a gauge, and `p`, `q` two
sequences of units. The kernel `⟪W g, W (w y)⟫`, with `w` = `weylRatio j p q`, satisfies the rules
of `New.Floors.PlaceData.IsPairingKernel`: it is measurable, transforms by a character under the
unipotent groups, its `w` commutes with the group of floor `j`, it has bounded mass, and its partial
correlations vanish unless the first point is near. -/
lemma Gauge.isPairingKernel_frameCorrelation (Γ : Gauge F) (hW : F.IsCut W) (j : ℕ) (p q : ℕ → Aˣ) :
    F.IsPairingKernel j (frameCorrelation W (weylRatio j p q)) (weylRatio j p q) := by
  have hW_meas : StronglyMeasurable W := hW.stronglyMeasurable
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y : T.G, ‖W y‖ ≤ C := hW.bounded
  refine
    { measurable := by fun_prop
      equivariance := fun {l u v} hu hv g y ↦ ?_
      conj_eq_self := fun σ hσ ↦ ?_
      exists_lintegral_le := fun l ↦ ?_
      isNear_of_partialCorrelation_ne_zero := fun {l g y} h_ne ↦ ?_ }
  · -- The law holds under the integral. Move `u` and `v` to the left by conjugation; they stay in
    -- the Bessel group `besselU`, where `W` transforms by the character
    -- `ψ (simpleRootSum · / F.levelUnit)`.
    simp only [partialCorrelation, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_descConv_mem ae_floorMeasure_mem] with σ hσ
    have hσ' : σ ∈ floorGroup l := floorGroup_anti l.le_succ hσ
    have h_left : W (σ * (u * g)) = ψ (F.levelUnit⁻¹.val * simpleRootSum (σ * u * σ⁻¹)) • W
      (σ * g) := by
      rw [show σ * (u * g) = σ * u * σ⁻¹ * (σ * g) by group]
      exact hW.map_unipotent_mul _ (unipotentBelow_le_besselU (conj_mem_unipotentBelow hσ' hu))
        (σ * g)
    let v' : T.G := (weylRatio j q p)⁻¹ * (σ * v * σ⁻¹) * weylRatio j q p
    have hv' : v' ∈ T.besselU :=
      conj_mem_unitriangular (by simp [coe_weylRatio, blockTriangular_diagonal])
        (unipotentBelow_le_besselU (conj_mem_unipotentBelow hσ' hv))
    have h_right : W (weylRatio j p q * (σ * (v * y))) =
        ψ (F.levelUnit⁻¹.val * simpleRootSum v') • W (weylRatio j p q * (σ * y)) := by
      have h_point : weylRatio j p q * (σ * (v * y)) = v' * (weylRatio j p q * (σ * y)) := by
        simp [v', weylRatio, mul_assoc]
      rw [h_point, hW.map_unipotent_mul v' hv']
    -- Conjugation by `σ` keeps the entries summed by `simpleRootSum`, and `weylRatio` is diagonal.
    have h_sum_left : simpleRootSum (σ * u * σ⁻¹) = simpleRootSum u :=
      sum_congr rfl fun a _ ↦ superdiag_conj_eq hu hσ
    have h_sum_right :
        simpleRootSum v' = simpleRootSum (weylRatio j p q * v * (weylRatio j p q)⁻¹) := by
      -- `besselFrame_castSucc` would rewrite the indices that `superdiag_conj_eq` has to match.
      simp [v', simpleRootSum, ← superdiag_conj_eq hv hσ, -besselFrame_castSucc, weylRatio_inv,
        coe_weylRatio]
    simp only [frameCorrelation, h_left, h_right]
    -- The first scalar leaves the inner product conjugated, that is inverted.
    rw [h_sum_left, h_sum_right, inner_smul_left, inner_smul_right, mul_sub, P.ψ.map_sub_eq_div,
      ← inv_eq_conj (P.norm_psi _), div_eq_mul_inv]
    ring
  · simp [weylRatio, weylElem_mul_left_comm hσ, mul_assoc]
  · -- The kernel is bounded and lives on near points, whose mass on each floor is at most the
    -- finite number `V` given by `floorMassLe_one`.
    obtain ⟨V, hV_ne, hV⟩ : ∃ V : ℝ≥0∞, V ≠ ∞ ∧ ∀ a : Fin 𝔰.n, F.FloorMassLe a V 1 := by
      refine ⟨_, ne_of_lt ?_, Γ.floorMassLe_one⟩
      grw [Γ.volume_ofSize_le]
      finiteness [Γ.loss_ne_top]
    refine ⟨.ofReal (|C| * C) * V ^ (𝔰.n - l), by finiteness, fun g y ↦ ?_⟩
    let near : Set T.G := {σ : T.G | F.IsNear (𝔰.ϱ + 2) (σ * g)}
    let modulus (σ : T.G) : ℝ≥0∞ := ‖⟪W (σ * g), W (weylRatio j p q * (σ * y))⟫_ℂ‖ₑ
    have h_supp : support modulus ⊆ near := fun σ hσ ↦
      hW.isNear_of_ne_zero fun h_zero ↦ hσ (by simp [modulus, h_zero])
    have h_bound (σ : T.G) : modulus σ ≤ .ofReal (|C| * C) := by
      unfold modulus
      grw [← ofReal_norm, norm_inner_le_norm, hC, le_abs_self C, hC]
    calc ∫⁻ σ : T.G, modulus σ ∂F.quotientMeasureFrom l
      _ = ∫⁻ σ : T.G in near, modulus σ ∂F.quotientMeasureFrom l :=
        (setLIntegral_eq_of_support_subset h_supp).symm
      _ ≤ ∫⁻ _ : T.G in near, .ofReal (|C| * C) ∂F.quotientMeasureFrom l := lintegral_mono h_bound
      _ = .ofReal (|C| * C) * F.quotientMeasureFrom l near := setLIntegral_const _ _
      _ ≤ .ofReal (|C| * C) * V ^ (𝔰.n - l) := by
        gcongr
        exact quotientMeasureFrom_isNear_le hV l g
  · -- If `g` is not near, the first factor `W (σ * g)` vanishes for all `σ` in `floorGroup l`.
    by_contra h_far
    refine h_ne (integral_eq_zero_of_ae ?_)
    filter_upwards [ae_descConv_mem ae_floorMeasure_mem] with σ hσ
    have h_zero : W (σ * g) = 0 := by
      by_contra hσg
      exact h_far ((hW.isNear_of_ne_zero hσg).of_floorGroup_mul hσ)
    simp [h_zero]

/-- For a place datum F with a gauge and a cut Bessel function W, the function (x, y) ↦ ⟨W(x), W(y)⟩
is a kernel in the sense of `New.Floors.PlaceData.IsPairingKernel` at floor j, with twisting element
1. -/
theorem Gauge.isPairingKernel_frameCorrelation_one {W : T.G → EuclideanSpace ℂ I} (Γ : Gauge F)
    (hk : F.IsCut W) (j : ℕ) : F.IsPairingKernel j (frameCorrelation W 1) 1 := by
  simpa [weylRatio] using Γ.isPairingKernel_frameCorrelation hk j 1 1

/-- Let the place datum `F` have a gauge and let `W` be a cut Bessel function. For every floor
`j : ℕ`, all sequences of units `p q : ℕ → Aˣ` and every position `x`, the double integral over
floor `j` with the weight `1`, `F.formIntegrand j p q W x 1`, is the product of two correlations
from floor `j` on, `F.partialCorrelationProduct j W x (weylRatio j p q) (weylElem j p)`. -/
lemma PlaceData.partialCorrelationProduct_eq {W : T.G → EuclideanSpace ℂ I} {x : T.G} (Γ : Gauge F)
    (hW : F.IsCut W) :
    F.partialCorrelationProduct j W x (weylRatio j p q) (weylElem j p) = F.formIntegrand j p q W x
      1 := by
  -- With weight 1 the double integral splits into the averages of the two kernels over floor `j`.
  have h_plain (y z : T.G) : F.partialCorrelation j (frameCorrelation W 1) y z =
      ∫ σ : T.G, F.partialCorrelation (j + 1) (frameCorrelation W 1) (σ * y) (σ * z) ∂F.floorMeasure
        j :=
    (Γ.isPairingKernel_frameCorrelation_one hW j).partialCorrelation_eq_integral_floorMeasure
  have h_twisted (y z : T.G) : F.partialCorrelation j (frameCorrelation W (weylRatio j p q)) y z =
      ∫ σ : T.G, F.partialCorrelation (j + 1) (frameCorrelation W (weylRatio j p q)) (σ * y) (σ * z)
        ∂F.floorMeasure j :=
    (Γ.isPairingKernel_frameCorrelation hW j p q).partialCorrelation_eq_integral_floorMeasure
  funext g
  simp [← h_plain, ← h_twisted, integral_conj, partialCorrelationProduct, mul_assoc, formIntegrand,
    integral_const_mul, integral_mul_const]

/-- The mass. For a place datum `F` with a gauge and a cut Bessel function `W`, the form of floor
`0` for the weight `1` is the integral of `|k₀(1, z)|²` in `z` against `F.groupMeasure`. Here
`k₀ = F.partialCorrelation 0 k` is the correlation from floor `0` on, an integral over all floors,
of the kernel `k = frameCorrelation W 1`. -/
theorem PlaceData.floorForm_zero_eq_integral (Γ : Gauge F) (hW : F.IsCut W) (p q : ℕ → Aˣ) :
    F.floorForm 0 p q W 1 =
      (∫ z : T.G, ‖F.partialCorrelation 0 (frameCorrelation W 1) 1 z‖ ^ 2 ∂F.groupMeasure : ℝ) := by
  -- Below floor `0` there is only the point `1`, and the Weyl elements of length `0` are trivial.
  have h_point (z : T.G) : F.formIntegrand 0 p q W z 1 1 =
      (‖F.partialCorrelation 0 (frameCorrelation W 1) 1 z‖ ^ 2 : ℝ) := by
    rw [← partialCorrelationProduct_eq Γ hW]
    simp [partialCorrelationProduct, weylRatio, Complex.mul_conj']
  have h_density : F.headDensity 0 p q = 1 := prod_range_zero _
  have h_stack : F.partialGroupMeasure 0 0 = dirac 1 := rfl
  rw [floorForm, h_density, h_stack, prod_dirac,
    (measurableEmbedding_prod_mk_right 1).integral_map, ← integral_complex_ofReal]
  simp only [h_point, toReal_one, Complex.ofReal_one, one_mul]

/-- The form of floor `b` as an integral of products of correlations from floor `b + 1` on. Let the
place datum `F` have a gauge, let `W` be a cut Bessel function whose majorant
`F.formMajorant b p q W`, for sequences of units `p q : ℕ → Aˣ`, has a finite integral against
𝖬 = `F.groupMeasure`, and let φ be measurable with |φ| ≤ 1. Let `F.floorMeasure b` be the image
under `(c, n) ↦ (v c)⁻¹ * n` of the product of `volume.withDensity ρ` and `ζ`, where `v` and `ρ` are
measurable, `ρ` is a.e. finite and `ζ` is carried by
`partialUnitriangularGroup (b + 1) ⊓ floorGroup b`. Write Z(x) for the Gram entry
`T.frameGram x b b`. Let `Ψ c` be, for almost every `c`, the product of `t`, the density
`F.headDensity b p q`, `ρ c`, φ(Z(v c)) and the integral over positions and points of
`F.partialCorrelationProduct (b + 1)` for the twist `weylRatio b p q` and the element
`weylElem b p * v c`. Then `Ψ` is integrable, and its integral is `t` times the form
`F.floorForm b p q W (φ ∘ Z)`. -/
lemma PlaceData.integrable_and_integral_succ_eq_mul_floorForm {W : T.G → EuclideanSpace ℂ I}
    (Γ : Gauge F) (hW : F.IsCut W) (b : Fin 𝔰.n) {ζ : Measure T.G} [SFinite ζ] {v : A → T.G}
    {ρ : A → ℝ≥0∞} {Ψ φ : A → ℂ} {t : ℂ} (hφ : Measurable φ) (hφ_le : ∀ c : A, ‖φ c‖ ≤ 1)
    (h_fin : ∫⁻ x : T.G, F.formMajorant b p q W x ∂F.groupMeasure ≠ ∞)
    (hζ : ∀ᵐ n : T.G ∂ζ, n ∈ partialUnitriangularGroup (b + 1) ⊓ floorGroup b)
    (hρ : ∀ᵐ c : A, ρ c < ∞)
    (h_conv : F.floorMeasure b = (volume.withDensity ρ).map (fun c : A ↦ (v c)⁻¹) ∗ₘ ζ)
    (hΨ : ∀ᵐ c : A,
      Ψ c = t *
          (F.headDensity b p q * ρ c).toReal •
            (φ (T.frameGram (v c) b b) *
              ∫ z : T.G × T.G, F.partialCorrelationProduct (b + 1) W z.1 (weylRatio b p q)
                (weylElem b p * v c)
                z.2 ∂F.groupMeasure.prod ((ζ ∗ₘ F.floorMeasure b) ∗ₘ F.partialGroupMeasure 0 b)))
    (hv : Measurable v := by fun_prop) (hρm : Measurable ρ := by fun_prop) :
    Integrable Ψ ∧ ∫ c : A, Ψ c =
      t * F.floorForm b p q W fun x : T.G ↦ φ (T.frameGram x b b) := by
  -- The substitution `τ = (v c)⁻¹ n σ`, `g' = n σ g` (`n` under `ζ`) shows that the integrand
  -- `succTerm` on floor `b + 1` and the integrand `formTerm` of `formIntegrand` have the same image
  -- measure; Fubini does the rest.
  let χ (x : T.G) : ℂ := φ (T.frameGram x b b)
  have hχ : Measurable χ := by fun_prop [frameGram]
  have hχ_left {n : T.G} (hn : n ∈ partialUnitriangularGroup (b + 1) ⊓ floorGroup b) (y : T.G) :
      χ (n * y) = χ y := congrArg φ (frameGram_diag_mul hn y).1
  have hχ_right {n : T.G} (hn : n ∈ partialUnitriangularGroup (b + 1) ⊓ floorGroup b) (y : T.G) :
      χ (y * n) = χ y := congrArg φ (frameGram_diag_mul hn y).2
  have h_plain : F.IsPairingKernel b (frameCorrelation W 1) 1 :=
    Γ.isPairingKernel_frameCorrelation_one hW b
  have h_twisted : F.IsPairingKernel b (frameCorrelation W (weylRatio b p q)) (weylRatio b p q) :=
    Γ.isPairingKernel_frameCorrelation hW b p q
  let succTerm : (T.G × T.G) × A → ℂ := fun (z, c) ↦
    χ (v c) * F.partialCorrelationProduct (b + 1) W z.1 (weylRatio b p q) (weylElem b p * v c) z.2
  let formTerm : ((T.G × T.G) × T.G) × T.G → ℂ := fun (((x, g), σ), τ) ↦
    χ (σ * τ⁻¹) * F.partialCorrelationProduct (b + 1) W x (weylRatio b p q) (σ * weylElem b p * τ⁻¹)
      (σ * g)
  have h_succ_meas : Measurable succTerm := by
    unfold succTerm
    fun_prop [partialCorrelationProduct]
  have h_form_meas : Measurable formTerm := by
    unfold formTerm
    fun_prop [partialCorrelationProduct]
  let ν : Measure (T.G × T.G) :=
    F.groupMeasure.prod ((ζ ∗ₘ F.floorMeasure b) ∗ₘ F.partialGroupMeasure 0 b)
  let μ_succ : Measure ((T.G × T.G) × A) := ν.prod (volume.withDensity ρ)
  let μ_form : Measure (((T.G × T.G) × T.G) × T.G) :=
    ((F.groupMeasure.prod (F.partialGroupMeasure 0 b)).prod (F.floorMeasure b)).prod
      (F.floorMeasure b)
  have h_invariant (x g σ τ : T.G) {s : T.G}
      (hs : s ∈ partialUnitriangularGroup (b + 1) ⊓ floorGroup b) :
      formTerm (((x, g), σ), s * τ) = formTerm (((x, g), σ), τ) := by
    simp [formTerm, partialCorrelationProduct, mul_assoc s, ← mul_assoc σ, hχ_right (inv_mem hs),
      h_twisted.partialCorrelation_mul_left (b : ℕ).le_succ hs]
  have h_subst (x g : T.G) (c : A) {σ n : T.G} (hσ : σ ∈ floorGroup b)
      (hn : n ∈ partialUnitriangularGroup (b + 1) ⊓ floorGroup b) :
      formTerm (((x, g), σ), (v c)⁻¹ * n * σ) = succTerm ((x, n * σ * g), c) := by
    simp [formTerm, succTerm, partialCorrelationProduct, weylElem_mul_left_comm hn.2,
      weylElem_mul_left_comm hσ, h_plain.partialCorrelation_mul_left (b : ℕ).le_succ hn,
      hχ_left (inv_mem hn), mul_assoc]
  -- For fixed `x`, `g`, `σ`: translate `τ` by `σ`, then expand `F.floorMeasure b` by `h_conv`.
  have h_fiber {f : ℂ → ℝ≥0∞} (hf : Measurable f) (x g : T.G) {σ : T.G} (hσ : σ ∈ floorGroup b) :
      ∫⁻ n : T.G, ∫⁻ c : A, f (succTerm ((x, n * σ * g), c)) ∂volume.withDensity ρ ∂ζ =
        ∫⁻ τ : T.G, f (formTerm (((x, g), σ), τ)) ∂F.floorMeasure b :=
    calc
      _ = ∫⁻ n : T.G, ∫⁻ c : A, f (formTerm (((x, g), σ), (v c)⁻¹ * n * σ))
            ∂volume.withDensity ρ ∂ζ :=
        lintegral_congr_of_ae_imp hζ fun n hn ↦ by simp only [h_subst x g _ hσ hn]
      _ = ∫⁻ τ : T.G, f (formTerm (((x, g), σ), τ * σ)) ∂F.floorMeasure b := by
        rw [h_conv, lintegral_mconv_symm (by fun_prop)]
        exact lintegral_congr fun n ↦ by rw [lintegral_map (by fun_prop) (by fun_prop)]
      _ = ∫⁻ τ : T.G, f (formTerm (((x, g), σ), τ)) ∂F.floorMeasure b :=
        lintegral_floorMeasure_mul_right (f := fun τ : T.G ↦ f (formTerm (((x, g), σ), τ))) le_rfl
          (fun s hs τ ↦ congrArg f (h_invariant x g σ τ hs))
          ⟨mem_partialUnitriangularGroup_of_mem_floorGroup hσ, hσ⟩
  have h_law : ProbabilityTheory.IdentDistrib succTerm formTerm μ_succ μ_form := by
    refine ⟨h_succ_meas.aemeasurable, h_form_meas.aemeasurable, ext_of_lintegral _ fun f hf ↦ ?_⟩
    rw [lintegral_map hf h_succ_meas, lintegral_map hf h_form_meas]
    -- Write both sides as iterated integrals over `x`, `g`, `σ` and the remaining variables.
    -- (As a discharger, `fun_prop` needs `with_unfolding_all` to treat the inner integrals.)
    simp (disch := with_unfolding_all fun_prop) only [μ_succ, μ_form, ν, lintegral_prod,
      lintegral_mconv_symm]
    refine lintegral_congr fun x ↦ lintegral_congr fun g ↦ ?_
    exact lintegral_congr_of_ae_imp ae_floorMeasure_mem fun σ hσ ↦ h_fiber hf x g hσ
  -- As `‖χ‖ ≤ 1`, the integral of `‖formTerm‖` is at most that of `F.formMajorant`.
  have h_form_le : ∫⁻ z : ((T.G × T.G) × T.G) × T.G, ‖formTerm z‖ₑ ∂μ_form ≤
      ∫⁻ x : T.G, F.formMajorant b p q W x ∂F.groupMeasure := by
    have hχ_le (y : T.G) : ‖χ y‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      exact ofReal_le_one.2 (hφ_le _)
    simp (disch := with_unfolding_all fun_prop) only [μ_form, lintegral_prod]
    refine lintegral_mono fun x ↦ lintegral_mono fun g ↦ ?_
    simp only [formTerm, enorm_mul]
    grw [hχ_le]
    -- The remaining double integral over floor `b` splits into the two factors `pivotL1Norm`.
    simp only [one_mul, pivotL1Norm, partialCorrelationProduct, enorm_mul, enorm_conj,
      _root_.mul_inv_rev,
      inv_inv, mul_assoc, inv_mul_cancel_left]
    exact (lintegral_lintegral_mul (by fun_prop) (by fun_prop)).le
  have h_form_int : Integrable formTerm μ_form :=
    ⟨h_form_meas.aestronglyMeasurable, h_form_le.trans_lt h_fin.lt_top⟩
  have h_succ_int : Integrable succTerm μ_succ := h_law.integrable_iff.2 h_form_int
  constructor
  · have h_int : Integrable fun c : A ↦ (ρ c).toReal • ∫ z : T.G × T.G, succTerm (z, c) ∂ν :=
      (integrable_withDensity_iff_integrable_smul' hρm hρ).1 h_succ_int.integral_prod_right
    simpa [succTerm, χ, ν, integrable_congr hΨ, mul_assoc, integral_const_mul] using
      (h_int.const_mul _).const_mul t
  · -- The integrals of `succTerm` and `formTerm` are equal; Fubini gives the two sides.
    have h_fubini : ∫ c : A, (ρ c).toReal • ∫ z : T.G × T.G, succTerm (z, c) ∂ν =
        ∫ z : T.G × T.G, ∫ σ : T.G, ∫ τ : T.G, formTerm ((z, σ), τ) ∂F.floorMeasure b
          ∂F.floorMeasure b ∂F.groupMeasure.prod (F.partialGroupMeasure 0 b) := by
      have h_eq : ∫ z, succTerm z ∂μ_succ = ∫ z, formTerm z ∂μ_form := h_law.integral_eq
      rwa [integral_prod_symm _ h_succ_int, integral_prod _ h_form_int,
        integral_prod _ h_form_int.integral_prod_left,
        integral_withDensity_eq_integral_toReal_smul hρm hρ] at h_eq
    calc ∫ c : A, Ψ c
      _ = t * ((F.headDensity b p q).toReal *
          ∫ c : A, (ρ c).toReal • ∫ z : T.G × T.G, succTerm (z, c) ∂ν) := by
        simp [succTerm, χ, ν, integral_congr_ae hΨ, mul_assoc, integral_const_mul]
      _ = t * F.floorForm b p q W χ := by
        simp only [h_fubini, formTerm, floorForm, formIntegrand]

/-- Descent. Let the place datum F have a gauge, let W be a cut Bessel function, `p q : ℕ → Aˣ`
sequences of units and a < ϱ. Let the majorant `F.formMajorant a p q W` have a finite integral
against 𝖬 = `F.groupMeasure`, and let φ be a measurable function on A with |φ| ≤ 1. Then
c ↦ φ(c) · t · 𝓘_{a+1}((p, c), (q, c); 1) is integrable, with integral t · 𝓘_a(p, q; φ(Z_{a,a})).
Here 𝓘_j(p, q; ω) is `F.floorForm j p q W ω`, (p, c) is p with the entry a replaced by c, and
Z_{a,a}(x) = h(f_a, x f_a) is a diagonal entry of `T.frameGram x`. -/
theorem Gauge.integral_weight_mul_floorForm_succ {W : T.G → EuclideanSpace ℂ I} (Γ : Gauge F)
    (hk : F.IsCut W) (a : Fin 𝔰.ϱ) (t : ℂ) {φ : A → ℂ} (hφ : Measurable φ)
    (hφ_le : ∀ c : A, ‖φ c‖ ≤ 1)
    (h_fin : ∫⁻ x : T.G, F.formMajorant a p q W x ∂F.groupMeasure ≠ ∞) :
    let f (c : A) : ℂ :=
      φ c * (t * F.floorForm (a + 1) (update p a (unitOrOne c)) (update q a (unitOrOne c)) W 1)
    Integrable f ∧
    ∫ c : A, f c =
      t * F.floorForm a p q W fun x : T.G ↦ φ (T.frameGram x a.castSucc a.castSucc) := by
  -- This is `integrable_and_integral_succ_eq_mul_floorForm` for the big cell: `F.floorMeasure a` is
  -- the law of `(floorWeyl a c)⁻¹ * n`, for `c` with the density `ρ` and `n` under
  -- `heisenbergMeasure a`.
  have h_cell : F.floorMeasure a.castSucc =
      (volume.withDensity fun c : A ↦ P.modulus c ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))).map
        (fun c : A ↦ (floorWeyl a.castSucc c)⁻¹) ∗ₘ heisenbergMeasure a.castSucc :=
          ite_eq_left a.isLt
  refine integrable_and_integral_succ_eq_mul_floorForm Γ hk a.castSucc hφ hφ_le h_fin
    (ae_mem_floorUnipotent.mono fun n hn ↦ ⟨unipotentBelow_le_partialUnitriangularGroup hn.2, hn.1⟩)
    (ae_isUnit.mono ?_) h_cell (ae_isUnit.mono ?_)
  · rintro _ ⟨c, rfl⟩
    simp [Ne.lt_top]
  · -- At a unit `c` the integrand is the one of `integrable_and_integral_succ_eq_mul_floorForm`:
    -- the Weyl element of floor `a + 1` is `weylElem a p * floorWeyl a c`, the twist `weylRatio` is
    -- unchanged, `floorWeyl a c` has Gram entry `c`, and the new factor of `headDensity` gives the
    -- density `ρ c`.
    rintro _ ⟨c, rfl⟩
    have h_density : F.headDensity (a + 1) (update p a c) (update q a c) =
        F.headDensity a p q * P.modulus (c : A) ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1))) := by
      simp [headDensity, ← sq, LT.lt.ne, ← rpow_two, -rpow_ofNat, field, prod_range,
        Fin.prod_univ_castSucc]
    have h_weyl : (weylElem (a + 1) (update p a c) : T.G) = weylElem a p * floorWeyl a (c : A) := by
      simp [weylElem_succ, (commute_weylElem _).eq]
    have h_ratio : (weylRatio (a + 1) (update p a c) (update q a c) : T.G) = weylRatio a p q := by
      simp [weylRatio, weylElem_succ, mul_assoc]
    have h_form : F.floorForm (a + 1) (update p a c) (update q a c) W 1 =
        (F.headDensity (a + 1) (update p a c) (update q a c)).toReal *
          ∫ z : T.G × T.G, F.partialCorrelationProduct (a + 1) W z.1 (weylRatio a p q)
            (weylElem a p * floorWeyl a (c : A)) z.2
            ∂F.groupMeasure.prod (F.partialGroupMeasure 0 (a + 1)) := by
      simp only [floorForm, ← h_weyl, ← h_ratio, ← partialCorrelationProduct_eq Γ hk]
    have h_stack : F.partialGroupMeasure 0 (a + 1) =
        (heisenbergMeasure a ∗ₘ F.floorMeasure a) ∗ₘ F.partialGroupMeasure 0 a := descConv_succ a
    simp only [Fin.val_castSucc, unitOrOne_val, h_form, h_density, h_stack, frameGram_floorWeyl,
      Complex.real_smul]
    ring

/-- Descent for a character: the case φ(c) = ψ(ηc) of
`New.Floors.Gauge.integral_weight_mul_floorForm_succ`, for a cut Bessel function `W` whose majorant
on floor `a` has a finite integral against `F.groupMeasure`. As a function of the common entry `c`
of `p` and `q` at `a`, ψ(ηc) times `t` times the form of floor `a + 1` with weight `1` is
integrable, and its integral is `t` times the form of floor `a` with the weight ψ(η Z(x)), where
Z(x) is the Gram entry `T.frameGram x a a`. -/
theorem Gauge.integral_psi_mul_floorForm_succ (Γ : Gauge F) (hW : F.IsCut W) (a : Fin 𝔰.ϱ) (t : ℂ)
    (η : A) (h_fin : ∫⁻ x : T.G, F.formMajorant a p q W x ∂F.groupMeasure ≠ ∞) :
    let f (c : A) : ℂ :=
      ψ (η * c) *
        (t * F.floorForm (a + 1) (update p a (unitOrOne c)) (update q a (unitOrOne c)) W 1)
    Integrable f ∧
    ∫ c : A, f c =
      t * F.floorForm a p q W fun x : T.G ↦ ψ (η * T.frameGram x a.castSucc a.castSucc) :=
  Γ.integral_weight_mul_floorForm_succ hW a t (φ := fun c : A ↦ ψ (η * c)) (by fun_prop)
    (fun c ↦ (P.norm_psi (η * c)).le) h_fin

end New.Floors

end
