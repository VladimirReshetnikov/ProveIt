import Lib.DiscreteSeries.Bruhat.ComplexPlace
import Lib.General.Measure.FibreMeasure

/-!
# Measures of a floor below fibre measures, at the place ℂ

The group `New.Shape.G₁` is the unitary group of the complex form `h` (Gram matrix `𝔰.J₁`) with
basis `e_a`, `x_i` (`i : κ`), `z`, `e*_a`: `ϱ` hyperbolic pairs `e_a, e*_a`, the `x_i` orthonormal
and `h(z, z) = -1`. The pair of index `a` has floor `a`, `z` has floor `ϱ` and the `x_i` have floor
`ϱ + 1` (`New.Floors.FloorGroups.floorOf`); `V_b`, for a floor `b : Fin 𝔰.n` (so `b ≤ ϱ`), is
spanned by the basis vectors of floor at least `b`; `oppositeIndex` exchanges the indices of `e_a`
and `e*_a`.

A vector `y` is chosen with given products with earlier basis vectors and with a given norm
`h(y, y)`. Here `New.LeFibreMeasure μ ν π b l` says that the measure `l` is at most the fibre
measure `dμ / dν` of the map `π` over the point `b`.

## Main definitions and results

* `New.Floors.leFibreMeasure_frameVector`: for the frame vector of a floor, half the quadric measure
  of the floor is at most the fibre measure.
* `New.Floors.leFibreMeasure_dualVector`: for the dual vector, half the measure of the Heisenberg
  group of the floor is at most the fibre measure.

The factor one half arises because these measures are quotients by `d(h(y, y) / 2)`. The last
section proves that the measures of the Heisenberg groups are invariant under inversion, as is the
Haar measure of the unitary group of the span of the `x_i`, carried into `G₁`.

Notions from other files:
* `New.Floors.HyperbolicBasis.floorQuadricMeasure`: The measure on a quadric in V_b: the image of
  `New.Floors.Place.quadricMeasure` with parameter β under the basis `F.floorBasis b`.
* `New.Floors.Place.heisenbergMeasure`: The measure on the Heisenberg group of floor `a`: the image
  of `dv` times the skew measure under the map that sends `(v, β)` to the isometry with
  `e*_a ↦ e*_a + v + (β - h(v, v) / 2) e_a`. For `a ≥ ϱ` it is the unit mass at `1`.
* `New.Shape.besselFrame`: The frame `(e_0, …, e_(ϱ-1), z)`, with one vector on each floor up to
  `ϱ`.
* `New.Floors.complexPlace`: The place `ℂ`: `τ = 1/2`, `δ = i/2`, `ν` the image of Lebesgue measure
  under `r ↦ r i`, modulus `‖x‖ ^ 2`, character `x ↦ exp (x - x̄)` and constant `c = π ^ 2`.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Bruhat.ComplexPlace` for sources.
-/

namespace New.Floors

open Matrix MeasureTheory Measure RealPlace FloorGroups

variable {𝔰 : Shape}

/-! ### Linear conditions and quadrics -/

/-- For the matrix `inclMatrix ℂ f` of the map that sends the basis vector at `a` to the one at
`f a`, the image of a vector `(t, v)` under the matrix of `f ⊕ g` is the sum of the images of
`t` and `v`. -/
lemma inclMatrix_sumElim_mulVec {α β ι : Type} [Fintype α] [Fintype β] [DecidableEq ι]
    (f : α → ι) (g : β → ι) (t : α → ℂ) (v : β → ℂ) :
    inclMatrix ℂ (Sum.elim f g) *ᵥ Sum.elim t v = inclMatrix ℂ f *ᵥ t + inclMatrix ℂ g *ᵥ v :=
  funext fun _ ↦ Fintype.sum_sum_type _

/-- Let `f` and `g` together enumerate the index set `ι`. On the vectors whose coordinates along
`f` are `c`, Lebesgue measure in the coordinates along `g` is at most the fibre measure of
`y ↦ y ∘ f` over `c`. -/
lemma leFibreMeasure_coords {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq α]
    [DecidableEq β] [DecidableEq ι] {f : α → ι} {g : β → ι} (hf : f.Injective)
    (hg : g.Injective) (h_compl : Set.range g = (Set.range f)ᶜ) (c : α → ℂ) :
    LeFibreMeasure volume volume (fun y : ι → ℂ ↦ y ∘ f) c
      (volume.map fun v : β → ℂ ↦ inclMatrix ℂ f *ᵥ c + inclMatrix ℂ g *ᵥ v) := by
  have h_ne (a : α) (b : β) : f a ≠ g b := fun h ↦ h_compl.subset ⟨b, rfl⟩ ⟨a, h⟩
  have h_bij : (Sum.elim f g).Bijective := by
    refine ⟨hf.sumElim hg h_ne, Set.range_eq_univ.1 ?_⟩
    rw [Set.Sum.elim_range, h_compl, Set.union_compl_self]
  let φ (p : (α → ℂ) × (β → ℂ)) : ι → ℂ := inclMatrix ℂ f *ᵥ p.1 + inclMatrix ℂ g *ᵥ p.2
  have h_vol : MeasurePreserving φ := by
    simp only [φ, ← inclMatrix_sumElim_mulVec]
    exact (measurePreserving_inclMatrix (.ofBijective _ h_bij)).comp measurePreserving_sumElim
  have h_fibre (t : α → ℂ) (v : β → ℂ) : φ (t, v) ∘ f = t := by
    ext a
    simp [φ, inclMatrix, mulVec, dotProduct, one_apply, hf.eq_iff, h_ne a]
  exact .of_measurePreserving h_vol (by fun_prop) h_fibre
    fun _ ↦ Continuous.continuousAt (by fun_prop)

lemma involutive_oppositeIndex : (oppositeIndex (𝔰 := 𝔰)).Involutive :=
  oppositeIndex_oppositeIndex

/-- The image of the indices with property `p` under the involution `oppositeIndex`, which
exchanges `e_a` with `e*_a`, consists of the indices whose opposite has property `p`. -/
lemma range_oppositeIndex_val (p : 𝔰.BesselIndex → Prop) :
    (Set.range fun i : Subtype p ↦ oppositeIndex i.1) =
      {i : 𝔰.BesselIndex | p (oppositeIndex i)} := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    simpa [involutive_oppositeIndex j.1] using j.2
  · exact fun hi ↦ ⟨⟨oppositeIndex i, hi⟩, involutive_oppositeIndex i⟩

/-- The skew element `i t / 2`, which indexes the quadric `h(v, v) = t` at the place `ℂ`. -/
noncomputable def skewOfLevel (t : ℝ) : skewAdjoint ℂ :=
  ⟨(t / 2 : ℝ) * .I, by simp [skewAdjoint.mem_iff]⟩

@[fun_prop]
lemma continuous_skewOfLevel : Continuous skewOfLevel := by fun_prop [skewOfLevel]

/-- The map `t ↦ i t / 2` carries `dt / 2` to the measure of the place `ℂ` on the skew elements. -/
lemma measurePreserving_skewOfLevel :
    MeasurePreserving skewOfLevel ((2 : ENNReal)⁻¹ • volume) complexPlace.skewMeasure := by
  have h_half : MeasurePreserving (fun t : ℝ ↦ t / 2) ((2 : ENNReal)⁻¹ • volume) volume := by
    refine ⟨by fun_prop, ?_⟩
    simp (disch := fun_prop) only [Measure.map_smul]
    simp [div_eq_inv_mul, Real.map_volume_mul_left, smul_smul, ENNReal.inv_mul_cancel]
  have h_embed : MeasurePreserving
      (fun r : ℝ ↦ (⟨r * .I, by simp [skewAdjoint.mem_iff]⟩ : skewAdjoint ℂ))
      volume complexPlace.skewMeasure :=
    ⟨by fun_prop, rfl⟩
  exact h_embed.comp h_half

/-- Multiplication of a real number `Γ` by the skew unit `δ = i / 2` of the place `ℂ` gives
`skewOfLevel Γ = i Γ / 2`. -/
lemma skewUnitMul_eq_skewOfLevel (Γ : ℂ) (hΓ : star Γ = Γ) :
    Place.skewUnitMul Γ hΓ = skewOfLevel Γ.re := by
  have h_real : (Γ.re : ℂ) = Γ := Complex.conj_eq_iff_re.1 hΓ
  ext
  simp [skewOfLevel, h_real, field]

/-- A complex number is `t / 2 + β` with `t` real and `β` skew, and Lebesgue measure is
`dt dν(β) / 2` for the measure `ν` on the skew elements. -/
lemma measurePreserving_half_add :
    MeasurePreserving (fun p : ℝ × skewAdjoint ℂ ↦ (p.1 / 2 + p.2 : ℂ))
      (((2 : ENNReal)⁻¹ • volume).prod complexPlace.skewMeasure) volume := by
  have h_half (t : ℝ) :
      (t / 2 : ℂ) = TraceOne.element * complexPlace.skewUnit⁻¹.val * (skewOfLevel t).val := by
    simp [skewOfLevel, field]
  simp only [h_half]
  exact complexPlace.measurePreserving_split.comp (measurePreserving_skewOfLevel.prod (.id _))

/-- Let `h` be the orthogonal sum of a hyperbolic plane and a hermitian form `T` (its Gram matrix is
`planeSumGram T`). Half the measure `quadricMeasure` of the quadric `h(v, v) = t₀`, which is indexed
by `skewOfLevel t₀ = i t₀ / 2`, is at most the fibre measure `dv / dh(v, v)` (`LeFibreMeasure`)
over `t₀`. -/
lemma leFibreMeasure_quadricMeasure {ι : Type} [Fintype ι] [DecidableEq ι] {T : Matrix ι ι ℂ}
    (hT : Tᴴ = T) (t₀ : ℝ) :
    LeFibreMeasure volume volume (fun v : Fin 2 ⊕ ι → ℂ ↦ (star v ⬝ᵥ planeSumGram T *ᵥ v).re) t₀
      ((2 : ENNReal)⁻¹ • Place.quadricMeasure T (skewOfLevel t₀)) := by
  have h_unit : ∀ᵐ p : (ℂ × (ι → ℂ)) × skewAdjoint ℂ ∂volume.prod complexPlace.skewMeasure,
      IsUnit p.1.1 :=
    quasiMeasurePreserving_fst.ae (quasiMeasurePreserving_fst.ae Place.ae_isUnit)
  -- The flat charts of the quadrics `h(v, v) = t` are coordinates in which the form is `t`.
  let ψ (t : ℝ) : (ℂ × (ι → ℂ)) × skewAdjoint ℂ → Fin 2 ⊕ ι → ℂ :=
    Place.flatChart T (skewOfLevel t)
  have h_form (t : ℝ) (p : (ℂ × (ι → ℂ)) × skewAdjoint ℂ) (hp : IsUnit p.1.1) :
      (star (ψ t p) ⬝ᵥ planeSumGram T *ᵥ ψ t p).re = t := by
    rw [Place.form_flatChart hT hp]
    simp [skewOfLevel, field]
  have h_cont (p : (ℂ × (ι → ℂ)) × skewAdjoint ℂ) : Continuous fun t : ℝ ↦ ψ t p := by
    simp only [ψ, Place.flatChart, continuous_pi_iff, Sum.forall, Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun _ ↦ by fun_prop, fun _ ↦ continuous_const⟩
  have h_integral (K : (Fin 2 ⊕ ι → ℂ) → ENNReal) (hK : Measurable K) :
      ∫⁻ t in Set.univ, ∫⁻ p, 2⁻¹ * K (ψ t p) ∂volume.prod complexPlace.skewMeasure =
        ∫⁻ v, K v := by
    have h_inner : Measurable fun β ↦ ∫⁻ v, K v ∂Place.quadricMeasure T β := by
      simp (disch := fun_prop) only [lintegral_map]
      fun_prop
    calc ∫⁻ t in Set.univ, ∫⁻ p, 2⁻¹ * K (ψ t p) ∂volume.prod complexPlace.skewMeasure
        = ∫⁻ t, ∫⁻ v, K v ∂Place.quadricMeasure T (skewOfLevel t) ∂(2 : ENNReal)⁻¹ • volume := by
          simp (disch := first | fun_prop | finiteness) only [ψ, restrict_univ,
            lintegral_const_mul', lintegral_map, lintegral_smul_measure, smul_eq_mul]
      _ = ∫⁻ β, ∫⁻ v, K v ∂Place.quadricMeasure T β ∂complexPlace.skewMeasure :=
          measurePreserving_skewOfLevel.lintegral_comp h_inner
      _ = ∫⁻ v, K v :=
          ((Place.isDisintegration_quadricMeasure hT).lintegral_eq (K ·.2) (by fun_prop)).symm
  have h_meas : Measurable ψ.uncurry := by fun_prop
  have h_form_ae (t : ℝ) : ∀ᵐ p ∂volume.prod complexPlace.skewMeasure,
      (2 : ENNReal)⁻¹ ≠ 0 → (star (ψ t p) ⬝ᵥ planeSumGram T *ᵥ ψ t p).re = t :=
    h_unit.mono fun p hp _ ↦ h_form t p hp
  simp (disch := fun_prop) only [← Measure.map_smul]
  rw [← withDensity_const]
  exact .of_coordinates (ψ := ψ) (w := fun _ _ ↦ 2⁻¹) (by fun_prop) h_meas measurable_const
    Filter.univ_mem (fun t _ ↦ h_form_ae t)
    (.of_forall fun p ↦ ⟨(h_cont p).continuousAt, continuousAt_const⟩)
    fun K hK ↦ (h_integral K hK).le

/-- Let `h` be the form with Gram matrix `J₁` and `V_b` the span of the basis vectors of floor at
least `b`, with Lebesgue measure `floorVolume b`. Half the measure `floorQuadricMeasure` of the
quadric `h(y, y) = t₀` in `V_b`, indexed by `skewOfLevel t₀ = i t₀ / 2` and taken in the
hyperbolic basis `complexBasis 𝔰`, is at most the fibre measure `dy / dh(y, y)` (`LeFibreMeasure`)
on `V_b`. -/
lemma leFibreMeasure_floorQuadric (b : Fin 𝔰.n) (t₀ : ℝ) :
    LeFibreMeasure (floorVolume b) volume
      (fun y : 𝔰.BesselIndex → ℂ ↦ (star y ⬝ᵥ 𝔰.J₁ *ᵥ y).re) t₀
      ((2 : ENNReal)⁻¹ • (complexBasis 𝔰).floorQuadricMeasure b (skewOfLevel t₀)) := by
  have h_herm : (hyperbolicGram (FloorPairs b 0) (1 : Matrix {i // i ≠ 𝔰.k₀} {i // i ≠ 𝔰.k₀} ℂ))ᴴ =
      hyperbolicGram (FloorPairs b 0) 1 := by
    simp [fromBlocks_conjTranspose, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      conjTranspose_fromCols_eq_fromRows_conjTranspose]
  have h_smul (μ : Measure _) : ((2 : ENNReal)⁻¹ • μ).map ((complexBasis 𝔰).floorBasis b *ᵥ ·) =
      (2 : ENNReal)⁻¹ • μ.map ((complexBasis 𝔰).floorBasis b *ᵥ ·) := by
    simp (disch := fun_prop) only [Measure.map_smul]
  rw [← (complexBasis 𝔰).map_floorBasis_volume b, ← h_smul]
  -- The floor basis pulls the form of `J₁` back to a plane plus the hyperbolic form.
  have h_form (v : Fin 2 ⊕ FloorPairs b 0 ⊕ {i // i ≠ 𝔰.k₀} ⊕ FloorPairs b 0 → ℂ) :
      (star v ⬝ᵥ planeSumGram (hyperbolicGram (FloorPairs b 0) 1) *ᵥ v).re =
        (star ((complexBasis 𝔰).floorBasis b *ᵥ v) ⬝ᵥ
          𝔰.J₁ *ᵥ (complexBasis 𝔰).floorBasis b *ᵥ v).re := by
    simp [← (complexBasis 𝔰).gram_floorBasis b, star_mulVec_dotProduct, ← Matrix.mul_assoc]
  exact .map ((leFibreMeasure_quadricMeasure h_herm t₀).congr (.of_forall h_form))
    (by fun_prop) (by fun_prop) (by fun_prop)

/-- The product `(J₁ *ᵥ y) i` of `y` with the basis vector of an index `i` of a floor below `ϱ` is
the coordinate of `y` at the opposite index. -/
lemma J₁_mulVec_apply_eq_oppositeIndex {i : 𝔰.BesselIndex} (hi : floorOf i < 𝔰.ϱ)
    (y : 𝔰.BesselIndex → ℂ) : (𝔰.J₁ *ᵥ y) i = y (oppositeIndex i) :=
  splitGram_mulVec_apply i hi

/-- The frame vector `f_b` of floor `b`, the basis vector of index `besselFrame b`. The vectors
`y` orthogonal for the form `h` of matrix `J₁` to the basis vectors of lower floors (`floorOf`)
form `V_b`. Half the measure of the quadric `h(y, y) = h(f_b, f_b)` in `V_b`, which is the default
level of `floorQuadricMeasure b`, is at most the fibre measure (`LeFibreMeasure`) of the products of
`y` with these vectors and with itself. -/
lemma leFibreMeasure_frameVector (b : Fin 𝔰.n) :
    LeFibreMeasure volume volume
      (fun y : 𝔰.BesselIndex → ℂ ↦
        (fun i : {i : 𝔰.BesselIndex // floorOf i < b} ↦ (𝔰.J₁ *ᵥ y) i, (star y ⬝ᵥ 𝔰.J₁ *ᵥ y).re))
      (fun i : {i : 𝔰.BesselIndex // floorOf i < b} ↦ 𝔰.J₁ i.1 (𝔰.besselFrame b),
        (𝔰.J₁ (𝔰.besselFrame b) (𝔰.besselFrame b)).re)
      ((2 : ENNReal)⁻¹ • (complexBasis 𝔰).floorQuadricMeasure b) := by
  have h_low (i : {i : 𝔰.BesselIndex // floorOf i < b}) : floorOf i.1 < 𝔰.ϱ := i.2.trans_le b.is_le
  have h_linear : LeFibreMeasure volume volume
      (fun (y : 𝔰.BesselIndex → ℂ) (i : {i : 𝔰.BesselIndex // floorOf i < b}) ↦ (𝔰.J₁ *ᵥ y) i) 0
      (floorVolume b) := by
    have h_compl : Set.range (Subtype.val : {i : 𝔰.BesselIndex // b ≤ floorOf i} → 𝔰.BesselIndex) =
        (Set.range fun i : {i : 𝔰.BesselIndex // floorOf i < b} ↦ oppositeIndex i)ᶜ := by
      rw [range_oppositeIndex_val, Subtype.range_coe_subtype]
      ext i
      simp [floorOf_oppositeIndex]
    have h_coords : LeFibreMeasure volume volume
        (fun (y : 𝔰.BesselIndex → ℂ) (i : {i : 𝔰.BesselIndex // floorOf i < b}) ↦
          y (oppositeIndex i)) 0 (floorVolume b) := by
      simpa [Function.comp_def] using leFibreMeasure_coords
        (involutive_oppositeIndex.injective.comp Subtype.val_injective) Subtype.val_injective
        h_compl 0
    -- The product of `y` with a basis vector of a lower floor is the opposite coordinate of `y`.
    exact h_coords.congr
      (.of_forall fun y ↦ funext fun i ↦ (J₁_mulVec_apply_eq_oppositeIndex (h_low i) y).symm)
  have h_orth :
      (fun i : {i : 𝔰.BesselIndex // floorOf i < b} ↦ 𝔰.J₁ i.1 (𝔰.besselFrame b)) = 0 := by
    funext i
    have h_floor : floorOf (oppositeIndex i.1) < b := by simp [floorOf_oppositeIndex, i.2]
    have h_ne : oppositeIndex i.1 ≠ 𝔰.besselFrame b := by grind
    simp [h_low, h_ne]
  have h_level : Place.skewUnitMul (𝔰.J₁ (𝔰.besselFrame b) (𝔰.besselFrame b)) =
      skewOfLevel (𝔰.J₁ (𝔰.besselFrame b) (𝔰.besselFrame b)).re :=
    skewUnitMul_eq_skewOfLevel _ _
  rw [h_orth, h_level]
  exact h_linear.trans (leFibreMeasure_floorQuadric b _) (by fun_prop)

/-- The vector `e*_a + v + μ e_a`, for `p = (μ, v)` with `v` in the span `V_(a+1)` of the basis
vectors of floor greater than `a`. -/
noncomputable def dualPoint (a : Fin 𝔰.ϱ)
    (p : ℂ × ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → ℂ)) : 𝔰.BesselIndex → ℂ :=
  Pi.single (eStar a) 1 + inclMatrix ℂ Subtype.val *ᵥ p.2 + p.1 • Pi.single (.inl a) 1

@[fun_prop]
lemma continuous_dualPoint (a : Fin 𝔰.ϱ) : Continuous (dualPoint a) := by fun_prop [dualPoint]

/-- The norm of `dualPoint a (μ, v) = e*_a + v + μ e_a` for the form `h` of matrix `J₁` is
`2 Re μ + h(v, v)`. Here `v` lives on the indices of floor (`floorOf`) greater than `a`, and
`inclMatrix` extends it by zero. -/
lemma re_form_dualPoint (a : Fin 𝔰.ϱ) (μ : ℂ) (v : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → ℂ) :
    (star (dualPoint a (μ, v)) ⬝ᵥ 𝔰.J₁ *ᵥ dualPoint a (μ, v)).re = 2 * μ.re +
      (star (inclMatrix ℂ Subtype.val *ᵥ v) ⬝ᵥ 𝔰.J₁ *ᵥ inclMatrix ℂ Subtype.val *ᵥ v).re := by
  -- In the expansion only the products of `e_a` with `e*_a` and of `v` with itself are nonzero.
  have h_expand : (star (dualPoint a (μ, v)) ⬝ᵥ 𝔰.J₁ *ᵥ dualPoint a (μ, v)).re = μ.re +
      (star (inclMatrix ℂ Subtype.val *ᵥ v) ⬝ᵥ 𝔰.J₁ *ᵥ inclMatrix ℂ Subtype.val *ᵥ v).re +
        μ.re := by
    simp [dualPoint, mulVec_add, mulVec_smul, inclMatrix_val_mulVec, -mulVec_mulVec]
  linarith

/-- For the form `h` of matrix `J₁`, consider the products of `y` with `e_a` and with the basis
vectors of lower floors (`floorOf`). Over their values at `e*_a` (index `eStar a`), the image of
`dμ dv` under `dualPoint a (μ, v) = e*_a + v + μ e_a` is at most the fibre measure
(`LeFibreMeasure`). -/
lemma leFibreMeasure_dualPoint (a : Fin 𝔰.ϱ) :
    LeFibreMeasure volume volume
      (fun (y : 𝔰.BesselIndex → ℂ) (i : {i : 𝔰.BesselIndex // floorOf i < a ∨ i = .inl a}) ↦
        (𝔰.J₁ *ᵥ y) i)
      (fun i : {i : 𝔰.BesselIndex // floorOf i < a ∨ i = .inl a} ↦ 𝔰.J₁ i.1 (eStar a))
      (volume.map (dualPoint a)) := by
  let I : Type := {i : 𝔰.BesselIndex // floorOf i < a ∨ i = .inl a}
  let S : Type := {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i}
  let f (i : I) : 𝔰.BesselIndex := oppositeIndex i.1
  let g : Unit ⊕ S → 𝔰.BesselIndex := Sum.elim (fun _ ↦ .inl a) Subtype.val
  let c (i : I) : ℂ := 𝔰.J₁ i.1 (eStar a)
  have h_low (i : I) : floorOf i.1 < 𝔰.ϱ := by
    rcases i.2 with h | h
    · exact h.trans a.2
    · simp [h, floorOf]
  have hf : f.Injective := involutive_oppositeIndex.injective.comp Subtype.val_injective
  have h_ne (i : S) : (.inl a : 𝔰.BesselIndex) ≠ i.1 := fun h ↦ by simpa [← h] using i.2
  have hg : g.Injective :=
    (Function.injective_of_subsingleton _).sumElim Subtype.val_injective fun _ ↦ h_ne
  have h_compl : Set.range g = (Set.range f)ᶜ := by
    rw [range_oppositeIndex_val, Set.Sum.elim_range, Subtype.range_coe_subtype]
    -- For each of the four kinds of index both sides are the same inequality of floors.
    ext (i | (i | i) | i) <;> simp <;> lia
  have h_param : MeasurePreserving fun p : ℂ × (S → ℂ) ↦ Sum.elim (fun _ : Unit ↦ p.1) p.2 :=
    measurePreserving_sumElim.comp ((volume_preserving_funUnique Unit ℂ).symm.prod (.id _))
  have h_base : inclMatrix ℂ f *ᵥ c = Pi.single (eStar a) 1 := by
    have hc : c = Pi.single ⟨.inl a, .inr rfl⟩ 1 := by
      funext i
      simp [c, I, h_low, Pi.single_apply, Subtype.ext_iff, involutive_oppositeIndex.eq_iff]
    rw [hc, mulVec_single_one]
    ext i
    simp [inclMatrix, f, one_apply, Pi.single_apply]
  have h_point : dualPoint a = (fun v ↦ inclMatrix ℂ f *ᵥ c + inclMatrix ℂ g *ᵥ v) ∘
      fun p : ℂ × (S → ℂ) ↦ Sum.elim (fun _ : Unit ↦ p.1) p.2 := by
    funext p
    have h_single : inclMatrix ℂ (fun _ : Unit ↦ (.inl a : 𝔰.BesselIndex)) *ᵥ (fun _ ↦ p.1) =
        p.1 • Pi.single (.inl a) 1 := by
      ext i
      simp [inclMatrix, mulVec, dotProduct, one_apply, Pi.single_apply]
    rw [Function.comp_apply, h_base, inclMatrix_sumElim_mulVec, h_single, dualPoint, add_assoc,
      add_comm (p.1 • _)]
  rw [h_point, ← Measure.map_map (by fun_prop) h_param.measurable, h_param.map_eq]
  exact (leFibreMeasure_coords hf hg h_compl c).congr
    (.of_forall fun y ↦ funext fun i ↦ (J₁_mulVec_apply_eq_oppositeIndex (h_low i) y).symm)

/-- The real part of a skew element of `ℂ` is zero. -/
lemma re_skewAdjoint_complex (β : skewAdjoint ℂ) : (β : ℂ).re = 0 := by
  have h_neg : star (β : ℂ) = -β := skewAdjoint.mem_iff.1 β.2
  have h_re_neg : (β : ℂ).re = -(β : ℂ).re := congrArg Complex.re h_neg
  exact self_eq_neg.1 h_re_neg

/-- The integral against the image of `dμ dv` under `dualPoint a`, in the coordinates `(v, t, β)`
with `μ = t / 2 + β - q v`, for a continuous shift `q`, `t` real and `β` skew. -/
lemma lintegral_map_dualPoint (a : Fin 𝔰.ϱ)
    {q : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → ℂ) → ℂ} (_hq : Continuous q)
    {K : (𝔰.BesselIndex → ℂ) → ENNReal} (hK : Measurable K) :
    ∫⁻ y : 𝔰.BesselIndex → ℂ, K y ∂volume.map (dualPoint a) =
      ∫⁻ v : { i : 𝔰.BesselIndex // a + 1 ≤ floorOf i } → ℂ,
        ∫⁻ p : ℝ × skewAdjoint ℂ, K (dualPoint a (p.1 / 2 + p.2 - q v, v))
        ∂((2 : ENNReal)⁻¹ • volume).prod complexPlace.skewMeasure := by
  symm
  calc ∫⁻ v, ∫⁻ p : ℝ × skewAdjoint ℂ, K (dualPoint a (p.1 / 2 + p.2 - q v, v))
          ∂((2 : ENNReal)⁻¹ • volume).prod complexPlace.skewMeasure
      = ∫⁻ v, ∫⁻ μ, K (dualPoint a (μ - q v, v)) :=
        lintegral_congr fun v ↦ measurePreserving_half_add.lintegral_comp
          (f := fun μ ↦ K (dualPoint a (μ - q v, v))) (by fun_prop)
    _ = ∫⁻ v, ∫⁻ μ, K (dualPoint a (μ, v)) :=
        lintegral_congr fun v ↦ lintegral_sub_right_eq_self (fun μ ↦ K (dualPoint a (μ, v))) (q v)
    _ = ∫⁻ y, K y ∂volume.map (dualPoint a) := by
        rw [lintegral_map hK (by fun_prop), volume_eq_prod, lintegral_prod_symm' _ (by fun_prop)]

/-- On the image under `dualPoint a (μ, v) = e*_a + v + μ e_a` of `dμ dv`, half the image of the
measure of the Heisenberg group of floor `a` under `u ↦ u e*_a` is at most the fibre measure
`dμ dv / dh(y, y)` (`LeFibreMeasure`) over the value `0`, for the form `h` of matrix `J₁`. Here
`eStar a` is the index of `e*_a`. -/
lemma leFibreMeasure_heisenbergMeasure (a : Fin 𝔰.ϱ) :
    LeFibreMeasure (volume.map (dualPoint a)) volume
      (fun y : 𝔰.BesselIndex → ℂ ↦ (star y ⬝ᵥ 𝔰.J₁ *ᵥ y).re) 0
      ((2 : ENNReal)⁻¹ • (complexPlace.heisenbergMeasure a).map
        fun u : 𝔰.G₁ ↦ (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) *ᵥ Pi.single (eStar a) 1) := by
  -- The norm is `2 Re μ + h(v, v)`; it is `t` when `μ = t / 2 + β - h(v, v) / 2` with `β` skew.
  let S : Type := {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i}
  let q (v : S → ℂ) : ℂ :=
    2⁻¹ * star (inclMatrix ℂ Subtype.val *ᵥ v) ⬝ᵥ 𝔰.J₁ *ᵥ inclMatrix ℂ Subtype.val *ᵥ v
  let ψ (t : ℝ) (p : (S → ℂ) × skewAdjoint ℂ) : 𝔰.BesselIndex → ℂ :=
    dualPoint a (t / 2 + p.2 - q p.1, p.1)
  have hq : Continuous q := by fun_prop
  have hψ : Continuous ψ.uncurry := by fun_prop
  have h_zero : ψ 0 = (fun u : 𝔰.G₁ ↦ u.val.val *ᵥ Pi.single (eStar a) 1) ∘
      TraceOne.heisenbergElem a := by
    funext p
    have h_orth : star (inclMatrix ℂ Subtype.val *ᵥ p.1) ⬝ᵥ 𝔰.J₁ *ᵥ Pi.single (eStar a) 1 = 0 := by
      simp [inclMatrix_val_mulVec]
    rw [Function.comp_apply, heisenbergElem_mulVec, h_orth]
    simp [ψ, q, dualPoint]
  have h_norm (t : ℝ) (p : (S → ℂ) × skewAdjoint ℂ) : (star (ψ t p) ⬝ᵥ 𝔰.J₁ *ᵥ ψ t p).re = t := by

    have h_re : (t / 2 + p.2 - q p.1 : ℂ).re = t / 2 -
        (star (inclMatrix ℂ Subtype.val *ᵥ p.1) ⬝ᵥ
          𝔰.J₁ *ᵥ inclMatrix ℂ Subtype.val *ᵥ p.1).re / 2 := by
      simp [q, re_skewAdjoint_complex, div_eq_inv_mul, -mulVec_mulVec]
    rw [re_form_dualPoint, h_re]
    ring
  rw [Place.heisenbergMeasure, dite_eq_left a.2, Measure.map_map (by fun_prop) (by fun_prop),
    ← h_zero]
  simp (disch := fun_prop) only [← Measure.map_smul]
  rw [← withDensity_const]
  refine .of_coordinates (w := fun _ _ ↦ 2⁻¹) (by fun_prop) hψ.measurable measurable_const
    Filter.univ_mem (fun t _ ↦ .of_forall fun p _ ↦ h_norm t p)
    (.of_forall fun p ↦ ⟨(hψ.uncurry_right p).continuousAt, continuousAt_const⟩)
    fun K hK ↦ le_of_eq ?_
  calc ∫⁻ t : ℝ in Set.univ, ∫⁻ p, 2⁻¹ * K (ψ t p) ∂volume.prod complexPlace.skewMeasure
      = 2⁻¹ * ∫⁻ t : ℝ, ∫⁻ v : S → ℂ, ∫⁻ β, K (ψ t (v, β)) ∂complexPlace.skewMeasure := by
        simp (disch := first | fun_prop | finiteness) only [restrict_univ, lintegral_const_mul',
          lintegral_prod]
    _ = 2⁻¹ * ∫⁻ v : S → ℂ, ∫⁻ t : ℝ, ∫⁻ β, K (ψ t (v, β)) ∂complexPlace.skewMeasure := by
        rw [lintegral_lintegral_swap (by fun_prop)]
    _ = ∫⁻ v, ∫⁻ p : ℝ × skewAdjoint ℂ, K (ψ p.1 (v, p.2))
          ∂((2 : ENNReal)⁻¹ • volume).prod complexPlace.skewMeasure := by
        simp (disch := first | fun_prop | finiteness) only [prod_smul_left,
          lintegral_const_mul', lintegral_prod, lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ y, K y ∂volume.map (dualPoint a) := (lintegral_map_dualPoint a hq hK).symm

/-- The dual vector `e*_a` of floor `a`, of index `eStar a`. For the form `h` of matrix `J₁`, on the
isotropic vectors `y` with `h(e_a, y) = 1` that are orthogonal to the basis vectors of lower floors
(`floorOf`), half the image of the measure of the Heisenberg group under `u ↦ u e*_a` is at most the
fibre measure (`LeFibreMeasure`) of the products of `y` with these vectors, with `e_a` and with
itself. -/
lemma leFibreMeasure_dualVector (a : Fin 𝔰.ϱ) :
    LeFibreMeasure volume volume
      (fun y : 𝔰.BesselIndex → ℂ ↦
        (fun i : {i : 𝔰.BesselIndex // floorOf i < a ∨ i = .inl a} ↦ (𝔰.J₁ *ᵥ y) i,
          (star y ⬝ᵥ 𝔰.J₁ *ᵥ y).re))
      (fun i : {i : 𝔰.BesselIndex // floorOf i < a ∨ i = .inl a} ↦ 𝔰.J₁ i.1 (eStar a), 0)
      ((2 : ENNReal)⁻¹ • (complexPlace.heisenbergMeasure a).map
        fun u : 𝔰.G₁ ↦ (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) *ᵥ Pi.single (eStar a) 1) :=
  (leFibreMeasure_dualPoint a).trans (leFibreMeasure_heisenbergMeasure a) (by fun_prop)

/-! ### Inversion -/

/-- The image under inversion of the convolution `μ ∗ₘ ν` of two s-finite measures is the
convolution of their images in the opposite order. -/
lemma inv_mconv {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] : (μ ∗ₘ ν).inv = ν.inv ∗ₘ μ.inv := by
  refine ext_of_lintegral _ fun f hf ↦ ?_
  rw [Measure.inv, lintegral_map hf measurable_inv, lintegral_mconv (by fun_prop),
    lintegral_lintegral_swap (by fun_prop), lintegral_mconv hf]
  -- Both sides are now double integrals; unfold the two inverted measures.
  simp (disch := fun_prop) only [Measure.inv, lintegral_map, _root_.mul_inv_rev]
  rw [lintegral_map (by fun_prop) measurable_inv]

/-- The Haar measure of the unitary group of the span of the vectors `x_i`, carried into `G₁` by
`embedH`, is invariant under inversion. -/
instance : (volume.map (embedH (𝔰 := 𝔰))).IsInvInvariant where
  inv_eq_self := by
    have h_comm : Inv.inv ∘ embedH (𝔰 := 𝔰) = embedH ∘ Inv.inv :=
      funext fun h ↦ (map_inv (toBesselH 𝔰 1) h).symm
    rw [Measure.inv, Measure.map_map measurable_inv (by fun_prop), h_comm,
      ← Measure.map_map (by fun_prop) measurable_inv, map_inv_eq_self]

/-- The measure of the Heisenberg group of floor `l` in `G₁` (the unit mass at `1` for `l ≥ ϱ`) is
invariant under inversion. -/
instance (l : ℕ) : (complexPlace.heisenbergMeasure l : Measure 𝔰.G₁).IsInvInvariant := by
  refine ⟨?_⟩
  by_cases hl : l < 𝔰.ϱ
  swap
  · simp [Place.heisenbergMeasure, hl, Measure.inv]
  · rw [Place.heisenbergMeasure, dite_eq_left hl]
    -- Inversion sends the parameters `(v, β)` to `(-v, c - β)`, with `c` independent of `β`.
    refine ext_of_lintegral _ fun f hf ↦ ?_
    have h_meas : Measurable (TraceOne.heisenbergElem (T := 𝔰.middleGram (1 : ℂ)) ⟨l, hl⟩) :=
      continuous_heisenbergElem.measurable
    simp (disch := fun_prop) only [Measure.inv, lintegral_map]
    rw [lintegral_prod _ (Measurable.aemeasurable (by fun_prop)),
      lintegral_prod _ (Measurable.aemeasurable (by fun_prop)), ← lintegral_neg_eq_self]
    refine lintegral_congr fun v ↦ ?_
    simp only [heisenbergElem_inv, neg_neg]
    exact lintegral_sub_left_eq_self (fun β ↦ f (TraceOne.heisenbergElem ⟨l, hl⟩ (v, β))) _

end New.Floors
