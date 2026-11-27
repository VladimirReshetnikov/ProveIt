import Lib.CM.Sigma.Basic
import Lib.DiscreteSeries.Bessel.FrameFibre
import Lib.DiscreteSeries.Bruhat.FloorFibre
import Lib.DiscreteSeries.Bruhat.SphereFibres
import Lib.Weil.Construction.HeisenbergModel
import New.Spanning.Bessel.Basic
import New.Spanning.Frames.Correlations

/-!
# Floor measures at the complex place: Haar measure, place datum and gauge

The group `New.Shape.G₁` is the unitary group of the complex form with basis `e_a`, `x_i` (`i : κ`),
`z`, `e*_a`. Here the `e_a, e*_a` are `ϱ` hyperbolic pairs, the `x_i` are orthonormal and
`h(z, z) = -1`. The filling argument at a place needs a place datum (`New.Floors.PlaceData`) and a
gauge (`New.Floors.Gauge`). A place datum consists of measures on the floors of a tower of
subgroups, a set of close pairs of vectors and a box; a gauge consists of sizes in which volumes are
bounded by powers of one constant. The place `ℂ` lies over a real place of the totally real field,
and the docstrings call it a real place.

## Main definitions and results

* `New.Floors.ascConv_heisenbergMeasure_eq_besselHaar`: the convolution of the measures
  `New.Floors.Place.heisenbergMeasure` on the Heisenberg groups of the floors is
  `New.Shape.besselHaar`, Lebesgue measure in the free entries of the unipotent group
  `New.Shape.Form.besselU`. Both are invariant, and the Gaussian `New.Floors.dualColumnGaussian`
  fixes the constant.
* `New.Floors.RealPlaceSizes.complexData`, `New.Floors.RealPlaceSizes.gauge`: the place datum and
  the gauge at `ℂ`.
* `New.Floors.RealPlaceSizes.haarRatio`,
  `New.Floors.RealPlaceSizes.haarRatio_ne_zero_and_groupMeasure_eq_smul`: the product measure
  `New.Floors.PlaceData.groupMeasure` over all floors is a finite positive multiple of the Haar
  measure, and the multiple is bounded by a ratio of volumes `New.volU` of compact unitary groups.
  The bound (`New.Floors.RealPlaceSizes.inv_groupMeasure_le`) compares two descriptions of the fibre
  measure of the Gram map on tuples `(y_0, y*_0, …, y_(ϱ-1), y*_(ϱ-1), y_ϱ)`: by Haar measure, and
  by choosing the vectors in turn.
* `New.Floors.RealPlaceSizes.exists_orthonormal_mul_eq_zero_and_fixed`: common subspaces of two
  points at `ℂ`, orthogonal to `n` given vectors, of each rank up to the free rank less `3 n`.
* `New.Floors.lengthAt`, `New.Floors.inducedLength`, `New.Floors.realDepth`: the Euclidean length at
  a point of `G₁`, the induced length on a quotient along the frame, and the depth of a frame vector
  as the infimum of |ζ|_g² + |ζ|_g'² over its duals ζ.
* `New.Floors.RealPlaceSizes.stableProducts_eq`, `New.Floors.RealPlaceSizes.depth_eq`: the set 𝔡_a
  (`New.Floors.PlaceData.stableProducts`) is a disc, and its inverse area
  `New.Floors.PlaceData.depth` is `New.Floors.realDepth` divided by π.

Notions from other files:
* `New.Floors.complexPlace`: The place `ℂ`: `τ = 1/2`, `δ = i/2`, `ν` the image of Lebesgue measure
  under `r ↦ r i`, modulus `‖x‖ ^ 2`, character `x ↦ exp (x - x̄)` and constant
  `kernelBound = π ^ 2`.
* `New.Floors.cellChart`: The chart of floor `l`: if `l = ϱ` and `c ≠ 0`, the boost with parameter
  `c / min 1 ‖c‖`; otherwise the Weyl element `floorWeyl l c`, which is `1` if `l ≥ ϱ` or `c = 0`.
* `New.Floors.cellLaw`: for floor l, the image of the measure with density `cellDensity 𝔰 l` on ℂ
  under `c ↦ (cellChart 𝔰 l c)⁻¹`; the chart is a Weyl element below the top floor ϱ.
* `New.Floors.PlaceData.floorMeasure`: the measure θ_l of floor l of place data; `groupMeasure` is
  𝖬 = (η_{ϱ+1} ∗ θ_{ϱ+1}) ∗ ⋯ ∗ (η₀ ∗ θ₀), with η_l = `Place.heisenbergMeasure l`.
* `New.LeGramFibre J E m`: the law of `g E` under `m` is at most the fibre measure of the Gram map
  on the tuples with the Gram matrix of `E`.

## Relation to the literature

See `Lib.DiscreteSeries.Bruhat.ComplexPlace` for sources.
-/

noncomputable section

/-!
## Convolution of the measures of the Heisenberg groups

The pair of index `a` has floor `a`, `z` has floor `ϱ` and the `x_i` have floor `ϱ + 1`
(`New.Floors.FloorGroups.floorOf`).
-/

namespace New.Floors

open Matrix MeasureTheory Measure RealPlace Fintype Real FloorGroups Finset

variable {𝔰 : Shape}

/-- The Gaussian exp(−π Σ_{b<l}(Σ_i |g_{i,e*_b}|² + (Im g_{e_b,e*_b})²)) on G₁, the inner sum over
the indices i of floor greater than b. -/
noncomputable abbrev dualColumnGaussian (l : ℕ) (g : 𝔰.G₁) : ENNReal :=
  ‖rexp
    (-π *
      ∑ b : Fin 𝔰.ϱ with b.val < l,
        let w : 𝔰.BesselIndex → ℂ := g.val.val *ᵥ Pi.single (eStar b) 1
        ∑ i : 𝔰.BesselIndex with b < floorOf i, ‖w i‖ ^ 2 + (w (Sum.inl b)).im ^ 2)‖ₑ

/-- The Heisenberg element of floor `a` with vector `v` (on the floors above `a`) and skew parameter
`β` sends `e*_a` to `e*_a + v + (β - τ h(v, v)) e_a`, where `v` is extended by zero. -/
lemma heisenbergElem_mulVec_single_eStar (a : Fin 𝔰.ϱ)
    (v : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → ℂ) (β : skewAdjoint ℂ) :
    ((TraceOne.heisenbergElem a (v, β) : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) *ᵥ
        Pi.single (eStar a) 1 =
      Pi.single (eStar a) 1 + inclMatrix ℂ Subtype.val *ᵥ v +
        (β - TraceOne.element * star (inclMatrix ℂ Subtype.val *ᵥ v) ⬝ᵥ
          𝔰.J₁ *ᵥ inclMatrix ℂ Subtype.val *ᵥ v) • Pi.single (Sum.inl a) 1 := by
  rw [heisenbergElem_mulVec]
  simp [inclMatrix_val_mulVec]

/-- A Heisenberg element of floor `a` fixes the basis vectors `e*_b` with `b < a`. -/
lemma heisenbergElem_mulVec_single_eStar_of_lt {a b : Fin 𝔰.ϱ} (hb : b < a)
    (v : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → ℂ) (β : skewAdjoint ℂ) :
    ((TraceOne.heisenbergElem a (v, β) : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) *ᵥ
        Pi.single (eStar b) 1 =
      Pi.single (eStar b) 1 := by
  rw [heisenbergElem_mulVec]
  simp [inclMatrix_val_mulVec, hb.ne', hb.not_gt]

/-- Let `ν` lie in the unitriangular group `unipotentBelow a` of the floors below `a`, and let `n`
be the Heisenberg element of floor `a` with vector `v` and skew parameter `β`. The Gaussian
`dualColumnGaussian` in the free entries of the columns `e*_b`, `b ≤ a`, of `ν n` is
`exp (-π (|v|² + (Im β)²))` times the Gaussian in those of the columns `e*_b`, `b < a`, of `ν`. -/
lemma dualColumnGaussian_succ_mul_heisenbergElem {a : Fin 𝔰.ϱ} {ν : 𝔰.G₁}
    (hν : ν ∈ unipotentBelow a)
    (v : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → ℂ) (β : skewAdjoint ℂ) :
    dualColumnGaussian (a + 1) (ν * TraceOne.heisenbergElem a (v, β)) =
      ‖rexp (-π * (∑ i : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i}, ‖v i‖ ^ 2 +
        (β : ℂ).im ^ 2))‖ₑ * dualColumnGaussian a ν := by
  -- The element `n` puts `v` and `Im β` into the free entries of column `e*_a` and fixes the
  -- earlier vectors `e*_b`; the element `ν` keeps the free entries of column `e*_a`.
  let col : 𝔰.BesselIndex → ℂ :=
    ((TraceOne.heisenbergElem a (v, β) : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) *ᵥ
      Pi.single (eStar a) 1
  have col_free (i : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i}) : col i = v i := by
    have h_ne (j : 𝔰.BesselIndex) (hj : floorOf j = a) : i.val ≠ j :=
      fun h ↦ by simpa [h, hj] using i.property
    simp only [col, heisenbergElem_mulVec_single_eStar]
    simp [inclMatrix_val_mulVec, i.property, h_ne (.inl a) rfl, h_ne (eStar a) rfl]
  have col_im : (col (.inl a)).im = (β : ℂ).im := by
    have form_real (w : 𝔰.BesselIndex → ℂ) : (star w ⬝ᵥ 𝔰.J₁ *ᵥ w).im = 0 :=
      Complex.conj_eq_iff_im.1 (star_dotProduct_mulVec_comm IsHermitianUnit.conjTranspose_eq w w)
    simp only [col, heisenbergElem_mulVec_single_eStar]
    simp [inclMatrix_val_mulVec, -mulVec_mulVec, form_real]
  have col_zero (b : Fin 𝔰.ϱ) (hb : b.val < a) : col (eStar b) = 0 := by
    simp only [col, heisenbergElem_mulVec_single_eStar]
    simp [inclMatrix_val_mulVec, Fin.ne_of_lt hb, Fin.not_lt.2 hb.le]
  have col_kept (i : 𝔰.BesselIndex) (hi : a ≤ floorOf i) : (ν *ᵥ col) i = col i :=
    unipotentBelow_mulVec_apply hν col_zero i (.inl hi)
  have h_erase : ({b : Fin 𝔰.ϱ | b.val < a + 1} : Finset (Fin 𝔰.ϱ)).erase a =
      ({b : Fin 𝔰.ϱ | b.val < a} : Finset (Fin 𝔰.ϱ)) := by grind
  push_cast [dualColumnGaussian, ← mulVec_mulVec]
  -- Split off the term of column `e*_a` and compare the summands.
  rw [← add_sum_erase (a := a) _ _ (by simp), h_erase, mul_add, exp_add, enorm_mul,
    ← sum_subtype_eq_sum_filter, subtype_univ]
  congr 4
  · congr 1
    · exact sum_congr rfl fun i _ ↦ by rw [col_kept i i.property.le, col_free]
    · rw [col_kept (.inl a) le_rfl, col_im]
  · exact sum_congr rfl fun b hb ↦ by
      rw [heisenbergElem_mulVec_single_eStar_of_lt (by simpa using hb)]

/-- At the place `ℂ` the measure `heisenbergMeasure a` on the Heisenberg group of floor `a < ϱ` is
the image of Lebesgue measure in `(v, r)` under the map to the Heisenberg element with vector `v`
and skew parameter `r i`. -/
lemma lintegral_heisenbergMeasure_complex (a : Fin 𝔰.ϱ) {f : 𝔰.G₁ → ENNReal} (hf : Measurable f) :
    ∫⁻ g : 𝔰.G₁, f g ∂complexPlace.heisenbergMeasure a =
      ∫⁻ x : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → ℂ) × ℝ,
        f (TraceOne.heisenbergElem a (x.1, ⟨x.2 * .I, by simp [skewAdjoint.mem_iff]⟩)) := by
  let skew (r : ℝ) : skewAdjoint ℂ := ⟨r * .I, by simp [skewAdjoint.mem_iff]⟩
  have h_skew : MeasurePreserving skew volume complexPlace.skewMeasure := ⟨by fun_prop, rfl⟩
  rw [Place.heisenbergMeasure, dite_eq_left a.is_lt, lintegral_map hf (by fun_prop)]
  exact (((MeasurePreserving.id volume).prod h_skew).lintegral_comp (by fun_prop)).symm

/-- Let `l ≤ ϱ`. The Gaussian `dualColumnGaussian l` has integral `1` against the convolution
`η_0 ∗ ⋯ ∗ η_(l-1)` of the measures `heisenbergMeasure` of the floors below `l`. -/
lemma lintegral_dualColumnGaussian_ascConv {l : ℕ} (hl : l ≤ 𝔰.ϱ) :
    ∫⁻ ν : 𝔰.G₁, dualColumnGaussian l ν ∂ascConv complexPlace.heisenbergMeasure l = 1 := by
  -- Induction on `l`: the Gaussian factors into a standard Gaussian on the Heisenberg group of the
  -- last floor and the Gaussian of the lower floors.
  induction l with
  | zero => simp [ascConv, dualColumnGaussian]
  | succ a ih =>
    lift a to Fin 𝔰.ϱ using hl
    let η : Measure 𝔰.G₁ := ascConv complexPlace.heisenbergMeasure a
    let n (x : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → ℂ) × ℝ) : 𝔰.G₁ :=
      TraceOne.heisenbergElem a (x.1, ⟨x.2 * .I, by simp [skewAdjoint.mem_iff]⟩)
    let gauss (x : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → ℂ) × ℝ) : ENNReal :=
      ‖rexp (-π * (∑ i : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i}, ‖x.1 i‖ ^ 2 + x.2 ^ 2))‖ₑ
    calc
      ∫⁻ ν, dualColumnGaussian (a + 1) ν ∂η ∗ₘ complexPlace.heisenbergMeasure a
        = ∫⁻ x, ∫⁻ ν, dualColumnGaussian (a + 1) (ν * n x) ∂η := by
        rw [lintegral_mconv_symm (by fun_prop),
          lintegral_heisenbergMeasure_complex a (by fun_prop)]
      _ = ∫⁻ x, ∫⁻ ν, gauss x * dualColumnGaussian a ν ∂η := by
        refine lintegral_congr fun x ↦
          lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν hν ↦ ?_
        rw [dualColumnGaussian_succ_mul_heisenbergElem hν]
        simp [gauss]
      _ = (∫⁻ x, gauss x) * ∫⁻ ν, dualColumnGaussian a ν ∂η :=
        lintegral_lintegral_mul (by fun_prop) (by fun_prop)
      _ = 1 := by rw [lintegral_gaussian_eq_one, ih a.is_lt.le, one_mul]

open scoped Classical in
/-- For `y` in G₁, the Gaussian `dualColumnGaussian ϱ` at `y⁻¹` is the standard Gaussian in the
entries of `y` in the rows `e_a`: the complex entries at the positions `IsFreeEntry` (column `e_b`
or `e*_b` with `b > a`, or a middle column) and the imaginary parts of the entries at
`(e_a, e*_a)`. -/
lemma dualColumnGaussian_inv (y : 𝔰.G₁) :
    dualColumnGaussian 𝔰.ϱ y⁻¹ =
      ‖rexp (-π *
        (∑ p : Fin 𝔰.ϱ × 𝔰.BesselIndex with IsFreeEntry p,
            ‖(y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (Sum.inl p.1) p.2‖ ^ 2 +
          ∑ a : Fin 𝔰.ϱ,
            ((y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (Sum.inl a) (eStar a)).im ^ 2))‖ₑ := by
  -- Since `y⁻¹ = J y* J`, column `e*_a` of `y⁻¹` is row `e_a` of `y` up to conjugation, signs and
  -- the exchange of `e_b` with `e*_b`.
  rw [dualColumnGaussian, U.coe_inv IsHermitianInvolution.mul_self]
  congr 3
  simp [sum_filter, sum_prod_type, splitGram, middleGram, mul_apply, Matrix.one_apply,
    sum_add_distrib]
  ring

/-- The function `y ↦ dualColumnGaussian ϱ y⁻¹` has integral `1` against the Haar measure
`besselHaar` of the unipotent group 𝖴 = `besselU`. -/
lemma lintegral_dualColumnGaussian_inv_besselHaar :
    ∫⁻ y : (𝔰.middleGram (1 : ℂ)).besselU,
      dualColumnGaussian 𝔰.ϱ (y : 𝔰.G₁)⁻¹ ∂𝔰.besselHaar = 1 := by
  classical
  -- The free entries carry `besselHaar` to Lebesgue measure.
  let gauss (x : (Subtype (IsFreeEntry (𝔰 := 𝔰)) → ℂ) × (Fin 𝔰.ϱ → ℝ)) : ENNReal :=
    ‖rexp (-π * (∑ p, ‖x.1 p‖ ^ 2 + ∑ a, x.2 a ^ 2))‖ₑ
  calc
    ∫⁻ y : (𝔰.middleGram (1 : ℂ)).besselU, dualColumnGaussian 𝔰.ϱ (y : 𝔰.G₁)⁻¹ ∂𝔰.besselHaar
      = ∫⁻ y, gauss (freeEntries IsFreeEntry (y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ))
          ∂𝔰.besselHaar := by
      refine lintegral_congr fun y ↦ ?_
      rw [dualColumnGaussian_inv, ← sum_subtype_eq_sum_filter, subtype_univ]
      simp [gauss]
    _ = ∫⁻ x, gauss x := measurePreserving_freeEntries_besselHaar.lintegral_comp (by fun_prop)
    _ = 1 := lintegral_gaussian_eq_one

/-- The Haar measure `New.Shape.besselHaar` of the unipotent group 𝖴 = `besselU`, carried to G₁ by
the inclusion, is the convolution η₀ ∗ ⋯ ∗ η_{ϱ−1} of the measures
`New.Floors.Place.heisenbergMeasure` on the Heisenberg groups of the floors. -/
lemma ascConv_heisenbergMeasure_eq_besselHaar :
    ascConv complexPlace.heisenbergMeasure 𝔰.ϱ = 𝔰.besselHaar.map .val := by
  -- Both measures are invariant under translation by `𝖴` and give a Gaussian the integral `1`.
  refine ext_of_lintegral _ fun f hf ↦ ?_
  set η : Measure 𝔰.G₁ := ascConv complexPlace.heisenbergMeasure 𝔰.ϱ
  have h_gauss_η : ∫⁻ x : 𝔰.G₁, dualColumnGaussian 𝔰.ϱ x ∂η = 1 :=
    lintegral_dualColumnGaussian_ascConv le_rfl
  have h_gauss_haar : ∫⁻ y : (𝔰.middleGram 1).besselU,
    dualColumnGaussian 𝔰.ϱ y⁻¹.val ∂𝔰.besselHaar = 1 :=
    lintegral_dualColumnGaussian_inv_besselHaar
  have h_inv (y : (𝔰.middleGram 1).besselU) : η ∗ₘ dirac y.val = η ∧ dirac y.val ∗ₘ η = η :=
    ascConv_heisenbergMeasure_invariant ((unipotentBelow_eq_besselU le_rfl).ge y.property)
  have h_right (y : (𝔰.middleGram (1 : ℂ)).besselU) :
      ∫⁻ x : 𝔰.G₁, f (x * y) ∂η = ∫⁻ x : 𝔰.G₁, f x ∂η := by
    simp (disch := fun_prop) only [← lintegral_mconv_dirac, h_inv]
  have h_left (y : (𝔰.middleGram (1 : ℂ)).besselU) :
      ∫⁻ x : 𝔰.G₁, dualColumnGaussian 𝔰.ϱ (y⁻¹.val * x) ∂η = 1 := by
    simp (disch := fun_prop) only [← lintegral_dirac_mconv, h_inv, h_gauss_η]
  calc
    ∫⁻ x, f x ∂η = ∫⁻ y, ∫⁻ x, dualColumnGaussian 𝔰.ϱ y⁻¹.val * f (x * y) ∂η ∂𝔰.besselHaar := by
      simp (disch := fun_prop) only [lintegral_const_mul, h_right, lintegral_mul_const,
        h_gauss_haar, one_mul]
    _ = ∫⁻ x, ∫⁻ y, dualColumnGaussian 𝔰.ϱ y⁻¹.val * f (x * y) ∂𝔰.besselHaar ∂η :=
      lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ x, ∫⁻ y, dualColumnGaussian 𝔰.ϱ (y⁻¹.val * x) * f y ∂𝔰.besselHaar ∂η := by
      -- almost every `x` lies in `𝖴`; substitute `x * y` for `y`
      refine lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow fun x hx ↦ ?_
      simpa using lintegral_mul_left_eq_self (μ := 𝔰.besselHaar)
        (fun y ↦ dualColumnGaussian 𝔰.ϱ (y⁻¹.val * x) * f y) ⟨x, unipotentBelow_le_besselU hx⟩
    _ = ∫⁻ y, ∫⁻ x, dualColumnGaussian 𝔰.ϱ (y⁻¹.val * x) * f y ∂η ∂𝔰.besselHaar :=
      lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ x, f x ∂𝔰.besselHaar.map Subtype.val := by
      simp (disch := fun_prop) only [lintegral_mul_const, h_left, one_mul, lintegral_map]

end New.Floors

/-!
## The place datum and the gauge at the complex place

`∗ₘ` is convolution of measures. In comments 𝖴 is the unipotent group `New.Shape.Form.besselU` and H
the image of `U(κ)` in `G₁`.
-/

section RealPlaceGauge

namespace New.Floors

open MeasureTheory Measure Matrix Real Metric Fintype ENNReal RealPlace Sum Norms.L2Operator
  FloorGroups WithLp

variable (𝔰 : Shape) (ρ : ℝ)

/-- The numerical hypotheses at a real place on the shape `𝔰`, a box radius `ρ`, an exponent `s` and
a base `b`. Here ϱ is the number of hyperbolic planes, n = ϱ + 1, k = |κ| is the rank of the
positive summand X₀ and r the rank of the whole space: ρ = b^(6n+2) ≥ 8r with b ≥ 2,
k = s + 3n + 6 ≥ n⁷, s > 10⁹n³ and ϱ ≥ 10⁸. -/
structure RealPlaceSizes (s : ℕ) (b : ℝ) where
  /-- The box radius is ρ = b^(6n+2). -/
  rho_eq : ρ = b ^ (6 * 𝔰.n + 2)
  /-- The box radius ρ is at least eight times the rank r. -/
  eight_mul_r_le_rho : 8 * 𝔰.r ≤ ρ
  /-- The rank of X₀ is s + 3n + 6. -/
  k_eq : 𝔰.k = s + 3 * 𝔰.n + 6
  /-- The exponent s exceeds 10⁹ n³. -/
  mul_cube_lt_s : 10 ^ 9 * 𝔰.n ^ 3 < s
  /-- The rank of X₀ is at least n⁷. -/
  pow_seven_le_k : 𝔰.n ^ 7 ≤ 𝔰.k
  /-- The number ϱ is at least 10⁸. -/
  ten_pow_le_varrho : 10 ^ 8 ≤ 𝔰.ϱ
  /-- The base b is at least 2. -/
  two_le_b : 2 ≤ b

variable {𝔰 : Shape} {ρ : ℝ} {s : ℕ} {b : ℝ} {L : ℝ} (hF : RealPlaceSizes 𝔰 ρ s b)

/-- If the squared Euclidean lengths of two vectors add up to less than `1`, all their entries have
modulus at most `1`. -/
lemma norm_apply_le_one_of_sq_add_sq_lt_one {ι : Type} [Fintype ι] {u v : ι → ℂ}
    (h : ‖toLp 2 u‖ ^ 2 + ‖toLp 2 v‖ ^ 2 < 1) (i : ι) : ‖u i‖ ≤ 1 ∧ ‖v i‖ ≤ 1 := by
  have hu : ‖toLp 2 u‖ ≤ 1 := by nlinarith [sq_nonneg ‖toLp 2 v‖]
  have hv : ‖toLp 2 v‖ ≤ 1 := by nlinarith [sq_nonneg ‖toLp 2 u‖]
  exact ⟨(PiLp.norm_apply_le (toLp 2 u) i).trans hu, (PiLp.norm_apply_le (toLp 2 v) i).trans hv⟩

/-- The Haar measure of the compact group `U(κ)`, carried into `𝔰.G₁` by `embedH`, is invariant
under right translation by the image of an element `u` of `U(κ)`. -/
lemma map_embedH_mconv_dirac (u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
    volume.map (embedH (𝔰 := 𝔰)) ∗ₘ dirac (embedH u) = volume.map embedH := by
  -- `embedH` abbreviates the homomorphism `toBesselH 𝔰 1`.
  change volume.map (toBesselH 𝔰 1) ∗ₘ dirac (toBesselH 𝔰 1 u) = volume.map (toBesselH 𝔰 1)
  rw [← map_dirac, ← map_mconv_monoidHom (toBesselH 𝔰 1) (by fun_prop), mconv_dirac,
    map_mul_right_eq_self]

/-- The place datum at `ℂ`: the unit `levelUnit = 1`, the close pairs `(ω₁, ω₂)` with
`|ω₁|² + |ω₂|² < 1` for the Euclidean length, the box `‖x‖ ≤ ρ` in operator norm, all positions
allowed, `measureH` the Haar measure of the compact group `U(κ)` carried into `𝔰.G₁`, and
`topFloorMeasure` the law `cellLaw ϱ` of floor `ϱ` convolved with `measureH`. -/
@[simps toHyperbolicBasis topFloorMeasure measureH levelUnit closePairs boxSet positions]
def RealPlaceSizes.complexData : PlaceData {i // i ≠ 𝔰.k₀} (𝔰.middleGram (1 : ℂ)) 0 where
  toHyperbolicBasis := complexBasis 𝔰
  topFloorMeasure := cellLaw 𝔰.ϱ ∗ₘ volume.map embedH
  measureH := volume.map embedH
  levelUnit := 1
  closePairs := {u : (𝔰.BesselIndex → ℂ) × (𝔰.BesselIndex → ℂ) |
    ‖toLp 2 u.1‖ ^ 2 + ‖toLp 2 u.2‖ ^ 2 < 1}
  boxSet := {x : (𝔰.middleGram (1 : ℂ)).G | ‖x.val.val‖ ≤ ρ}
  positions := Set.univ
  topFloorMeasure_mem_and_map_eq := by
                        refine ⟨ae_mem_mconv ?_ ?_ measurableSet_floorGroup,
                          map_orbitPoint_cellLaw_top (by simp [hF.k_eq])⟩
                        · exact (ae_map_iff (by fun_prop) measurableSet_floorGroup).2
                            (.of_forall fun _ ↦ inv_mem cellChart_mem_floorGroup)
                        · exact (ae_map_iff (by fun_prop) measurableSet_floorGroup).2
                            (.of_forall embedH_mem_floorGroup)
  measureH_mem_and_invariant_and_le_one := by
                            refine ⟨?_, fun s hs ↦ ?_, fun _ ↦ prob_le_one⟩
                            · exact (ae_map_iff (by fun_prop) measurableSet_floorGroup).2
                                (.of_forall toBesselH_mem)
                            · obtain ⟨u, rfl⟩ : ∃ u : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
                                s = toBesselH 𝔰 1 u :=
                                exists_eq_toBesselH hs isUnit_one
                              exact map_embedH_mconv_dirac u
  star_levelUnit := by simp
  isOpen_closePairs_and_zero_mem_and_isCompact_closure := by
                                         refine ⟨isOpen_lt (by fun_prop) continuous_const, by simp,
                                           ((isBounded_closedBall (x := 0) (r := 1)).subset fun u
                                             hu ↦ ?_).isCompact_closure⟩
                                         simpa [Prod.norm_def, pi_norm_le_iff_of_nonneg, forall_and]
                                           using
                                           norm_apply_le_one_of_sq_add_sq_lt_one hu
  isCompact_boxSet_and_measurableSet_positions := ⟨isCompact_U_norm_le ρ, MeasurableSet.univ⟩

/-- A chosen constant c in [0, ∞] with 𝖬 = c · dy, where 𝖬 is the product `groupMeasure` of the
measures of all floors of the place datum at ℂ and dy is the Haar measure `volume` on G₁. -/
def RealPlaceSizes.haarRatio : ℝ≥0∞ :=
  (exists_eq_smul_haar volume hF.complexData.isMulRightInvariant_groupMeasure).choose

/-- Assume the numerical hypotheses `hF` on the ranks and the box radius, and let
`θ_l = floorMeasure l` be the measure of floor `l` of the place datum `complexData` at `ℂ`. Let `E`
be the tuple of the basis vectors of the floors below `l`, and `E'` the same tuple with the frame
vector `besselFrame l` of floor `l` added; `q` is its set of indices. If the image of `m` under
`g ↦ g E` is at most the fibre measure of the Gram map over the Gram matrix of `E` (`LeGramFibre`),
then the same holds for `E'` and the image of the product of `m` and `θ_l / 2` under
`(g, σ) ↦ g σ⁻¹ E'`. -/
lemma RealPlaceSizes.leGramFibre_mconv_floorMeasure (hF : RealPlaceSizes 𝔰 ρ s b) (l : Fin 𝔰.n)
    {m : Measure 𝔰.G₁} [SFinite m] {q : 𝔰.BesselIndex → Prop} [DecidablePred q]
    (hq : ∀ i : 𝔰.BesselIndex, q i ↔ floorOf i < l ∨ i = 𝔰.besselFrame l)
    (hm : LeGramFibre 𝔰.J₁
      (inclMatrix ℂ (Subtype.val : {i : 𝔰.BesselIndex // floorOf i < l} → 𝔰.BesselIndex)) m) :
    LeGramFibre 𝔰.J₁ (inclMatrix ℂ (Subtype.val : Subtype q → 𝔰.BesselIndex))
      (m ∗ₘ ((2⁻¹ : ℝ≥0∞) • (hF.complexData.floorMeasure l).inv)) := by
  have h_law : (hF.complexData.floorMeasure l).inv.map
      (fun g : 𝔰.G₁ ↦ g *ᵥ Pi.single (𝔰.besselFrame l) (1 : ℂ)) =
        (complexBasis 𝔰).floorQuadricMeasure l := by
    rw [Measure.inv, Measure.map_map (by fun_prop) measurable_inv]
    exact (hF.complexData.measurePreserving_orbitPoint l).map_eq
  have h_mem : ∀ᵐ g : 𝔰.G₁ ∂(hF.complexData.floorMeasure l).inv, g ∈ floorGroup l :=
    (ae_map_iff measurable_inv.aemeasurable measurableSet_floorGroup).2
      (hF.complexData.ae_floorMeasure_mem.mono fun _ ↦ inv_mem)
  refine hm.insert (by simp [floorOf_besselFrame]) hq ?_ (ae_smul_measure h_mem _)
  simp (disch := fun_prop) only [Measure.map_smul, h_law]
  exact leFibreMeasure_frameVector l

/-- An element `g` of the Heisenberg group `floorUnipotent a` of floor `a` fixes `e_a` and the basis
vectors of lower floors: in these columns `k` it agrees with the identity matrix. -/
lemma apply_of_mem_floorUnipotent {a : Fin 𝔰.ϱ} {g : 𝔰.G₁} (hg : g ∈ floorUnipotent a)
    (i k : 𝔰.BesselIndex) (hk : floorOf k < a ∨ k = .inl a) :
    g.val.val i k = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) i k := by
  obtain ⟨h_floor, h_unip⟩ : g ∈ floorGroup a ∧ g ∈ unipotentBelow (a + 1) := hg
  obtain hk | rfl := hk
  · exact mem_floorGroup.1 h_floor i k hk
  by_cases hi : floorOf i < a
  · exact apply_eq_one_apply_of_mem_floorGroup h_floor i _ (.inl ⟨hi, hi.trans a.is_lt⟩)
  · -- `g` is unitriangular for `BesselIndex.level`, and `i` has level at least that of `e_a`.
    have h_level : BesselIndex.level (.inl a : 𝔰.BesselIndex) = a := rfl
    have h_le : BesselIndex.level (.inl a : 𝔰.BesselIndex) ≤ BesselIndex.level i := by
      grind [floorOf_level_cases i]
    have h_mem : g ∈ partialUnitriangularGroup (a + 1) :=
      unipotentBelow_le_partialUnitriangularGroup h_unip
    exact mem_partialUnitriangularGroup.1 h_mem i _ h_le (by simp [h_level])

/-- Assume the numerical hypotheses `hF` on the ranks and the box radius, and let `l ≤ ϱ`. For the
place datum `complexData` at `ℂ`, the measure `partialGroupMeasure 0 l` is the product
`(η_(l-1) ∗ θ_(l-1)) ∗ ⋯ ∗ (η_0 ∗ θ_0)`, where `η_a` is the measure of the Heisenberg group of floor
`a` and `θ_a` the measure of floor `a`. Its image under `g ↦ g⁻¹ (e_0, e*_0, …, e_(l-1), e*_(l-1))`,
divided by `2 ^ (2 l)`, is at most the fibre measure of the Gram map on the tuples with the Gram
matrix of the first `l` hyperbolic pairs. -/
lemma RealPlaceSizes.leGramFibre_partialGroupMeasure (hF : RealPlaceSizes 𝔰 ρ s b) {l : ℕ}
    (hl : l ≤ 𝔰.ϱ) :
    LeGramFibre 𝔰.J₁
      (inclMatrix ℂ (Subtype.val : {i : 𝔰.BesselIndex // floorOf i < l} → 𝔰.BesselIndex))
      ((2⁻¹ : ℝ≥0∞) ^ (2 * l) • (hF.complexData.partialGroupMeasure 0 l).inv) := by
  -- Choose the vectors of the tuple in turn.
  induction l with
  | zero =>
    have : IsEmpty {i : 𝔰.BesselIndex // floorOf i < 0} := ⟨fun i ↦ Nat.not_lt_zero _ i.2⟩
    simpa [descConv, Measure.inv] using leGramFibre_dirac _
  | succ a ih =>
    lift a to Fin 𝔰.ϱ using hl
    have h_split : (2⁻¹ : ℝ≥0∞) ^ (2 * (a.val + 1)) •
      (hF.complexData.partialGroupMeasure 0 (a + 1)).inv =
        (((2⁻¹ : ℝ≥0∞) ^ (2 * a.val) • (hF.complexData.partialGroupMeasure 0 a).inv) ∗ₘ
          ((2⁻¹ : ℝ≥0∞) • (hF.complexData.floorMeasure a).inv)) ∗ₘ
            ((2⁻¹ : ℝ≥0∞) • complexPlace.heisenbergMeasure a) := by
      simp only [descConv_succ, inv_mconv, Measure.inv_eq_self, mconv_smul_left, mconv_smul_right,
        smul_smul, mconv_assoc]
      ring_nf
    have h_index (i : 𝔰.BesselIndex) :
        floorOf i < a + 1 ↔ (floorOf i < a ∨ i = .inl a) ∨ i = eStar a := by
      obtain i | (i | i) | i := i <;> simp <;> lia
    -- Add the frame vector `e_a`, then the dual vector `e*_a`.
    have h_frame : LeGramFibre 𝔰.J₁
        (inclMatrix ℂ
          (Subtype.val : {i : 𝔰.BesselIndex // floorOf i < a ∨ i = .inl a} → 𝔰.BesselIndex))
        (((2⁻¹ : ℝ≥0∞) ^ (2 * a.val) • (hF.complexData.partialGroupMeasure 0 a).inv) ∗ₘ
          ((2⁻¹ : ℝ≥0∞) • (hF.complexData.floorMeasure a).inv)) :=
      hF.leGramFibre_mconv_floorMeasure a.castSucc (by simp) (ih a.2.le)
    rw [h_split]
    refine h_frame.insert (j := eStar a) (by simp) h_index ?_ ?_
    · have h_zero : (𝔰.J₁ (eStar a) (eStar a)).re = 0 := by simp
      simp (disch := fun_prop) only [Measure.map_smul, h_zero]
      exact leFibreMeasure_dualVector a
    · exact ae_smul_measure (ae_mem_floorUnipotent.mono fun _ ↦ apply_of_mem_floorUnipotent) _

/-- Assume the numerical hypotheses `hF` on the ranks and the box radius. Let `groupMeasure` be the
product of the Heisenberg and floor measures of all floors of the place datum `complexData` at `ℂ`.
Its image under inversion is at most `volU r / volU k` times the Haar measure `volume` of `G₁`. -/
lemma RealPlaceSizes.inv_groupMeasure_le (hF : RealPlaceSizes 𝔰 ρ s b) :
    hF.complexData.groupMeasure.inv ≤ ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k) • volume := by
  -- Add `z` to the hyperbolic pairs. The complement `X₀` of this tuple is definite, and the
  -- measure of floor `ϱ + 1` is the Haar measure of `U(X₀)`.
  have h_disjoint (i : {i : 𝔰.BesselIndex // floorOf i < 𝔰.n}) (j : 𝔰.κ) :
      i.val ≠ 𝔰.indexX₀ j := fun h ↦ by simpa [h] using i.2
  have h_bij : Function.Bijective (Sum.elim Subtype.val 𝔰.indexX₀ :
      {i : 𝔰.BesselIndex // floorOf i < 𝔰.n} ⊕ 𝔰.κ → 𝔰.BesselIndex) :=
    ⟨Subtype.val_injective.sumElim (fun _ _ h ↦ by simpa using h) h_disjoint,
      by rintro (i | (i | i) | i) <;> simp⟩
  let e : {i : 𝔰.BesselIndex // floorOf i < 𝔰.n} ⊕ 𝔰.κ ≃ 𝔰.BesselIndex := .ofBijective _ h_bij
  have h_index (i : 𝔰.BesselIndex) :
      floorOf i < 𝔰.n ↔ floorOf i < 𝔰.top ∨ i = 𝔰.besselFrame 𝔰.top := by
    obtain i | (i | i) | i := i <;> simp
  let m : Measure 𝔰.G₁ := ((2⁻¹ : ℝ≥0∞) ^ (2 * 𝔰.ϱ) •
    (hF.complexData.partialGroupMeasure 0 𝔰.ϱ).inv) ∗ₘ
    ((2⁻¹ : ℝ≥0∞) • (hF.complexData.floorMeasure 𝔰.ϱ).inv)
  have h_tuple : LeGramFibre 𝔰.J₁ (inclMatrix ℂ (e ∘ inl)) m :=
    hF.leGramFibre_mconv_floorMeasure 𝔰.top h_index (hF.leGramFibre_partialGroupMeasure le_rfl)
  calc hF.complexData.groupMeasure.inv
      = (hF.complexData.partialGroupMeasure 0 𝔰.ϱ).inv ∗ₘ (hF.complexData.floorMeasure 𝔰.ϱ).inv ∗ₘ
          volume.map embedH := by simp [descConv_succ, inv_mconv, mconv_assoc]
    _ = (2 : ℝ≥0∞) ^ (2 * 𝔰.ϱ + 1) • (m ∗ₘ volume.map embedH) := by
        simp only [m, mconv_smul_left, mconv_smul_right, smul_smul, mconv_assoc, ← pow_succ',
          ← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top, one_pow, one_smul]
    _ ≤ (2 : ℝ≥0∞) ^ (2 * 𝔰.ϱ + 1) •
          ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k / 2 ^ (2 * 𝔰.ϱ + 1)) • volume := by
        gcongr
        exact h_tuple.mconv_embedH_le e fun _ ↦ rfl
    _ = ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k) • volume := by
        rw [smul_smul, ← ofReal_ofNat, ← ofReal_pow zero_le_two, ← ofReal_mul (by positivity),
          mul_div_cancel₀ _ (by positivity)]

/-- The convolution `groupMeasure` of the Heisenberg and floor measures of all floors of the place
datum at `ℂ` is `haarRatio` times the Haar measure of `G₁`. -/
lemma RealPlaceSizes.groupMeasure_eq_haarRatio_smul (hF : RealPlaceSizes 𝔰 ρ s b) :
    hF.complexData.groupMeasure = hF.haarRatio • volume :=
  (exists_eq_smul_haar volume hF.complexData.isMulRightInvariant_groupMeasure).choose_spec

/-- Assume the numerical hypotheses `hF`. The constant `haarRatio`, the ratio of the measure
`groupMeasure` of the place datum at ℂ to the Haar measure of `G₁`, is at most `volU r / volU k`, a
ratio of volumes of unitary groups. -/
lemma RealPlaceSizes.haarRatio_le (hF : RealPlaceSizes 𝔰 ρ s b) :
    hF.haarRatio ≤ ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k) := by
  -- Haar measure is invariant under inversion. Compare the measures of a ball.
  have h_inv : hF.complexData.groupMeasure.inv = hF.haarRatio • volume := by
    simp [hF.groupMeasure_eq_haarRatio_smul, Measure.inv, Measure.map_smul,
      measurable_inv.aemeasurable]
  have h_smul_le : hF.haarRatio • (volume : Measure 𝔰.G₁) ≤
      ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k) • volume :=
    h_inv.symm.trans_le hF.inv_groupMeasure_le
  let B : Set 𝔰.G₁ := {g | ‖(g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ 2}
  have hB_ne_zero : volume B ≠ 0 := measure_sublevel_ne_zero volume
  have hB_ne_top : volume B ≠ ∞ := (isCompact_U_norm_le (J := 𝔰.J₁) 2).measure_ne_top
  have h_le : hF.haarRatio * volume B ≤ ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k) * volume B :=
    h_smul_le B
  exact (ENNReal.mul_le_mul_iff_left hB_ne_zero hB_ne_top).1 h_le

open PlaceData Shape in
/-- Assume the numerical hypotheses `hF`. Let `f` be a measurable function on `G₁` that is invariant
on the left under the unipotent group 𝖴 = `besselU`. Its integral against the convolution
`quotientMeasureFrom 0` of the floor measures of the place datum `complexData` at `ℂ` is `haarRatio`
times its integral against `besselQuotMeasure`, which integrates over `𝖴 \ G₁`. -/
lemma RealPlaceSizes.lintegral_quotientMeasureFrom_eq_haarRatio_mul (hF : RealPlaceSizes 𝔰 ρ s b)
    {f : 𝔰.G₁ → ℝ≥0∞} (hf : Measurable f) (h_inv : besselU.FixesLeft f) :
    ∫⁻ g : 𝔰.G₁, f g ∂hF.complexData.quotientMeasureFrom 0 =
      hF.haarRatio * ∫⁻ g : 𝔰.G₁, f g ∂besselQuotMeasure := by
  -- `groupMeasure` is `du ∗ θ`, with `θ` the convolution of the measures of the floors. So
  -- `(g, u) ↦ u g` carries `θ × du` to `haarRatio` times Haar measure, and `θ` represents the
  -- quotient of that measure by 𝖴.
  set θ : Measure 𝔰.G₁ := hF.complexData.quotientMeasureFrom 0 with hθ
  have h_conv : 𝔰.besselHaar.map .val ∗ₘ θ = hF.haarRatio • volume := by
    simpa [hθ, partialGroupMeasure_zero_eq, ascConv, ascConv_heisenbergMeasure_eq_besselHaar] using
      hF.groupMeasure_eq_haarRatio_smul
  have h_incl : MeasurePreserving (fun p : 𝔰.G₁ × besselU ↦ ((p.2 : 𝔰.G₁), p.1))
      (θ.prod 𝔰.besselHaar) ((𝔰.besselHaar.map .val).prod θ) := by
    have h_val : MeasurePreserving Subtype.val 𝔰.besselHaar (𝔰.besselHaar.map .val) :=
      measurable_subtype_coe.measurePreserving _
    exact (h_val.prod (.id θ)).comp measurePreserving_swap
  have h_mul : MeasurePreserving (fun p : 𝔰.G₁ × 𝔰.G₁ ↦ p.1 * p.2)
      ((𝔰.besselHaar.map .val).prod θ) (hF.haarRatio • volume) := ⟨measurable_mul, h_conv⟩
  have h_unfold : MeasurePreserving (fun p : 𝔰.G₁ × besselU ↦ p.2 • p.1) (θ.prod 𝔰.besselHaar)
      (hF.haarRatio • volume) := h_mul.comp h_incl
  have h_law : ProbabilityTheory.IdentDistrib f f
      (orbitMeasure 𝔰.besselHaar (hF.haarRatio • volume)) θ :=
    identDistrib_orbitMeasure_of_unfold (.id _) h_unfold hf measurable_id fun u ↦ h_inv u u.2
  calc ∫⁻ g : 𝔰.G₁, f g ∂θ
      = ∫⁻ g : 𝔰.G₁, f g ∂orbitMeasure 𝔰.besselHaar (hF.haarRatio • volume) :=
        h_law.lintegral_eq.symm
    _ = hF.haarRatio * ∫⁻ g : 𝔰.G₁, f g ∂besselQuotMeasure := by
        simp [withDensity_smul_measure]

open PlaceData Shape in
/-- Assume the numerical hypotheses `hF` on the ranks and the box radius. The measure `groupMeasure`
of the place datum `complexData` at `ℂ` is a number `haarRatio`, neither `0` nor `∞`, times the Haar
measure `volume` of `G₁`. For measurable `f` invariant on the left under 𝖴, the integral of `f`
against `quotientMeasureFrom 0 = θ_(ϱ+1) ∗ ⋯ ∗ θ_0`, the product of the measures of the floors, is
`haarRatio` times its integral against `besselQuotMeasure`, the Haar measure weighted by a cutoff
for 𝖴. Moreover `haarRatio` is at most `volU r / volU k`, a ratio of volumes of unitary groups. -/
lemma RealPlaceSizes.haarRatio_ne_zero_and_groupMeasure_eq_smul (hF : RealPlaceSizes 𝔰 ρ s b) :
    (hF.haarRatio ≠ 0 ∧ hF.haarRatio ≠ ∞) ∧
    hF.complexData.groupMeasure = hF.haarRatio • volume ∧
    (∀ f : 𝔰.G₁ → ℝ≥0∞, Measurable f → besselU.FixesLeft f →
      ∫⁻ g : (𝔰.middleGram (1 : ℂ)).G, f g ∂hF.complexData.quotientMeasureFrom 0 =
        hF.haarRatio * ∫⁻ g : 𝔰.G₁, f g ∂besselQuotMeasure) ∧
    ENNReal.ofReal (volU 𝔰.k / volU 𝔰.r) * hF.haarRatio ≤ 1 := by
  have h_smul : hF.complexData.groupMeasure = hF.haarRatio • volume :=
    hF.groupMeasure_eq_haarRatio_smul
  have h_ne_zero : hF.haarRatio ≠ 0 := fun h_zero ↦ by
    simp [h_zero, partialGroupMeasure_ne_zero] at h_smul
  refine ⟨⟨h_ne_zero, (hF.haarRatio_le.trans_lt ofReal_lt_top).ne⟩, h_smul,
    fun f ↦ hF.lintegral_quotientMeasureFrom_eq_haarRatio_mul, ?_⟩
  have hk : 0 < volU 𝔰.k := volU_pos 𝔰.k
  have hr : 0 < volU 𝔰.r := volU_pos 𝔰.r
  calc ENNReal.ofReal (volU 𝔰.k / volU 𝔰.r) * hF.haarRatio
      ≤ ENNReal.ofReal (volU 𝔰.k / volU 𝔰.r) * ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k) := by
        grw [hF.haarRatio_le]
    _ = 1 := by
        rw [← ofReal_mul (div_pos hk hr).le, div_mul_div_cancel₀ hr.ne', div_self hk.ne',
          ofReal_one]

/-- The measure `groupMeasure` of the place datum at `ℂ` is a Haar measure on `G₁`. -/
instance : hF.complexData.groupMeasure.IsHaarMeasure := by
  simp [hF.haarRatio_ne_zero_and_groupMeasure_eq_smul, IsHaarMeasure.smul]

attribute [local simp ←] ofReal_pow ofReal_mul ofReal_coe_nnreal dotProduct_mulVec
attribute [local simp] inclMatrix star_mulVec Size.vecsOfSize MeasureTheory.volume_pi_closedBall
  pi_norm_le_iff_of_nonneg

open Fock Set ComplexOrder ProbabilityTheory Complex EuclideanSpace Size

/-- The polydisc of radius `r` in `ι → ℂ` has volume `(π r²) ^ card ι`. -/
lemma volume_closedBall_pi_complex {ι : Type} [Fintype ι] {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall (0 : ι → ℂ) r) = ENNReal.ofReal ((π * r ^ 2) ^ card ι) := by
  rw [MeasureTheory.volume_pi_closedBall _ hr, ofReal_pow (by positivity), ofReal_mul pi_pos.le,
    ofReal_pow hr, ← NNReal.coe_real_pi, ofReal_coe_nnreal, mul_comm]
  simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ]

/-- If the rank of `C` plus `d` is at most the number of columns of `C`, then some `d` columns of a
unitary matrix `Q` lie in the kernel of `C`. -/
lemma exists_unitary_mul_submatrix_eq_zero {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq ι]
    (C : Matrix m ι ℂ) {d : ℕ} (hd : C.rank + d ≤ card ι) :
    ∃ (Q : unitaryGroup ι ℂ) (D : Finset ι),
      D.card = d ∧ C * Q.val.submatrix id ((↑) : D → ι) = 0 := by
  -- Take eigenvectors of `Cᴴ * C` with eigenvalue `0`.
  have H : (Cᴴ * C).IsHermitian := C.isHermitian_conjTranspose_mul_self
  have h_rank : C.rank = card {i : ι // H.eigenvalues i ≠ 0} := by
    rw [← H.rank_eq_card_non_zero_eigs, rank_conjTranspose_mul_self]
  obtain ⟨D, hD, D_card⟩ : ∃ D ⊆ ({i | H.eigenvalues i = 0} : Finset ι), D.card = d :=
    Finset.exists_subset_card_eq (by grind [card_subtype_compl, card_subtype])
  refine ⟨H.eigenvectorUnitary, D, D_card, ?_⟩
  rw [← conjTranspose_mul_self_mul_eq_zero]
  ext a i
  have h_eig : H.eigenvalues i = 0 := by simpa using hD i.2
  have h_ker : (Cᴴ * C) *ᵥ ⇑(H.eigenvectorBasis i) = 0 := by
    rw [H.mulVec_eigenvectorBasis, h_eig, zero_smul]
  exact congrFun h_ker a

/-- Let `Q` be a unitary matrix and `D` a nonempty set of indices. Send `u` to the squared length of
the coordinates in `D` of `Qᴴ u` and to the other coordinates. This carries Lebesgue measure to the
product of Lebesgue measure and the measure on `r > 0` with density
`sphereDensity #D r / 2 = π ^ #D r ^ (#D - 1) / (#D - 1)!`. -/
lemma measurePreserving_normSq_prod_compl {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : unitaryGroup ι ℂ) (D : Finset ι) [Nonempty D] :
    MeasurePreserving
      (fun u : ι → ℂ ↦ (‖star (fun i : D ↦ (Q.valᴴ *ᵥ u) i) ⬝ᵥ fun i : D ↦ (Q.valᴴ *ᵥ u) i‖,
        fun i : {i : ι // i ∉ D} ↦ (Q.valᴴ *ᵥ u) i))
      volume
      (((volume.restrict (Ioi 0)).withDensity fun r : ℝ ↦
        ENNReal.ofReal (sphereDensity (card D) r / 2)).prod volume) := by
  have h_unitary : MeasurePreserving (fun u : ι → ℂ ↦ Q.valᴴ *ᵥ u) volume volume :=
    complexPlace.measurePreserving_mulVec Q.valᴴ (Unitary.star_mul_self_of_mem
      (det_of_mem_unitary (star Q).2))
  have h_split : MeasurePreserving
      (fun w : ι → ℂ ↦ (fun i : D ↦ w i, fun i : {i : ι // i ∉ D} ↦ w i)) volume volume := by
    have h_pi := volume_preserving_piEquivPiSubtypeProd (fun _ : ι ↦ ℂ) (· ∈ D)
    rwa [Subsingleton.elim (Subtype.fintype (· ∈ D)) inferInstance] at h_pi
  exact ((measurePreserving_normSq_sphereDensity.prod (.id _)).comp h_split).comp h_unitary

/-- If the entries of `u` have modulus at most `R` and `Q` is unitary, then the entries of `Qᴴ u`
have modulus at most `card ι * R`. -/
lemma norm_unitary_conjTranspose_mulVec_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : unitaryGroup ι ℂ) {R : ℝ} {u : ι → ℂ} (hu : ∀ i : ι, ‖u i‖ ≤ R) (i : ι) :
    ‖(Q.valᴴ *ᵥ u) i‖ ≤ card ι * R := by
  calc ‖(Q.valᴴ *ᵥ u) i‖ ≤ ∑ k : ι, ‖star (Q.val k i) * u k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : ι, 1 * R := by
        gcongr with k
        grw [norm_mul, norm_star, entry_norm_bound_of_unitary Q.2, hu k]
    _ = card ι * R := by simp

/-- The integral of `(36 / r) ^ s` over `0 < r ≤ R` against the density
`sphereDensity (s + 1) r / 2 = π ^ (s + 1) r ^ s / s!` is at most `4 * 3 ^ 144 * R`. -/
lemma setLIntegral_inv_pow_sphereDensity_le (s : ℕ) (R : ℝ) :
    ∫⁻ r : ℝ in Iic R, (ENNReal.ofReal (r / 36))⁻¹ ^ s
        ∂(volume.restrict (Ioi 0)).withDensity
          (fun r : ℝ ↦ ENNReal.ofReal (sphereDensity (s + 1) r / 2)) ≤
      ENNReal.ofReal (4 * 3 ^ 144) * ENNReal.ofReal R := by
  have integrand_le (r : ℝ) (hr : 0 < r) : ENNReal.ofReal (sphereDensity (s + 1) r / 2) *
      (ENNReal.ofReal (r / 36))⁻¹ ^ s ≤ ENNReal.ofReal (4 * 3 ^ 144) := by
    rw [← ofReal_inv_of_pos (by positivity), ← ofReal_pow (by positivity),
      ← ofReal_mul (by positivity)]
    apply ofReal_le_ofReal
    calc sphereDensity (s + 1) r / 2 * (r / 36)⁻¹ ^ s = π * ((π * 36) ^ s / s.factorial) := by
          simp only [sphereDensity, Nat.add_sub_cancel, inv_div, div_pow, mul_pow, pow_succ]
          field
      _ ≤ 4 * ((4 * 36) ^ s / s.factorial) := by gcongr <;> exact pi_le_four
      _ ≤ 4 * rexp (4 * 36) := by grw [pow_div_factorial_le_exp _ (by norm_num) s]
      _ = 4 * rexp 1 ^ 144 := by norm_num [exp_one_pow]
      _ ≤ 4 * 3 ^ 144 := by grw [exp_one_lt_three]
  rw [restrict_withDensity measurableSet_Iic, restrict_restrict measurableSet_Iic, Iic_inter_Ioi]
  calc _ ≤ ∫⁻ r : ℝ in Ioc 0 R, ENNReal.ofReal (sphereDensity (s + 1) r / 2) *
          (ENNReal.ofReal (r / 36))⁻¹ ^ s :=
        lintegral_withDensity_le_lintegral_mul _ (by fun_prop) _
    _ ≤ ∫⁻ _r : ℝ in Ioc 0 R, ENNReal.ofReal (4 * 3 ^ 144) :=
        setLIntegral_mono' measurableSet_Ioc fun r hr ↦ integrand_le r hr.1
    _ = ENNReal.ofReal (4 * 3 ^ 144) * ENNReal.ofReal R := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero]

/-- Let n = `𝔰.n` = ϱ + 1; the shape 𝔰 enters only through this number. Let C be a matrix with
s + 1 + 3 n ≤ L columns and rank at most 3 n, and let L ≥ 4. The kernel of C contains orthonormal
vectors, the columns of a matrix O, such that for every j the integral of (36 / |Oᴴ u|²)^s over the
u with entries of modulus at most L^j is at most (L²)^(99 n (j+1)). -/
lemma exists_orthonormal_ker_lintegral_le {𝔰 : Shape} {s : ℕ} {L : ℝ} {m ι : Type}
    [Fintype m] [Fintype ι] [DecidableEq ι] (C : Matrix m ι ℂ)
    (hcard : card ι = s + 1 + 3 * 𝔰.n) (h4 : 4 ≤ L) (hrank : C.rank ≤ 3 * 𝔰.n) (hL : card ι ≤ L) :
    ∃ (D : Finset ι) (O : Matrix ι D ℂ),
      C * O = 0 ∧ Oᴴ * O = 1 ∧
      ∀ j : ℕ,
        ∫⁻ u : ι → ℂ in {u : ι → ℂ | ∀ i : ι, ‖u i‖ ≤ L ^ j},
            (ENNReal.ofReal (‖star (Oᴴ *ᵥ u) ⬝ᵥ Oᴴ *ᵥ u‖ / 36))⁻¹ ^ s ≤
          (ENNReal.ofReal L ^ 2) ^ (99 * 𝔰.n * (j + 1)) := by
  -- The columns of `O` are `s + 1` columns of a unitary matrix `Q`. Pass to the basis `Q`; of the
  -- coordinates in `D` keep only `|Oᴴ u|²`, of law `μ`. The integral splits as a product.
  obtain ⟨Q, D, D_card, hCO⟩ : ∃ (Q : unitaryGroup ι ℂ) (D : Finset ι),
      D.card = s + 1 ∧ C * Q.val.submatrix id ((↑) : D → ι) = 0 :=
    exists_unitary_mul_submatrix_eq_zero C (by lia)
  set O : Matrix ι D ℂ := Q.val.submatrix id (↑)
  have hO : Oᴴ * O = 1 := by
    have hQ : Q.valᴴ * Q.val = 1 := Unitary.star_mul_self_of_mem Q.2
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id, hQ]
    exact submatrix_one _ Subtype.val_injective
  refine ⟨D, O, hCO, hO, fun j ↦ ?_⟩
  have : Nonempty D := (D.card_pos.1 (by lia)).coe_sort
  have hL_pos : 0 < L := by linarith
  let μ : Measure ℝ :=
    (volume.restrict (Ioi 0)).withDensity fun r ↦ ENNReal.ofReal (sphereDensity (s + 1) r / 2)
  let Φ (u : ι → ℂ) : ℝ × ({i : ι // i ∉ D} → ℂ) :=
    (‖star (Oᴴ *ᵥ u) ⬝ᵥ Oᴴ *ᵥ u‖, fun i ↦ (Q.valᴴ *ᵥ u) i)
  have h_coord (u : ι → ℂ) : Oᴴ *ᵥ u = fun i : D ↦ (Q.valᴴ *ᵥ u) i := rfl
  have hΦ : MeasurePreserving Φ volume (μ.prod volume) := by
    simpa only [Φ, μ, h_coord, card_coe, D_card] using measurePreserving_normSq_prod_compl Q D
  let R : ℝ := L * (L * L ^ j) ^ 2
  let B : Set ({i : ι // i ∉ D} → ℂ) := closedBall 0 (L * L ^ j)
  have box_subset : {u : ι → ℂ | ∀ i : ι, ‖u i‖ ≤ L ^ j} ⊆ Φ ⁻¹' Iic R ×ˢ B := by
    intro u hu
    have coord_le (i : ι) : ‖(Q.valᴴ *ᵥ u) i‖ ≤ L * L ^ j := by
      grw [norm_unitary_conjTranspose_mulVec_le Q hu i, hL]
    refine ⟨?_, mem_closedBall_zero_iff.2
      ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ coord_le i)⟩
    calc ‖star (Oᴴ *ᵥ u) ⬝ᵥ Oᴴ *ᵥ u‖ = ∑ i : D, ‖(Q.valᴴ *ᵥ u) i‖ ^ 2 := by
          rw [star_dotProduct_self_eq_norm_sq, norm_pow, norm_real, norm_norm, norm_sq_eq, h_coord]
      _ ≤ ∑ _i : D, (L * L ^ j) ^ 2 := by
          gcongr with i
          exact coord_le i
      _ = D.card * (L * L ^ j) ^ 2 := by simp
      _ ≤ L * (L * L ^ j) ^ 2 := by grw [D.card_le_univ, hL]
  have hB : volume B = ENNReal.ofReal ((π * (L * L ^ j) ^ 2) ^ (3 * 𝔰.n)) := by
    have h_compl : card {i : ι // i ∉ D} = 3 * 𝔰.n := by simp [hcard, D_card]
    rw [volume_closedBall_pi_complex (by positivity), h_compl]
  have const_le : 4 * 3 ^ 144 * R * (π * (L * L ^ j) ^ 2) ^ (3 * 𝔰.n) ≤
      (L ^ 2) ^ (99 * 𝔰.n * (j + 1)) := by
    have h3 : 3 ≤ L := by linarith
    have h_exp : 145 + (2 * j + 3) * (3 * 𝔰.n + 1) ≤ 2 * (99 * 𝔰.n * (j + 1)) := by
      nlinarith only [Nat.succ_pos 𝔰.ϱ, show 𝔰.n = 𝔰.ϱ + 1 from rfl]
    calc 4 * 3 ^ 144 * R * (π * (L * L ^ j) ^ 2) ^ (3 * 𝔰.n)
        ≤ L * L ^ 144 * R * (L * (L * L ^ j) ^ 2) ^ (3 * 𝔰.n) := by
          gcongr
          exact pi_le_four.trans h4
      _ = L ^ (145 + (2 * j + 3) * (3 * 𝔰.n + 1)) := by
          simp only [R]
          ring
      _ ≤ L ^ (2 * (99 * 𝔰.n * (j + 1))) := pow_le_pow_right₀ (by linarith) h_exp
      _ = (L ^ 2) ^ (99 * 𝔰.n * (j + 1)) := pow_mul ..
  calc
    _ ≤ ∫⁻ u in Φ ⁻¹' Iic R ×ˢ B, (ENNReal.ofReal ((Φ u).1 / 36))⁻¹ ^ s :=
      lintegral_mono_set box_subset
    _ = ∫⁻ p in Iic R ×ˢ B, (ENNReal.ofReal (p.1 / 36))⁻¹ ^ s ∂μ.prod volume :=
      hΦ.setLIntegral_comp_preimage (f := fun p ↦ (ENNReal.ofReal (p.1 / 36))⁻¹ ^ s)
        (measurableSet_Iic.prod measurableSet_closedBall) (by fun_prop)
    _ = (∫⁻ r in Iic R, (ENNReal.ofReal (r / 36))⁻¹ ^ s ∂μ) * volume B := by
      rw [← prod_restrict, lintegral_prod_symm _ (by fun_prop)]
      simp
    _ ≤ ENNReal.ofReal (4 * 3 ^ 144) * ENNReal.ofReal R * volume B := by
      grw [setLIntegral_inv_pow_sphereDensity_le]
    _ ≤ (ENNReal.ofReal L ^ 2) ^ (99 * 𝔰.n * (j + 1)) := by
      rw [hB, ← ofReal_mul (by positivity), ← ofReal_mul (by positivity), ← ofReal_pow hL_pos.le,
        ← ofReal_pow (by positivity)]
      exact ofReal_le_ofReal const_le

/-- The box size `ρ` is at least 4, being at least 8 times the rank. -/
lemma RealPlaceSizes.four_le (hF : RealPlaceSizes 𝔰 ρ s b) : 4 ≤ ρ := by
  have hr : (1 : ℝ) ≤ 𝔰.r := by exact_mod_cast card_pos_iff.2 ⟨𝔰.besselFrame 𝔰.top⟩
  linarith [hF.eight_mul_r_le_rho]

/-- Let `e = orthonormalPart` be the matrix whose columns are the free orthonormal basis vectors of
the place datum at `ℂ`, and let `g` be in the unitary group `G₁` of the form of matrix `J₁`. If `J₁`
fixes `g e w`, then `g e w` and `w` have the same Euclidean length. -/
lemma RealPlaceSizes.norm_sq_mulVec_of_fixed (hF : RealPlaceSizes 𝔰 ρ s b) (g : 𝔰.G₁)
    (w : hF.complexData.FreeIndex → ℂ)
    (h_fix :
      𝔰.J₁ *ᵥ g.val.val *ᵥ hF.complexData.orthonormalPart *ᵥ w =
        g.val.val *ᵥ hF.complexData.orthonormalPart *ᵥ w) :
    ‖toLp 2 (g.val.val *ᵥ hF.complexData.orthonormalPart *ᵥ w)‖ ^ 2 = ‖star w ⬝ᵥ w‖ := by
  set e : Matrix 𝔰.BesselIndex hF.complexData.FreeIndex ℂ := hF.complexData.orthonormalPart
  have he : eᴴ * (𝔰.J₁ * e) = 1 := by
    ext
    simp [e, complexBasis, mul_apply, splitGram, middleGram, Matrix.one_apply, PlaceData.freeIndex,
      Subtype.val_inj]
  calc ‖toLp 2 (g.val.val *ᵥ e *ᵥ w)‖ ^ 2
      = ‖star (g.val.val *ᵥ e *ᵥ w) ⬝ᵥ g.val.val *ᵥ e *ᵥ w‖ := by
        rw [star_dotProduct_self_eq_norm_sq, norm_pow, norm_real, norm_norm]
    _ = ‖star (g.val.val *ᵥ e *ᵥ w) ⬝ᵥ 𝔰.J₁ *ᵥ g.val.val *ᵥ e *ᵥ w‖ := by rw [h_fix]
    _ = ‖star (e *ᵥ w) ⬝ᵥ 𝔰.J₁ *ᵥ e *ᵥ w‖ := by rw [U.form_mulVec_mulVec]
    _ = ‖star w ⬝ᵥ w‖ := by simp [he]

/-- At a real place, with `⟨u, v⟩ = star u ⬝ᵥ J₁ v`, the numbers `⟨ω₁, ω'₁⟩ - ⟨ω₂, ω'₂⟩` for two
close pairs `(ω₁, ω₂)` and `(ω'₁, ω'₂)`, which form the set `productDifferences`, have modulus at
most `1`. -/
lemma RealPlaceSizes.norm_le_of_mem_productDifferences (hF : RealPlaceSizes 𝔰 ρ s b) {c : ℂ}
    (hc : c ∈ hF.complexData.productDifferences) : ‖c‖ ≤ 1 := by
  obtain ⟨⟨ω₁, ω₂⟩, h_close, ⟨ω₁', ω₂'⟩, h_close', rfl⟩ := hc
  have form_le (u v : 𝔰.BesselIndex → ℂ) :
      ‖star u ⬝ᵥ 𝔰.J₁ *ᵥ v‖ ≤ (‖toLp 2 u‖ ^ 2 + ‖toLp 2 v‖ ^ 2) / 2 := by
    rw [dotProduct_comm]
    refine (norm_inner_J₁_le (v := toLp 2 u) (w := toLp 2 v)).trans ?_
    linarith [two_mul_le_add_sq ‖toLp 2 u‖ ‖toLp 2 v‖]
  change ‖toLp 2 ω₁‖ ^ 2 + ‖toLp 2 ω₂‖ ^ 2 < 1 at h_close
  change ‖toLp 2 ω₁'‖ ^ 2 + ‖toLp 2 ω₂'‖ ^ 2 < 1 at h_close'
  simp only [complexData_levelUnit, inv_one, Units.val_one, one_mul]
  grw [norm_sub_le, form_le, form_le]
  linarith

/-- Assume the numerical hypotheses `hF`, and let `e = orthonormalPart` embed the span `X'` of the
free orthonormal basis vectors of the place datum at `ℂ` into the space. The common vectors are the
`w` in `X'` with `v w = 0` and `|x⁻¹ e w|² + |(x y)⁻¹ e w|² < 1`. Let the columns of `O` be
orthonormal, killed by `v`, and carried by `x⁻¹ e` and `(x y)⁻¹ e` into the space on which `J₁` is
the identity. If `r = |Oᴴ u|²` is not `0`, the products `⟨u, w⟩` with the common vectors `w` cover
the closed disc of radius `|Oᴴ u| / 2`. -/
lemma RealPlaceSizes.closedBall_subset_image_commonVectors (hF : RealPlaceSizes 𝔰 ρ s b)
    {D : Type} [Fintype D] [DecidableEq D] {x y : 𝔰.G₁}
    {v : Matrix (Fin 𝔰.ϱ) hF.complexData.FreeIndex ℂ}
    {O : Matrix hF.complexData.FreeIndex D ℂ}
    (hO : Oᴴ * O = 1) (hv : v * O = 0)
    (h_fix : ∀ g ∈ ({x⁻¹, (x * y)⁻¹} : Set 𝔰.G₁), ∀ t : D → ℂ,
      𝔰.J₁ *ᵥ g.val.val *ᵥ hF.complexData.orthonormalPart *ᵥ O *ᵥ t =
        g.val.val *ᵥ hF.complexData.orthonormalPart *ᵥ O *ᵥ t)
    {u : hF.complexData.FreeIndex → ℂ} {r : ℂ} (hr : star (Oᴴ *ᵥ u) ⬝ᵥ Oᴴ *ᵥ u = r)
    (hr_ne : r ≠ 0) :
    closedBall 0 (|√‖r‖| / 2) ⊆ (fun w : hF.complexData.FreeIndex → ℂ ↦ star u ⬝ᵥ w) ''
      hF.complexData.commonVectors x y v := by
  intro t ht
  rw [mem_closedBall_zero_iff] at ht
  set e : Matrix 𝔰.BesselIndex hF.complexData.FreeIndex ℂ := hF.complexData.orthonormalPart
  -- The multiple `w` of `O Oᴴ u` with `⟨u, w⟩ = t` has length at most `1 / 2`.
  let w : hF.complexData.FreeIndex → ℂ := O *ᵥ (t / r) • Oᴴ *ᵥ u
  have h_adj (z : hF.complexData.FreeIndex → ℂ) (z' : D → ℂ) :
      star z ⬝ᵥ O *ᵥ z' = star (Oᴴ *ᵥ z) ⬝ᵥ z' := by
    rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]
  have h_prod : star u ⬝ᵥ w = t := by
    rw [h_adj, dotProduct_smul, hr, smul_eq_mul, div_mul_cancel₀ t hr_ne]
  have h_len : ‖star w ⬝ᵥ w‖ ≤ 4⁻¹ := by
    have h_back : Oᴴ *ᵥ w = (t / r) • Oᴴ *ᵥ u := by rw [mulVec_mulVec, hO, one_mulVec]
    have hr_pos : 0 < ‖r‖ := norm_pos_iff.2 hr_ne
    calc ‖star w ⬝ᵥ w‖ = ‖star (t / r) * (t / r * r)‖ := by
          rw [h_adj, h_back, star_smul, smul_dotProduct, dotProduct_smul, hr, smul_eq_mul,
            smul_eq_mul]
      _ = ‖t‖ ^ 2 / ‖r‖ := by
          rw [div_mul_cancel₀ t hr_ne, norm_mul, norm_star, norm_div]
          ring
      _ ≤ (|√‖r‖| / 2) ^ 2 / ‖r‖ := by gcongr
      _ = 4⁻¹ := by
          rw [div_pow, sq_abs, sq_sqrt hr_pos.le]
          field
  refine ⟨w, ⟨by simp [w, hv], ?_⟩, h_prod⟩
  change ‖toLp 2 (x⁻¹.val.val *ᵥ e *ᵥ w)‖ ^ 2 + ‖toLp 2 ((x * y)⁻¹.val.val *ᵥ e *ᵥ w)‖ ^ 2 < 1
  rw [hF.norm_sq_mulVec_of_fixed _ w (h_fix _ (.inl rfl) _),
    hF.norm_sq_mulVec_of_fixed _ w (h_fix _ (.inr rfl) _)]
  linarith

/-- A closed disc of radius `R ≥ 0` in `ℂ` has area `π R²`. -/
lemma volume_closedBall_eq_ofReal_pi_mul_sq {R : ℝ} (hR : 0 ≤ R) :
    volume (closedBall (0 : ℂ) R) = ENNReal.ofReal (π * R ^ 2) := by
  rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hR, ← ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- For `t > 0`, a set `W ⊆ ℂ` that contains the closed disc of radius `√t / 2` about `0` has
`(volume W)⁻¹` at most `36 / t`. -/
lemma inv_volume_le_of_closedBall_subset {W : Set ℂ} {t : ℝ} (ht : 0 < t)
    (hW : closedBall 0 (√t / 2) ⊆ W) : (volume W)⁻¹ ≤ (ENNReal.ofReal (t / 36))⁻¹ := by
  refine ENNReal.inv_le_inv.2 ?_
  calc ENNReal.ofReal (t / 36) ≤ ENNReal.ofReal (π * (√t / 2) ^ 2) := by
        rw [div_pow, sq_sqrt ht.le]
        exact ofReal_le_ofReal (by nlinarith [pi_gt_three])
    _ = volume (closedBall (0 : ℂ) (√t / 2)) :=
        (volume_closedBall_eq_ofReal_pi_mul_sq (by positivity)).symm
    _ ≤ volume W := measure_mono hW

/-- For `t > 0`, a subset of the disc of radius `2 / √t` in `ℂ` has area at most `36 / t`. -/
lemma volume_le_of_subset_closedBall {W : Set ℂ} {t : ℝ} (ht : 0 < t)
    (hW : W ⊆ closedBall 0 (2 / √t)) : volume W ≤ (ENNReal.ofReal (t / 36))⁻¹ := by
  calc volume W ≤ volume (closedBall (0 : ℂ) (2 / √t)) := measure_mono hW
    _ = ENNReal.ofReal (π * (2 / √t) ^ 2) :=
        volume_closedBall_eq_ofReal_pi_mul_sq (by positivity)
    _ = ENNReal.ofReal (4 * π / t) := by
        rw [div_pow, sq_sqrt ht.le]
        ring_nf
    _ ≤ ENNReal.ofReal (36 / t) := by
        gcongr
        linarith [pi_le_four]
    _ = (ENNReal.ofReal (t / 36))⁻¹ := by
        rw [← ofReal_inv_of_pos (by positivity), inv_div]

/-- The Gram matrix `J₁` swaps `e_a` with `e*_a`, fixes the `x_i` and negates `z`. So it fixes a
vector `w` with equal coordinates at `e_a` and `e*_a` and with coordinate `0` at `z`. -/
lemma J₁_mulVec_eq_self_of_apply_eq {w : 𝔰.BesselIndex → ℂ}
    (h_pair : ∀ a : Fin 𝔰.ϱ, w (inl a) = w (eStar a)) (h_z : w (inr (inl (inr ()))) = 0) :
    𝔰.J₁ *ᵥ w = w := by
  ext k
  obtain a | (i | ⟨⟩) | a := k <;>
    simp [mulVec_eq_sum, splitGram, middleGram, Matrix.one_apply, h_pair, h_z]

/-- At `ℂ` the span `X'` of the free orthonormal basis vectors has rank `s + 1 + 3 n`. -/
lemma RealPlaceSizes.card_freeIndex_complexData (hF : RealPlaceSizes 𝔰 ρ s b) :
    card hF.complexData.FreeIndex = s + 1 + 3 * 𝔰.n := by
  have h_block : hF.complexData.blockRank = 2 := rfl
  have h_index : card {i : 𝔰.κ // i ≠ 𝔰.k₀} = s + 3 * 𝔰.n + 5 := by simp [hF.k_eq]
  rw [card_fin, h_block, h_index]
  lia

/-- For the place datum `hF.complexData` at `ℂ`, the number of indices in `FreeIndex` (the
orthonormal basis vectors left when two blocks are set aside) is at most the box radius `ρ`. -/
lemma RealPlaceSizes.card_freeIndex_complexData_le (hF : RealPlaceSizes 𝔰 ρ s b) :
    card hF.complexData.FreeIndex ≤ ρ := by
  have k_le_r : 𝔰.k ≤ 𝔰.r := by
    simp only [Shape.r, card_sum]
    lia
  have card_le_r : card hF.complexData.FreeIndex ≤ 8 * 𝔰.r := by
    linarith [hF.card_freeIndex_complexData, hF.k_eq]
  exact le_trans (mod_cast card_le_r) hF.eight_mul_r_le_rho

/-- Assume the numerical hypotheses `hF`. Let `e = orthonormalPart` embed the span `X'` of the free
orthonormal basis vectors (`FreeIndex`) of the place datum `complexData` at `ℂ` into the space. Let
`x` and `y` be in `G₁`, and let `v` be a matrix whose number of rows is at most `𝔰.n`. Then there is
a matrix `C` of rank at most `3 * 𝔰.n` such that every `w` in `X'` with `C w = 0` has `v w = 0`.
Such a `w` also has `J₁ g e w = g e w` for `g = x⁻¹` and `g = (x y)⁻¹`. -/
lemma RealPlaceSizes.exists_rank_le_and_fixed_of_mulVec_eq_zero (hF : RealPlaceSizes 𝔰 ρ s b)
    (x y : 𝔰.G₁) {m : Type} [Fintype m] (v : Matrix m hF.complexData.FreeIndex ℂ)
    (hm : card m ≤ 𝔰.n) :
    ∃ C : Matrix (m ⊕ (Fin 𝔰.ϱ ⊕ Unit) ⊕ Fin 𝔰.ϱ ⊕ Unit) hF.complexData.FreeIndex ℂ,
      C.rank ≤ 3 * 𝔰.n ∧
      ∀ w : hF.complexData.FreeIndex → ℂ, C *ᵥ w = 0 →
        v *ᵥ w = 0 ∧
        ∀ g ∈ ({x⁻¹, (x * y)⁻¹} : Set 𝔰.G₁),
          𝔰.J₁ *ᵥ g.val.val *ᵥ hF.complexData.orthonormalPart *ᵥ w =
            g.val.val *ᵥ hF.complexData.orthonormalPart *ᵥ w := by
  -- The `n` rows of `N` cut out the space on which `J₁` is the identity.
  let N : Matrix (Fin 𝔰.ϱ ⊕ Unit) 𝔰.BesselIndex ℂ :=
    (1 - 𝔰.J₁).submatrix (Sum.map id (inl ∘ inr)) id
  let e : Matrix 𝔰.BesselIndex hF.complexData.FreeIndex ℂ := hF.complexData.orthonormalPart
  have hN (u : 𝔰.BesselIndex → ℂ) (hu : N *ᵥ u = 0) : 𝔰.J₁ *ᵥ u = u := by
    refine J₁_mulVec_eq_self_of_apply_eq (fun a ↦ ?_) ?_
    · simpa [N, mulVec_eq_sum, splitGram, Matrix.one_apply, ← sub_eq_add_neg, sub_eq_zero]
        using congrFun hu (inl a)
    · simpa [N, mulVec_eq_sum, splitGram, middleGram, Matrix.one_apply] using congrFun hu (inr ())
  refine ⟨fromRows v (fromRows (N * x⁻¹.val.val * e) (N * (x * y)⁻¹.val.val * e)), ?_,
    fun w hw ↦ ?_⟩
  · grw [rank_le_card_height]
    simp only [card_sum, card_fin, card_unit]
    lia
  · obtain ⟨hv, hx, hxy⟩ : v *ᵥ w = 0 ∧ N *ᵥ x⁻¹.val.val *ᵥ e *ᵥ w = 0 ∧
        N *ᵥ (x * y)⁻¹.val.val *ᵥ e *ᵥ w = 0 := by
      simpa only [fromRows_mulVec, ← mulVec_mulVec, funext_iff, Sum.forall, elim_inl, elim_inr,
        Pi.zero_apply] using hw
    refine ⟨hv, ?_⟩
    rintro g (rfl | rfl)
    exacts [hN _ hx, hN _ hxy]

/-- Let `e = orthonormalPart` embed the span `X'` of the free orthonormal basis vectors of the place
datum at `ℂ` into the space, let `x` and `y` be in `G₁`, and let `v` be a matrix with at most `n`
rows. For every `d` up to the rank of `X'` less `3 n` there are `d` orthonormal vectors of `X'`, the
columns of `O`, that are killed by `v` and carried by `x⁻¹ e` and by `(x y)⁻¹ e` into the space on
which `J₁` is the identity. -/
theorem RealPlaceSizes.exists_orthonormal_mul_eq_zero_and_fixed (hF : RealPlaceSizes 𝔰 ρ s b)
    (x y : 𝔰.G₁) {m : Type} [Fintype m] (v : Matrix m hF.complexData.FreeIndex ℂ)
    (hm : card m ≤ 𝔰.n) {d : ℕ} (hd : d + 3 * 𝔰.n ≤ card hF.complexData.FreeIndex) :
    ∃ O : Matrix hF.complexData.FreeIndex (Fin d) ℂ,
      Oᴴ * O = 1 ∧
      v * O = 0 ∧
      ∀ g ∈ ({x⁻¹, (x * y)⁻¹} : Set 𝔰.G₁),
        𝔰.J₁ * (g.val.val * hF.complexData.orthonormalPart * O) =
          g.val.val * hF.complexData.orthonormalPart * O := by
  -- Take `d` columns of a unitary matrix in the kernel of the matrix `C` of the conditions.
  set e : Matrix 𝔰.BesselIndex hF.complexData.FreeIndex ℂ := hF.complexData.orthonormalPart
  obtain ⟨C, rank_le, hC⟩ :
      ∃ C : Matrix (m ⊕ (Fin 𝔰.ϱ ⊕ Unit) ⊕ Fin 𝔰.ϱ ⊕ Unit) hF.complexData.FreeIndex ℂ,
        C.rank ≤ 3 * 𝔰.n ∧ ∀ w : hF.complexData.FreeIndex → ℂ, C *ᵥ w = 0 →
          v *ᵥ w = 0 ∧ ∀ g ∈ ({x⁻¹, (x * y)⁻¹} : Set 𝔰.G₁),
            𝔰.J₁ *ᵥ g.val.val *ᵥ e *ᵥ w = g.val.val *ᵥ e *ᵥ w :=
    hF.exists_rank_le_and_fixed_of_mulVec_eq_zero x y v hm
  obtain ⟨Q, D, D_card, hCQ⟩ :
      ∃ (Q : unitaryGroup hF.complexData.FreeIndex ℂ) (D : Finset hF.complexData.FreeIndex),
        D.card = d ∧ C * Q.val.submatrix id ((↑) : D → hF.complexData.FreeIndex) = 0 :=
    exists_unitary_mul_submatrix_eq_zero C (by lia)
  let σ : Fin d ≃ D := (D.equivFinOfCardEq D_card).symm
  let O : Matrix hF.complexData.FreeIndex (Fin d) ℂ := Q.val.submatrix id fun j ↦ σ j
  have hCO : C * O = 0 := by
    ext i j
    exact congrFun₂ hCQ i (σ j)
  have h_ker (t : Fin d → ℂ) : C *ᵥ O *ᵥ t = 0 := by rw [mulVec_mulVec, hCO, zero_mulVec]
  refine ⟨O, ?_, ?_, fun g hg ↦ ?_⟩
  · have hQ : Q.valᴴ * Q.val = 1 := Unitary.star_mul_self_of_mem Q.2
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id, hQ]
    exact submatrix_one _ (Subtype.val_injective.comp σ.injective)
  · refine Matrix.ext_iff_mulVec.2 fun t ↦ ?_
    rw [← mulVec_mulVec, (hC _ (h_ker t)).1, zero_mulVec]
  · refine Matrix.ext_iff_mulVec.2 fun t ↦ ?_
    simpa only [← mulVec_mulVec] using (hC _ (h_ker t)).2 g hg

/-- Let `L ≥ ρ`, and let `S` be the size in which size `j` means modulus at most `L ^ j`. Let
`W = commonVectors x y v` be the set of the `w` with `v w = 0` and `|x⁻¹ w|² + |(x y)⁻¹ w|² < 1`.
Then some measurable `φ` is a common bound for `W` with constant `L²`: `φ u` bounds the inverse area
of `⟨u, W⟩` and the area of the numbers `c` with `⟨c u, W⟩` inside `productDifferences`, a subset of
the unit disc, and the integral of `φ ^ volumeExponent` over the vectors of size `j` is at most
`(L²) ^ (99 n (j + 1))`. -/
lemma RealPlaceSizes.exists_isCommonBound (hF : RealPlaceSizes 𝔰 ρ s b) (hρ : ρ ≤ L)
    {S : Size (𝔰.middleGram (1 : ℂ))} (hS : ∀ j : ℕ, S.ofSize j = {c : ℂ | ‖c‖ ≤ L ^ j})
    (x y : 𝔰.G₁) (v : Matrix (Fin 𝔰.ϱ) hF.complexData.FreeIndex ℂ) :
    ∃ φ : (hF.complexData.FreeIndex → ℂ) → ℝ≥0∞, hF.complexData.IsCommonBound S
      (ENNReal.ofReal L ^ 2) (hF.complexData.commonVectors x y v) φ := by
  -- At most `3 n` linear conditions on `w` give `v w = 0` and put `x⁻¹ w` and `(x y)⁻¹ w` into the
  -- space on which `J₁` is the identity; the columns of `O` are orthonormal solutions, and
  -- `φ u = 36 / |Oᴴ u|²`.
  let e : Matrix 𝔰.BesselIndex hF.complexData.FreeIndex ℂ := hF.complexData.orthonormalPart
  obtain ⟨C, rank_le, hC⟩ :
      ∃ C : Matrix (Fin 𝔰.ϱ ⊕ (Fin 𝔰.ϱ ⊕ Unit) ⊕ Fin 𝔰.ϱ ⊕ Unit) hF.complexData.FreeIndex ℂ,
        C.rank ≤ 3 * 𝔰.n ∧ ∀ w : hF.complexData.FreeIndex → ℂ, C *ᵥ w = 0 →
          v *ᵥ w = 0 ∧ ∀ g ∈ ({x⁻¹, (x * y)⁻¹} : Set 𝔰.G₁),
            𝔰.J₁ *ᵥ g.val.val *ᵥ e *ᵥ w = g.val.val *ᵥ e *ᵥ w :=
    hF.exists_rank_le_and_fixed_of_mulVec_eq_zero x y v (by simp)
  have exponent_eq : hF.complexData.volumeExponent = s := by
    rw [PlaceData.volumeExponent, hF.card_freeIndex_complexData]
    lia
  obtain ⟨D, O, hCO, hO, h_int⟩ :
      ∃ (D : Finset hF.complexData.FreeIndex) (O : Matrix hF.complexData.FreeIndex D ℂ),
        C * O = 0 ∧ Oᴴ * O = 1 ∧ ∀ j : ℕ,
          ∫⁻ u in {u | ∀ i, ‖u i‖ ≤ L ^ j},
              (ENNReal.ofReal (‖star (Oᴴ *ᵥ u) ⬝ᵥ Oᴴ *ᵥ u‖ / 36))⁻¹ ^ s ≤
            (ENNReal.ofReal L ^ 2) ^ (99 * 𝔰.n * (j + 1)) :=
    exists_orthonormal_ker_lintegral_le C hF.card_freeIndex_complexData (hF.four_le.trans hρ)
      rank_le (hF.card_freeIndex_complexData_le.trans hρ)
  have h_ker (t : D → ℂ) : C *ᵥ O *ᵥ t = 0 := by rw [mulVec_mulVec, hCO, zero_mulVec]
  have hv : v * O = 0 := by
    refine Matrix.ext_iff_mulVec.2 fun t ↦ ?_
    rw [← mulVec_mulVec, (hC _ (h_ker t)).1, zero_mulVec]
  have h_fix (g : 𝔰.G₁) (hg : g ∈ ({x⁻¹, (x * y)⁻¹} : Set 𝔰.G₁)) (t : D → ℂ) :
      𝔰.J₁ *ᵥ g.val.val *ᵥ e *ᵥ O *ᵥ t = g.val.val *ᵥ e *ᵥ O *ᵥ t :=
    (hC _ (h_ker t)).2 g hg
  let q (u : hF.complexData.FreeIndex → ℂ) : ℝ := ‖star (Oᴴ *ᵥ u) ⬝ᵥ Oᴴ *ᵥ u‖
  have h_disc (u : hF.complexData.FreeIndex → ℂ) (hu : 0 < q u) : closedBall 0 (√(q u) / 2) ⊆
      (fun w ↦ star u ⬝ᵥ w) '' hF.complexData.commonVectors x y v := by
    rw [← abs_of_nonneg (sqrt_nonneg (q u))]
    exact hF.closedBall_subset_image_commonVectors hO hv h_fix rfl (norm_pos_iff.1 hu)
  refine ⟨fun u ↦ (ENNReal.ofReal (q u / 36))⁻¹,
    { measurable := by fun_prop
      inv_volume_le u := ?_
      volume_le u := ?_
      lintegral_le j := by
        simpa only [vecsOfSize, hS, mem_ofPred_eq, exponent_eq] using h_int j }⟩
  · obtain h_zero | h_pos : 0 = q u ∨ 0 < q u := (norm_nonneg _).eq_or_lt
    · simp [← h_zero]
    · exact inv_volume_le_of_closedBall_subset h_pos (h_disc u h_pos)
  · obtain h_zero | h_pos : 0 = q u ∨ 0 < q u := (norm_nonneg _).eq_or_lt
    · simp [← h_zero]
    refine volume_le_of_subset_closedBall h_pos fun c hc ↦ ?_
    -- Test `c` on a common vector `w` whose product with `u` is `√(q u) / 2`.
    obtain ⟨w, hw, hw_eq⟩ :
        ∃ w ∈ hF.complexData.commonVectors x y v, star u ⬝ᵥ w = √(q u) / 2 :=
      h_disc u h_pos (by simp [abs_of_nonneg])
    have h_test : ‖c‖ * (√(q u) / 2) ≤ 1 := by
      simpa [hw_eq, abs_of_nonneg] using hF.norm_le_of_mem_productDifferences (hc w hw)
    rw [mem_closedBall_zero_iff, le_div_iff₀ (sqrt_pos.2 h_pos)]
    linarith

/-- A vector of `𝔰.BesselIndex → ℂ` with entries of modulus at most `R` has squared Euclidean length
at most `r R²`, where `r` is the rank. -/
lemma norm_toLp_sq_le {R : ℝ} {ω : 𝔰.BesselIndex → ℂ} (hω : ∀ k : 𝔰.BesselIndex, ‖ω k‖ ≤ R) :
    ‖toLp 2 ω‖ ^ 2 ≤ 𝔰.r * R ^ 2 := by
  calc ‖toLp 2 ω‖ ^ 2 = ∑ k : 𝔰.BesselIndex, ‖ω k‖ ^ 2 := norm_sq_eq _
    _ ≤ ∑ _k : 𝔰.BesselIndex, R ^ 2 := by
        gcongr with k
        exact hω k
    _ = 𝔰.r * R ^ 2 := by simp

/-- Assume the numerical hypotheses `hF` and `ρ ≤ L`. Take two vectors `ω₁`, `ω₂` indexed by
`𝔰.BesselIndex` whose entries have modulus at most `L ^ i`. Dividing both by `L ^ (i + 2)` gives a
pair in `closePairs` of the place datum `complexData` at ℂ. -/
lemma RealPlaceSizes.smul_mem_closePairs (hF : RealPlaceSizes 𝔰 ρ s b) (hρ : ρ ≤ L) {i : ℕ}
    {ω₁ ω₂ : 𝔰.BesselIndex → ℂ}
    (h₁ : ∀ k : 𝔰.BesselIndex, ‖ω₁ k‖ ≤ L ^ i) (h₂ : ∀ k : 𝔰.BesselIndex, ‖ω₂ k‖ ≤ L ^ i) :
    (((L : ℂ) ^ (i + 2))⁻¹ • ω₁, ((L : ℂ) ^ (i + 2))⁻¹ • ω₂) ∈ hF.complexData.closePairs := by
  have h4 : 4 ≤ L := hF.four_le.trans hρ
  have hr : 8 * 𝔰.r ≤ L := hF.eight_mul_r_le_rho.trans hρ
  have entry_le {ω : 𝔰.BesselIndex → ℂ} (hω : ∀ k : 𝔰.BesselIndex, ‖ω k‖ ≤ L ^ i)
      (k : 𝔰.BesselIndex) : ‖(((L : ℂ) ^ (i + 2))⁻¹ • ω) k‖ ≤ (L ^ 2)⁻¹ := by
    rw [Pi.smul_apply, norm_smul, norm_inv, norm_pow, Complex.norm_of_nonneg (by linarith)]
    grw [hω k]
    field_simp
    rw [pow_add]
  change ‖toLp 2 (((L : ℂ) ^ (i + 2))⁻¹ • ω₁)‖ ^ 2 + ‖toLp 2 (((L : ℂ) ^ (i + 2))⁻¹ • ω₂)‖ ^ 2 < 1
  calc _ ≤ 𝔰.r * (L ^ 2)⁻¹ ^ 2 + 𝔰.r * (L ^ 2)⁻¹ ^ 2 :=
        add_le_add (norm_toLp_sq_le (entry_le h₁)) (norm_toLp_sq_le (entry_le h₂))
    _ = 2 * 𝔰.r / L ^ 4 := by ring
    _ < 1 := by
        rw [div_lt_one (by positivity)]
        linarith [le_self_pow₀ (a := L) (by linarith) four_ne_zero]

/-- The gauge of scale `L ≥ ρ` for the place datum at `ℂ`: a number has size `j` if its modulus is
at most `L ^ j`, and the constant whose powers bound moduli and volumes is the field `loss`, equal
to `L²`. -/
def RealPlaceSizes.gauge (hρ : ρ ≤ L := by rfl) : Gauge hF.complexData := by
  obtain ⟨hk, hr, h4⟩ := hF.k_eq, hF.eight_mul_r_le_rho, hF.four_le.trans hρ
  refine
    { ofSize j := {x | ‖x‖ ≤ L ^ j}
      loss := .ofReal L ^ 2
      mul_mem_ofSize hx hy := (norm_mul_le_of_le hx hy).trans_eq (pow_add ..).symm
      sum_mem_ofSize := fun h_card hf ↦ ?sum
      neg_mem_iff_and_star_mem_iff := by simp
      zero_one_mem_ofSize i :=
        ⟨by simpa using by positivity, by simpa using one_le_pow₀ (by linarith)⟩
      splitGram_and_inv_mem := by
              simp [inv_eq_left_inv IsHermitianInvolution.mul_self, h4.trans',
                (entry_norm_bound_of_unitary IsHermitianInvolution.mem_unitary ..).trans]
      isCompact_ofSize _ := by simpa [closedBall] using isCompact_closedBall (0 : ℂ) _
      two_le_loss := ?le
      loss_ne_top := by simp
      pairs_le := by simp
      one_le_kernelBound := by simpa [abs_of_pos pi_pos] using by linarith [two_le_pi]
      levelUnit_mem_ofSize := by simpa using by linarith
      hasMatrixSize_basisMatrix := ?basis
      traceOne_div_mem_ofSize := ?trace
      hasMatrixSize_boxSet := by
              simp +contextual [HasMatrixSize, (norm_apply_le_l2_opNorm ..).trans, hρ.trans']
      mem_vecsOfSize_of_mem_closePairs := fun ω₁ ω₂ h_close ↦ ?close
      exists_unit_smul_mem_closePairs i _ :=
        ⟨(Units.mk0 ((L : ℂ) ^ (i + 2)) (by simpa using by linarith))⁻¹,
          by simp [abs_of_nonneg, h4.trans'],
          fun _ h₁ _ h₂ ↦ hF.smul_mem_closePairs hρ h₁ h₂⟩
      modulus_le := ?md
      volume_ofSize_le := ?vol
      two_mul_blockRank_le := by simp [hk, PlaceData.blockRank]
      exists_blockKernel := ?block
      exists_commonBound x _ y _ := hF.exists_isCommonBound hρ (fun _ ↦ rfl) x y }
  case block =>
    -- the spheres of ℂ² have mass at most `4 π² L ^ (2 j)` in size `j`
    obtain ⟨l, h_finite, h_dis, h_mass⟩ :=
      exists_isDisintegration_le_sphereDensity (κ := Fin 2) (by simp)
    refine ⟨l, h_finite, h_dis, fun β j ↦ (h_mass β (L ^ j)).trans ?_⟩
    have h_one : 1 ≤ L ^ j := one_le_pow₀ (by linarith)
    have h_sphere : sphereDensity 2 (2 * (L ^ j) ^ 2) ≤ (L ^ 2) ^ (2 * (j + 1)) :=
      calc sphereDensity 2 (2 * (L ^ j) ^ 2) = 4 * π ^ 2 * (L ^ j) ^ 2 := by
            simp only [sphereDensity]
            norm_num
            ring
        _ ≤ L ^ 2 * L ^ 2 * (L ^ j) ^ 4 := by
            gcongr
            exacts [by nlinarith, pi_le_four.trans h4, by norm_num]
        _ = (L ^ 2) ^ (2 * (j + 1)) := by ring
    rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_pow (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by simpa using h_sphere)
  case sum =>
    rify at h_card
    simp_all [pow_succ']
    grw [norm_sum_le, hf]
    simp
    bound
  case le =>
    simp (disch := positivity)
    bound [sq_nonneg (L - 1)]
  case basis =>
    simp [HasMatrixSize, apply_ite, complexBasis, Pi.single_apply, Matrix.one_apply]
    grind [norm_add_le, norm_one, norm_I]
  case trace =>
    simp
    linarith
  case close =>
    have h_entry (k : 𝔰.BesselIndex) : ‖ω₁ k‖ ≤ 1 ∧ ‖ω₂ k‖ ≤ 1 :=
      norm_apply_le_one_of_sq_add_sq_lt_one h_close k
    refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
    · simpa using (h_entry k).1.trans (by linarith)
    · simpa using (norm_sub_le_of_le (h_entry k).1 (h_entry k).2).trans (by linarith)
  case md =>
    simp (disch := positivity) [← ofReal_norm, pow_right_comm]
    bound
  case vol =>
    simp (disch := positivity) [← mem_closedBall_zero_iff, -mem_closedBall]
    grw [pi_le_four, h4]
    ring_nf
    bound

/-- A number has size `j` in the gauge of scale `L` if and only if its modulus is at most
`L ^ j`. -/
lemma RealPlaceSizes.mem_gauge_ofSize_iff (hF : RealPlaceSizes 𝔰 ρ s b) (hρ : ρ ≤ L) {j : ℕ}
    {x : ℂ} : x ∈ (hF.gauge hρ).ofSize j ↔ ‖x‖ ≤ L ^ j :=
  Iff.rfl

/-- At the place `ℂ`, let each of the points `y` and `γ⁻¹ y` be near at `l`: some element of the
partly unitriangular group `partialUnitriangularGroup l` moves it into the box of operator norm at
most `ρ`. Then the leading minors of order `j ≤ l` of `realFrameGram γ`, the matrix of the products
`h(f_a, γ f_b)` of the `n` frame vectors `f = (e_0, …, e_(ϱ-1), z)`, have modulus at most
`ρ ^ (9 n)`. -/
theorem RealPlaceSizes.norm_leadingMinor_le_of_isNear (hF : RealPlaceSizes 𝔰 ρ s b) {l : ℕ}
    {γ y : 𝔰.G₁} (hy : hF.complexData.IsNear l y) (hγy : hF.complexData.IsNear l (γ⁻¹ * y))
    {j : Fin (𝔰.n + 1)} (hj : j.val ≤ l) :
    ‖leadingMinor (realFrameGram γ) j‖ ≤ ρ ^ (9 * 𝔰.n) :=
  (hF.mem_gauge_ofSize_iff le_rfl).1
    ((hF.gauge le_rfl).leadingMinor_mem_ofSize_of_isNear hy hγy hj)

/-! ### Lengths and the depth at the complex place -/

/-- The length of the vector y at the point g: the Euclidean length of g⁻¹ y. -/
def lengthAt (g : 𝔰.G₁) (y : 𝔰.BesselIndex → ℂ) : ℝ := ‖toLp 2 (g⁻¹.val.val *ᵥ y)‖

/-- The length at the point g of the class of y modulo the e_b, b < l: the infimum of the lengths
at g of its lifts. -/
def inducedLength (g : 𝔰.G₁) (l : ℕ) (y : 𝔰.BesselIndex → ℂ) : ℝ :=
  ⨅ y' : {y' : 𝔰.BesselIndex → ℂ // CongrBelow l y y'}, lengthAt g y'

/-- The depth of e_a at the points g and g': the infimum of |ζ|_g² + |ζ|_g'², for the lengths
`inducedLength` modulo the e_b, b < a, over the ζ orthogonal to these e_b with ⟨e_a, ζ⟩ = 1. The
product ⟨e_a, ζ⟩ is the coordinate of ζ at e*_a. -/
def realDepth (a : Fin 𝔰.ϱ) (g g' : 𝔰.G₁) : ℝ :=
  ⨅ ζ : {ζ : 𝔰.BesselIndex → ℂ // IsOrthogonalBelow a ζ ∧ ζ (eStar a) = 1},
    inducedLength g a ζ ^ 2 + inducedLength g' a ζ ^ 2

section Depth

variable {a : Fin 𝔰.ϱ} {g g' : 𝔰.G₁} {l : ℕ} {y : 𝔰.BesselIndex → ℂ} {t : ℝ}

lemma lengthAt_nonneg : 0 ≤ lengthAt g y := norm_nonneg _

lemma lengthAt_smul (c : ℂ) : lengthAt g (c • y) = ‖c‖ * lengthAt g y := by
  simp [lengthAt, norm_smul, mulVec_smul]

lemma inducedLength_nonneg : 0 ≤ inducedLength g l y := Real.iInf_nonneg fun _ ↦ lengthAt_nonneg

lemma realDepth_nonneg : 0 ≤ realDepth a g g' := Real.iInf_nonneg fun _ ↦ by positivity

/-- The squared induced length of y at g is below t exactly if some lift y' of its class modulo the
e_b, b < l, has squared length below t at g. -/
lemma inducedLength_sq_lt_iff :
    inducedLength g l y ^ 2 < t ↔
      ∃ y' : 𝔰.BesselIndex → ℂ, CongrBelow l y y' ∧ lengthAt g y' ^ 2 < t := by
  have : Nonempty {y' : 𝔰.BesselIndex → ℂ // CongrBelow l y y'} := ⟨y, .refl l y⟩
  rw [← lt_sqrt inducedLength_nonneg, inducedLength,
    ciInf_lt_iff ⟨0, forall_mem_range.2 fun _ ↦ lengthAt_nonneg⟩]
  simp [lt_sqrt lengthAt_nonneg]

/-- The depth of the basis vector e_a at the points g and g' is below t exactly if there are a
vector ζ orthogonal to the e_b, b < a, with ⟨e_a, ζ⟩ = 1 and a vector ζ' congruent to ζ modulo these
e_b such that |g⁻¹ ζ|² + |g'⁻¹ ζ'|² < t in the Euclidean length. -/
lemma realDepth_lt_iff {a : Fin 𝔰.ϱ} {g g' : 𝔰.G₁} {t : ℝ} :
    realDepth a g g' < t ↔
      ∃ ζ ζ' : 𝔰.BesselIndex → ℂ, IsOrthogonalBelow a ζ ∧ ζ (eStar a) = 1 ∧ CongrBelow a ζ ζ' ∧
        lengthAt g ζ ^ 2 + lengthAt g' ζ' ^ 2 < t := by
  have : Nonempty {ζ : 𝔰.BesselIndex → ℂ // IsOrthogonalBelow a ζ ∧ ζ (eStar a) = 1} :=
    ⟨Pi.single (eStar a) 1, fun b hb ↦ by simp [Fin.ne_of_lt hb], by simp⟩
  have h_bdd : BddBelow (range
      fun ζ : {ζ : 𝔰.BesselIndex → ℂ // IsOrthogonalBelow a ζ ∧ ζ (eStar a) = 1} ↦
        inducedLength g a ζ ^ 2 + inducedLength g' a ζ ^ 2) :=
    ⟨0, forall_mem_range.2 fun _ ↦ by positivity⟩
  rw [realDepth, ciInf_lt_iff h_bdd]
  constructor
  · -- Choose a lift `ζ₁` at `g`, then a lift `ζ₂` at `g'`.
    rintro ⟨⟨ζ, h_orth, h_one⟩, h_lt⟩
    obtain ⟨ζ₁, h₁, h_lt₁⟩ : ∃ ζ₁ : 𝔰.BesselIndex → ℂ, CongrBelow a ζ ζ₁ ∧
        lengthAt g ζ₁ ^ 2 < t - inducedLength g' a ζ ^ 2 :=
      inducedLength_sq_lt_iff.1 (lt_sub_iff_add_lt.2 h_lt)
    obtain ⟨ζ₂, h₂, h_lt₂⟩ : ∃ ζ₂ : 𝔰.BesselIndex → ℂ, CongrBelow a ζ ζ₂ ∧
        lengthAt g' ζ₂ ^ 2 < t - lengthAt g ζ₁ ^ 2 :=
      inducedLength_sq_lt_iff.1 (lt_sub_comm.1 h_lt₁)
    have h_orth₁ : IsOrthogonalBelow a ζ₁ := h_orth.of_congrBelow h₁ a.isLt.le
    have h_one₁ : ζ₁ (eStar a) = 1 := (h₁.apply_eStar a.isLt.le a).trans h_one
    exact ⟨ζ₁, ζ₂, h_orth₁, h_one₁, h₁.symm.trans h₂, lt_sub_iff_add_lt'.1 h_lt₂⟩
  · rintro ⟨ζ, ζ', h_orth, h_one, h_congr, h_lt⟩
    have h_lt₂ : inducedLength g' a ζ ^ 2 < t - lengthAt g ζ ^ 2 :=
      inducedLength_sq_lt_iff.2 ⟨ζ', h_congr, lt_sub_iff_add_lt'.2 h_lt⟩
    have h_lt₁ : inducedLength g a ζ ^ 2 < t - inducedLength g' a ζ ^ 2 :=
      inducedLength_sq_lt_iff.2 ⟨ζ, .refl a ζ, lt_sub_comm.1 h_lt₂⟩
    exact ⟨⟨ζ, h_orth, h_one⟩, lt_sub_iff_add_lt.1 h_lt₁⟩

/-- At ℂ a number c lies in `stableProducts a x y` exactly if c = ⟨e_a, ω⟩ for a vector ω orthogonal
to the e_b, b < a, whose class modulo these e_b has a lift ω' with |ω|_x² + |ω'|_{x y}² < 1. -/
lemma RealPlaceSizes.mem_stableProducts_iff (hF : RealPlaceSizes 𝔰 ρ s b) {a : Fin 𝔰.ϱ} {x y : 𝔰.G₁}
    {c : ℂ} :
    c ∈ hF.complexData.stableProducts a x y ↔
      ∃ ω ω' : 𝔰.BesselIndex → ℂ, IsOrthogonalBelow a ω ∧ ω (eStar a) = c ∧ CongrBelow a ω ω' ∧
        lengthAt x ω ^ 2 + lengthAt (x * y) ω' ^ 2 < 1 := by
  simp only [PlaceData.stableProducts, PlaceData.IsStable, complexData_closePairs, lengthAt,
    mem_image,
    mem_ofPred_eq]
  tauto

/-- Assume the numerical hypotheses `hF`. For the place datum `complexData` at ℂ, the set
`stableProducts a x y` of products with e_a (see `mem_stableProducts_iff`) is the disc of the c ∈ ℂ
with ‖c‖² d < 1. Here d = `realDepth a x (x * y)` is the depth of e_a at the points x and x y. -/
lemma RealPlaceSizes.stableProducts_eq (hF : RealPlaceSizes 𝔰 ρ s b) (a : Fin 𝔰.ϱ) (x y : 𝔰.G₁) :
    hF.complexData.stableProducts a x y = {c : ℂ | ‖c‖ ^ 2 * realDepth a x (x * y) < 1} := by
  -- For c ≠ 0 write ω = c ζ with ⟨e_a, ζ⟩ = 1; the bound 1 on the squared lengths becomes 1 / |c|².
  ext c
  rw [hF.mem_stableProducts_iff, mem_ofPred_eq]
  obtain rfl | hc := eq_or_ne c 0
  · exact iff_of_true ⟨0, 0, fun _ _ ↦ rfl, rfl, .refl a 0, by simp [lengthAt]⟩ (by simp)
  have hc_pos : 0 < ‖c‖ ^ 2 := by positivity
  rw [← lt_div_iff₀' hc_pos, realDepth_lt_iff]
  constructor
  · rintro ⟨ω, ω', h_orth, h_val, h_congr, h_lt⟩
    refine ⟨c⁻¹ • ω, c⁻¹ • ω', h_orth.smul _, by simp [h_val, hc], h_congr.smul _, ?_⟩
    rw [lengthAt_smul, lengthAt_smul, lt_div_iff₀' hc_pos, norm_inv]
    field_simp
    exact h_lt
  · rintro ⟨ζ, ζ', h_orth, h_val, h_congr, h_lt⟩
    refine ⟨c • ζ, c • ζ', h_orth.smul _, by simp [h_val], h_congr.smul _, ?_⟩
    rwa [lengthAt_smul, lengthAt_smul, mul_pow, mul_pow, ← mul_add, ← lt_div_iff₀' hc_pos]

/-- At ℂ the depth `PlaceData.depth a x y`, the inverse area of the set `stableProducts a x y`, is
the depth `realDepth` of e_a at the points x and x y, divided by π. -/
lemma RealPlaceSizes.depth_eq (hF : RealPlaceSizes 𝔰 ρ s b) (a : Fin 𝔰.ϱ) (x y : 𝔰.G₁) :
    hF.complexData.depth a x y = ENNReal.ofReal (realDepth a x (x * y) / π) := by
  rw [PlaceData.depth, hF.stableProducts_eq]
  set d : ℝ := realDepth a x (x * y)
  obtain h_zero | h_pos : 0 = d ∨ 0 < d :=
    (realDepth_nonneg (a := a) (g := x) (g' := x * y)).eq_or_lt
  · simp [← h_zero]
  have h_ball : {c : ℂ | ‖c‖ ^ 2 * d < 1} = ball 0 √(1 / d) := by
    ext c
    rw [mem_ball_zero_iff, lt_sqrt (norm_nonneg c), lt_div_iff₀ h_pos, mem_ofPred_eq]
  have h_area : volume (ball (0 : ℂ) √(1 / d)) = ENNReal.ofReal (π / d) := by
    rw [← addHaar_closedBall_eq_addHaar_ball, volume_closedBall_eq_ofReal_pi_mul_sq (sqrt_nonneg _),
      sq_sqrt (by positivity), mul_one_div]
  rw [h_ball, h_area, ← ofReal_inv_of_pos (by positivity), inv_div]

/-- If y has length at most L^i at g, then y has size i at g in the gauge of scale L: the entries of
g⁻¹ y have modulus at most L^i. -/
lemma RealPlaceSizes.lengthLeAt_of_lengthAt_le (hF : RealPlaceSizes 𝔰 ρ s b) {g : 𝔰.G₁} {i : ℕ}
    {y : 𝔰.BesselIndex → ℂ} (hρ : ρ ≤ L) (h : lengthAt g y ≤ L ^ i) :
    (hF.gauge hρ).LengthLeAt g i y := by
  intro k
  rw [hF.mem_gauge_ofSize_iff hρ]
  exact (PiLp.norm_apply_le (toLp 2 (g⁻¹.val.val *ᵥ y)) k).trans h

/-- Let y have size i at g in the gauge of scale L: the entries of g⁻¹ y have modulus at most L^i.
Then y has length at most √r L^i at g, where r is the rank. -/
lemma RealPlaceSizes.lengthAt_le_of_lengthLeAt (hF : RealPlaceSizes 𝔰 ρ s b) {g : 𝔰.G₁} {i : ℕ}
    {y : 𝔰.BesselIndex → ℂ} (hρ : ρ ≤ L) (h : (hF.gauge hρ).LengthLeAt g i y) :
    lengthAt g y ≤ √𝔰.r * L ^ i := by
  have hL : 0 ≤ L ^ i := pow_nonneg (by linarith [hF.four_le]) i
  have h_entry (k : 𝔰.BesselIndex) : ‖(g⁻¹.val.val *ᵥ y) k‖ ≤ L ^ i :=
    (hF.mem_gauge_ofSize_iff hρ).1 (h k)
  calc lengthAt g y = ‖toLp 2 (g⁻¹.val.val *ᵥ y)‖ := rfl
    _ ≤ √(𝔰.r * (L ^ i) ^ 2) := le_sqrt_of_sq_le (norm_toLp_sq_le h_entry)
    _ = √𝔰.r * L ^ i := by rw [sqrt_mul (by positivity), sqrt_sq hL]

end Depth

end New.Floors

end RealPlaceGauge

end
