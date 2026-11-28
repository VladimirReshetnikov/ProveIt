import Lib.DiscreteSeries.Bessel.FrameFibre
import Lib.DiscreteSeries.Bruhat.ComplexPlace
import New.Spanning.Bessel.GramSection

/-!
# The mean value inequality over the Gram matrix of two frames

Let `G₁` be the real unitary group `New.Shape.G₁`, `e = (e₁, …, e_ϱ, z)` its frame, `R°` the fixer
of the frame, the product of the unipotent group `𝖴⁰ = New.Shape.Form.besselU0` and the compact
group `H = U(κ)`, and `γ_Z = New.RealPlace.gramSection Z` the section of the map that sends `γ` to
the matrix `Z` of the products of `e` with `γ e`, over the open set `Ω = New.Shape.openCell` of the
invertible `Z` whose inverse has last diagonal entry of absolute value less than `1`.

On the frames `y = γ e` the fibre measure of the Gram map is compared with Haar measure in
`New.LeGramFibre.mconv_fixerHaar_le`. This file bounds the same fibre measure from below, by `dZ`
times a measure on the frames whose products with `e` form the matrix `Z`. Such a frame is `y' Z`
with `y'` dual to `e`. The first `ϱ` vectors of `y'` are moved by `𝖴⁰`, and the part of the last one
in `X₀ = ℂ ^ κ` runs over a sphere.

One can find the measure on the frames over `Z` by letting both frames vary and dividing two
equalities of fibre measures, the one on pairs of frames, which are tuples of `2 (ϱ + 1)` vectors
with an invertible Gram matrix, by the one on frames. Here a fibre measure enters only through the
relation of being at most it (`New.LeFibreMeasure`); the measure over `Z` is computed directly in
coordinates as a lower bound, and the fibre measure on frames is used as an upper bound.

* `New.RealPlace.lintegral_eq_lintegral_sphereMass_mul_dualFrameOfGram`: Lebesgue measure on the
  tuples dual to the frame, in terms of their Gram matrix and of `R°`.
* `New.RealPlace.leGramFibre_gramSectionMeasure`: the law of `s γ_Z e`, with a density proportional
  to `New.RealPlace.gramDiscReal Z ^ (|κ| - 1)`, is at most the fibre measure.
* `New.RealPlace.lintegral_gramSection_le`: the mean value inequality for the integral of
  `f (s' γ_Z s)` over `s, s'` in `R°` and `Z` in `Ω`.

Notions from other files:
* `fixerHaar 𝔰`: the measure `du dh` on `R°`, with `u = unipotentOf q` for Lebesgue measure `dq` and
  `embedH h` for the Haar probability measure `dh` on `U(κ)`.
* `frameCols`, `dualCols`, `isotropicCols`, `definiteCols`, `freeCols`: the matrices with the
  columns `(e₁, …, e_ϱ, z)`, `e*_b`, `e_b`, `x_i`, and `(e_b, x_i)` respectively.
* `J₁`: the hermitian form on the space with the basis `e_b, x_i, z, e*_b`, which pairs `e_b` with
  `e*_b`, is the identity on `X₀` and is `-1` at `z`.
* `top`, `k`, `k₀`: the last index of the frame, the number `|κ|` and a chosen element of `κ`.
* `embedH h`: the element of `G₁` that acts by `h` on `X₀` and fixes the other basis vectors.
* `hermOfReal t`: the hermitian matrix with the real coordinates `t`.

## Relation to the literature

Part of the bound on the open cell for the Bessel integrals at a real place; see
`New.Spanning.Bessel.FillingData`. For fibre measures of the Gram map compare Siegel, Über die
analytische Theorie der quadratischen Formen, Ann. of Math. 36 (1935).
-/

noncomputable section

namespace New.RealPlace

open Matrix MeasureTheory Measure Shape ENNReal Complex Fin Fintype Norms.L2Operator
  Floors.FloorGroups

variable {𝔰 : Shape}

/-! ### The measure on the fixer of the frame -/

/-- The integral for `fixerHaar 𝔰`, the measure on the fixer of the frame, is the iterated integral
of the value at `u h`. Here `h` runs over `U(κ)` with Haar probability measure, and `u` runs over
the unipotent group `𝖴⁰` with `besselHaar₀`, the image of Lebesgue measure under `unipotentOf`. -/
theorem lintegral_fixerHaar {φ : 𝔰.G₁ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ s : 𝔰.G₁, φ s ∂fixerHaar 𝔰 =
      ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), ∫⁻ u : besselU0, φ (u.val * embedH h) ∂𝔰.besselHaar₀ := by
  rw [fixerHaar, Floors.lintegral_mconv_symm hφ, lintegral_map (by fun_prop) (by fun_prop)]
  exact lintegral_congr fun h ↦ lintegral_map (by fun_prop) measurable_subtype_coe

/-- The integral for `fixerHaar 𝔰`, the measure on the fixer of the frame, in coordinates: the
iterated integral of the value at `unipotentOf q * embedH h`, for Lebesgue measure in the parameter
`q` of the unipotent group and Haar measure in `h` on `U(κ)`. -/
theorem lintegral_fixerHaar_eq_unipotentOf {φ : 𝔰.G₁ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ s : 𝔰.G₁, φ s ∂fixerHaar 𝔰 =
      ∫⁻ q : 𝔰.UnipotentParams, ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), φ (unipotentOf q * embedH h) := by
  rw [lintegral_fixerHaar hφ, lintegral_lintegral_swap (by fun_prop)]
  exact lintegral_map (by fun_prop) (continuous_unipotentOf.subtype_mk _).measurable

/-- The measure `fixerHaar 𝔰`, that is `du dh` on the fixer `R° = 𝖴⁰ H` of the frame, is invariant
under inversion: the integral of `φ` is the iterated integral of `φ ((u h)⁻¹)`. -/
theorem lintegral_fixerHaar_eq_inv {φ : 𝔰.G₁ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ s : 𝔰.G₁, φ s ∂fixerHaar 𝔰 =
      ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), ∫⁻ u : besselU0, φ (u.val * embedH h)⁻¹ ∂𝔰.besselHaar₀ := by
  -- We have `(u h)⁻¹ = (h⁻¹ u⁻¹ h) h⁻¹`. Inversion keeps `du` and `dh`, and conjugation by `h`
  -- keeps `du`.
  rw [lintegral_fixerHaar hφ, ← lintegral_inv_eq_self]
  refine lintegral_congr fun h ↦ ?_
  have h_mem : embedH h⁻¹ ∈ besselS :=
    mem_besselS_of_mem_besselFixer (mem_besselFixer_of_mem_besselH (toBesselH_mem h⁻¹))
  rw [← ((measurePreserving_conj_bessel mem_besselU0_iff_apply besselS_le_normalizer_besselU0
    h_mem).comp (measurePreserving_inv 𝔰.besselHaar₀)).lintegral_comp (by fun_prop)]
  simp [mul_assoc]

/-! ### Tuples dual to the frame -/

theorem re_hermOfReal_apply_self {n : Type} [DecidableEq n] (t : Matrix n n ℝ) (a : n) :
    (hermOfReal t a a).re = t a a := by simp [hermOfReal, skewOfReal]

/-- Taking a principal submatrix along an injective map commutes with `hermOfReal`. -/
theorem submatrix_hermOfReal {m n : Type} [DecidableEq m] [DecidableEq n] (t : Matrix n n ℝ)
    {f : m → n} (hf : f.Injective) :
    (hermOfReal t).submatrix f f = hermOfReal (t.submatrix f f) := by
  simp [hermOfReal, skewOfReal, ← ext_iff, hf.eq_iff]

/-- The equivalence of `Fin j ⊕ Unit` with `Fin (j + 1)` that sends `inl b` to `b.castSucc` and the
point of `Unit` to `Fin.last j`. -/
def splitLast (j : ℕ) : Fin j ⊕ Unit ≃ Fin (j + 1) :=
  (Equiv.optionEquivSumPUnit _).symm.trans finSuccEquivLast.symm

/-- The matrix `joinCol (splitLast j) p`, made of the `j` columns of `p.1` followed by the vector
`p.2`, agrees with `p.1` in each column before the last. -/
@[simp]
theorem joinCol_castSucc {l : Type} [Fintype l] [DecidableEq l] {j : ℕ}
    (p : Matrix l (Fin j) ℂ × (l → ℂ)) (i : l) (b : Fin j) :
    joinCol (splitLast j) p i b.castSucc = p.1 i b := by
  simpa [splitLast] using joinCol_inl (splitLast j) p i b

/-- The matrix `joinCol (splitLast j) p`, made of the `j` columns of `p.1` followed by the vector
`p.2`, has the last column `p.2`. -/
@[simp]
theorem joinCol_last {l : Type} [Fintype l] [DecidableEq l] {j : ℕ}
    (p : Matrix l (Fin j) ℂ × (l → ℂ)) (i : l) : joinCol (splitLast j) p i (last j) = p.2 i := by
  simpa [splitLast] using joinCol_inr (splitLast j) p i

/-- For a hermitian matrix `T` of size `ϱ + 1` (a `FrameMatrix`), the tuple of the vectors
`e*_b + ½ ∑_a T_{ab} e_a`, `b < ϱ`, and `-z + ∑_a T_{a,last} e_a + √(1 + T_{last,last}) x_{k₀}`,
as the columns of a matrix whose rows are indexed by the basis `e_a, x_i, z, e*_a` (`BesselIndex`).
Here `x_{k₀}` is the chosen basis vector of `X₀`. The tuple is dual to the frame `(e₁, …, e_ϱ, z)`,
and it has the Gram matrix `T` if the number under the root is not negative
(`New.RealPlace.gram_dualFrameOfGram`). -/
def dualFrameOfGram (T : 𝔰.FrameMatrix) : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ :=
  joinCol (splitLast 𝔰.ϱ)
    (𝔰.dualCols + 𝔰.isotropicCols * ((2⁻¹ : ℂ) • T.submatrix castSucc castSucc),
      -Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ (fun a : Fin 𝔰.ϱ ↦ T a.castSucc 𝔰.top) +
        𝔰.definiteCols *ᵥ √(1 + (T 𝔰.top 𝔰.top).re) • Pi.single 𝔰.k₀ 1)

@[fun_prop]
theorem continuous_dualFrameOfGram : Continuous (dualFrameOfGram (𝔰 := 𝔰)) := by
  unfold dualFrameOfGram
  fun_prop

/-- The coefficient of `e_a`, the basis vector with the index `.inl a`, in column `b` of
`dualFrameOfGram T` is the entry `T a.castSucc b` in row `a` of `T`, halved when `b ≠ top`, i.e. in
the first `ϱ` columns. -/
theorem dualFrameOfGram_apply_inl (T : 𝔰.FrameMatrix) (a : Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)) :
    dualFrameOfGram T (.inl a) b = (if b = 𝔰.top then 1 else 2⁻¹) * T a.castSucc b := by
  induction b using lastCases <;>
    simp [dualFrameOfGram, inclMatrix, Matrix.mul_apply, mulVec, dotProduct, one_apply]

/-- The coefficient of `e*_a`, the basis vector with the index `eStar a`, in column `b` of
`dualFrameOfGram T` is `1` if `b = a` and `0` otherwise. -/
theorem dualFrameOfGram_apply_eStar (T : 𝔰.FrameMatrix) (a : Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)) :
    dualFrameOfGram T (eStar a) b = if b = a.castSucc then 1 else 0 := by
  induction b using lastCases <;> simp [dualFrameOfGram, inclMatrix, Matrix.mul_apply, mulVec,
    dotProduct, one_apply, (castSucc_lt_last a).ne, eq_comm]

/-- The coefficient of `z` in `dualFrameOfGram T` is `-1` in the last column and `0` in the
others. -/
theorem dualFrameOfGram_apply_z (T : 𝔰.FrameMatrix) (b : Fin (𝔰.ϱ + 1)) :
    dualFrameOfGram T 𝔰.z b = if b = 𝔰.top then -1 else 0 := by
  induction b using lastCases <;>
    simp [dualFrameOfGram, inclMatrix, Matrix.mul_apply, mulVec, dotProduct]

/-- The part in `X₀` of `dualFrameOfGram T` is `√(1 + T_{last,last}) x_{k₀}` in the last column and
zero in the others. Here `indexX₀ i` is the index of the basis vector `x_i` of `X₀`. -/
theorem dualFrameOfGram_apply_indexX₀ (T : 𝔰.FrameMatrix) (b : Fin (𝔰.ϱ + 1)) (i : 𝔰.κ) :
    dualFrameOfGram T (𝔰.indexX₀ i) b =
      if b = 𝔰.top ∧ i = 𝔰.k₀ then (√(1 + (T 𝔰.top 𝔰.top).re) : ℂ) else 0 := by
  induction b using lastCases <;> simp [dualFrameOfGram, inclMatrix, Matrix.mul_apply, mulVec,
    dotProduct, one_apply, Pi.single_apply]

/-- Let `T` be a hermitian `(ϱ + 1)×(ϱ + 1)` matrix (`𝔰.FrameMatrix`) with `1 + Re T_{top,top} ≥ 0`.
Then the tuple `dualFrameOfGram T` has the Gram matrix `T` for `𝔰.J₁`. -/
theorem gram_dualFrameOfGram {T : 𝔰.FrameMatrix} (hT : Tᴴ = T)
    (h_top : 0 ≤ 1 + (T 𝔰.top 𝔰.top).re) : (dualFrameOfGram T)ᴴ * 𝔰.J₁ * dualFrameOfGram T = T := by
  set y : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ := dualFrameOfGram T
  have h_form (a b : Fin (𝔰.ϱ + 1)) : (yᴴ * 𝔰.J₁ * y) a b =
      ∑ c : Fin 𝔰.ϱ, (star (y (eStar c) a) * y (.inl c) b + star (y (.inl c) a) * y (eStar c) b) +
        ∑ i : 𝔰.κ, star (y (𝔰.indexX₀ i) a) * y (𝔰.indexX₀ i) b - star (y 𝔰.z a) * y 𝔰.z b := by
    -- The form pairs each `e_c` with `e*_c`, is the identity on `X₀`, and is `-1` at `z`.
    simp [Matrix.mul_apply, splitGram, middleGram, one_apply, Finset.sum_add_distrib]
    ring
  have h_conj (a b : Fin (𝔰.ϱ + 1)) : starRingEnd ℂ (T a b) = T b a := congrFun₂ hT b a
  have h_real : ((T 𝔰.top 𝔰.top).re : ℂ) = T 𝔰.top 𝔰.top := conj_eq_iff_re.1 (h_conj _ _)
  ext a b
  simp only [h_form, y, dualFrameOfGram_apply_inl, dualFrameOfGram_apply_eStar,
    dualFrameOfGram_apply_z, dualFrameOfGram_apply_indexX₀]
  -- The block is `T / 2 + T / 2`, and the corner is `(1 + T_{last,last}) - 1`.
  induction a using lastCases <;> induction b using lastCases
  · simp [← Complex.ofReal_mul, h_top, h_real, (castSucc_lt_last _).ne']
  · simp [h_conj, (castSucc_lt_last _).ne']
  · simp [(castSucc_lt_last _).ne']
  · simp [h_conj, Finset.sum_add_distrib, ← two_mul]

/-- The mass `π ^ k r ^ (k - 1) / (k - 1)!` of the sphere `⟨x, x⟩ = r` in `ℂ ^ k` for the fibre
measure `dx / d⟨x, x⟩` if `r > 0`, and `0` if `r ≤ 0`. The mass is written as half of
`sphereDensity k r = 2 π ^ k r ^ (k - 1) / (k - 1)!`. -/
def sphereMass (k : ℕ) (r : ℝ) : ℝ≥0∞ :=
  (Set.Ioi 0).indicator (fun r : ℝ ↦ ENNReal.ofReal (sphereDensity k r / 2)) r

/-- For `r > 0` the mass of the sphere `⟨x, x⟩ = r` in `ℂ ^ k` is half of
`sphereDensity k r = 2 π ^ k r ^ (k - 1) / (k - 1)!`. -/
theorem sphereMass_of_pos {k : ℕ} {r : ℝ} (hr : 0 < r) :
    sphereMass k r = ENNReal.ofReal (sphereDensity k r / 2) := Set.indicator_of_mem hr _

@[fun_prop]
theorem measurable_sphereMass (k : ℕ) : Measurable (sphereMass k) :=
  Measurable.indicator (by fun_prop) measurableSet_Ioi

theorem continuousAt_sphereMass {k : ℕ} {r : ℝ} (hr : 0 < r) : ContinuousAt (sphereMass k) r := by
  have h_cont : Continuous fun x : ℝ ↦ ENNReal.ofReal (sphereDensity k x / 2) :=
    continuous_ofReal.comp (by fun_prop)
  refine h_cont.continuousAt.congr ?_
  filter_upwards [Ioi_mem_nhds hr] with x hx using (sphereMass_of_pos hx).symm

/-- Coordinates for the last vector `-z + ∑ a_b e_b + x` of a tuple dual to the frame
`(e₁, …, e_ϱ, z)`, where `v = (a, x)` and `x` lies in `X₀ = ℂ ^ κ`, of dimension `k = |κ|` and with
the basis `x_i`. Fix `u = unipotentOf q`, an element of the unipotent group `𝖴⁰` fixing the frame.
Write the vector as `u · embedH h` applied to `-z + ∑ c_b e_b + √(1 + r) x_{k₀}`, where `p = (c, r)`
and `r` is the product of the vector with itself. Here `k₀` is the chosen element of `κ`, `h` lies
in `U(κ)`, and `embedH h` acts as `h` on `X₀` and as the identity elsewhere. Then Lebesgue measure
`dv` is `sphereMass k (1 + r) dc dr dh`, with `dh` the Haar probability measure. -/
theorem lintegral_neg_single_add_freeCols_mulVec_eq {K : (𝔰.BesselIndex → ℂ) → ℝ≥0∞}
    (hK : Measurable K) (q : 𝔰.UnipotentParams) :
    ∫⁻ v : Fin 𝔰.ϱ ⊕ 𝔰.κ → ℂ, K (-Pi.single 𝔰.z (1 : ℂ) + 𝔰.freeCols *ᵥ v) =
      ∫⁻ p : (Fin 𝔰.ϱ → ℂ) × ℝ, sphereMass 𝔰.k (1 + p.2) * ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
        K ((unipotentOf q * embedH h).val.val *ᵥ (-Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ p.1 +
          𝔰.definiteCols *ᵥ √(1 + p.2) • Pi.single 𝔰.k₀ 1)) := by
  -- On these vectors `h` rotates `x` and `u` translates `a`.
  have h_act (h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (a : Fin 𝔰.ϱ → ℂ) (x : 𝔰.κ → ℂ) :
      (unipotentOf q * embedH h).val.val *ᵥ
          (-Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ a + 𝔰.definiteCols *ᵥ x) =
        -Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ (a + q.1 *ᵥ h.val.val *ᵥ x) +
          𝔰.definiteCols *ᵥ h.val.val *ᵥ x := by
    simp [funext_iff, val_unipotentOf_coe, val_toBesselH_apply_coe, mulVec, dotProduct,
      inclMatrix, Matrix.mul_apply, one_apply, Pi.single_apply]
  let translated (a : Fin 𝔰.ϱ → ℂ) (x : 𝔰.κ → ℂ) : ℝ≥0∞ :=
    K (-Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ (a + q.1 *ᵥ x) + 𝔰.definiteCols *ᵥ x)
  calc
    -- split `v = (a, x)` and translate `a` by `q.1 x`
    _ = ∫⁻ x : 𝔰.κ → ℂ, ∫⁻ a : Fin 𝔰.ϱ → ℂ, translated a x := by
      rw [← Floors.measurePreserving_sumElim.lintegral_comp (by fun_prop), volume_eq_prod,
        lintegral_prod_symm _ (by fun_prop)]
      simp only [fromCols_mulVec_sumElim, ← add_assoc]
      exact lintegral_congr fun x : 𝔰.κ → ℂ ↦ (lintegral_add_right_eq_self _ (q.1 *ᵥ x)).symm
    -- polar coordinates in `x`
    _ = ∫⁻ r : ℝ, sphereMass 𝔰.k r *
          ∫⁻ h : U 1, ∫⁻ a, translated a (h.val.val *ᵥ √r • Pi.single 𝔰.k₀ 1) := by
      rw [Floors.lintegral_eq_polar 𝔰.k₀ (by fun_prop), ← lintegral_indicator measurableSet_Ioi]
      simp only [sphereMass, Set.indicator_mul_left]
    -- shift `r` by one and integrate in `h` before `a`
    _ = ∫⁻ p : (Fin 𝔰.ϱ → ℂ) × ℝ, sphereMass 𝔰.k (1 + p.2) *
          ∫⁻ h : U 1, translated p.1 (h.val.val *ᵥ √(1 + p.2) • Pi.single 𝔰.k₀ 1) := by
      rw [← lintegral_add_left_eq_self _ 1, volume_eq_prod, lintegral_prod_symm _ (by fun_prop)]
      refine lintegral_congr fun r : ℝ ↦ ?_
      rw [lintegral_lintegral_swap (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
    _ = _ := by simp only [translated, h_act]

/-- Coordinates on the tuples dual to the frame `e = (e₁, …, e_ϱ, z)`, which are the `J₁ e + R p`:
here `e` is `frameCols`, and `R` is `freeCols`, whose columns are the `e_b` and the basis vectors
`x_i` of `X₀ = ℂ ^ κ`. Write such a tuple as `s y(T)`, where `T = hermOfReal t` is its Gram matrix,
with real coordinates `t`, `y(T) = dualFrameOfGram T` is the standard dual tuple with the Gram
matrix `T`, and `s` lies in the fixer `R°` of the frame, with its measure `ds = fixerHaar 𝔰`. Then
Lebesgue measure `dp` is `2 ^ (-ϱ) sphereMass k r dt ds`, where `k = |κ|` and
`r = 1 + T_{last,last}`. -/
theorem lintegral_eq_lintegral_sphereMass_mul_dualFrameOfGram
    {K : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ, K (𝔰.J₁ * 𝔰.frameCols + 𝔰.freeCols * p) =
      ∫⁻ t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ,
        (2 ^ 𝔰.ϱ)⁻¹ * sphereMass 𝔰.k (1 + (hermOfReal t 𝔰.top 𝔰.top).re) *
          ∫⁻ s : 𝔰.G₁, K (s.val.val * dualFrameOfGram (hermOfReal t)) ∂fixerHaar 𝔰 := by
  -- Choose the first `ϱ` vectors, which fixes the upper left block of `T` and the unipotent part
  -- of `s`, and then the last vector.
  let firstCols (t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ) : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ :=
    𝔰.dualCols + 𝔰.isotropicCols * ((2⁻¹ : ℂ) • hermOfReal t)
  let lastIntegral (Y : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ) : ℝ≥0∞ :=
    ∫⁻ v : Fin 𝔰.ϱ ⊕ 𝔰.κ → ℂ, K (joinCol (splitLast 𝔰.ϱ) (Y, -Pi.single 𝔰.z 1 + 𝔰.freeCols *ᵥ v))
  let tuple (p : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ × (Fin 𝔰.ϱ → ℂ) × ℝ) :
      Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ :=
    joinCol (splitLast 𝔰.ϱ) (firstCols p.1, -Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ p.2.1 +
      𝔰.definiteCols *ᵥ √(1 + p.2.2) • Pi.single 𝔰.k₀ 1)
  let movedIntegrand (p : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ × (Fin 𝔰.ϱ → ℂ) × ℝ) (s : 𝔰.G₁) : ℝ≥0∞ :=
    K (s.val.val * tuple p)
  -- A dual tuple is given by its first `ϱ` vectors and its last one.
  have h_split (p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin 𝔰.ϱ) ℂ) (v : Fin 𝔰.ϱ ⊕ 𝔰.κ → ℂ) :
      𝔰.J₁ * 𝔰.frameCols + 𝔰.freeCols * joinCol (splitLast 𝔰.ϱ) (p, v) = joinCol (splitLast 𝔰.ϱ)
        (𝔰.dualCols + 𝔰.freeCols * p, -Pi.single 𝔰.z 1 + 𝔰.freeCols *ᵥ v) := by
    simp [← ext_iff, forall_fin_succ', mul_joinCol, splitGram, middleGram, inclMatrix,
      Matrix.mul_apply, one_apply, Pi.single_apply]
  -- With the first `ϱ` vectors fixed, integrate over the last one; `h` fixes the first ones.
  have h_last_vector (t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ) (q : 𝔰.UnipotentParams) :
      lastIntegral ((unipotentOf q).val.val * firstCols t) =
        ∫⁻ p : (Fin 𝔰.ϱ → ℂ) × ℝ, sphereMass 𝔰.k (1 + p.2) *
          ∫⁻ h : U 1, movedIntegrand (t, p) (unipotentOf q * embedH h) := by
    have h_first (h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) : (unipotentOf q * embedH h).val.val * firstCols t =
        (unipotentOf q).val.val * firstCols t := by
      simp [firstCols, coe_embedH, actOnCols, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul,
        Matrix.sub_mul, inclMatrix_gram_eq_zero, inclMatrix_gram_mul_eq_zero]
    simp only [movedIntegrand, tuple, mul_joinCol, h_first]
    exact lintegral_neg_single_add_freeCols_mulVec_eq (K := fun v : 𝔰.BesselIndex → ℂ ↦
      K (joinCol (splitLast 𝔰.ϱ) ((unipotentOf q).val.val * firstCols t, v))) (by fun_prop) q
  -- The measure preserving `φ` gives `t` by its upper left block, the rest of the last column of
  -- `hermOfReal t` and its corner.
  obtain ⟨φ, φ_vol, φ_apply⟩ := exists_measurePreserving_hermCorner (splitLast 𝔰.ϱ)
  calc
    _ = ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin 𝔰.ϱ) ℂ, lastIntegral (𝔰.dualCols + 𝔰.freeCols * p) := by
      rw [← (measurePreserving_joinCol (splitLast 𝔰.ϱ)).lintegral_comp (by fun_prop),
        volume_eq_prod, lintegral_prod _ (by fun_prop)]
      simp only [lastIntegral, h_split]
    _ = (2 ^ 𝔰.ϱ)⁻¹ * ∫⁻ t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ, ∫⁻ q : 𝔰.UnipotentParams,
          lastIntegral ((unipotentOf q).val.val * firstCols t) :=
      lintegral_eq_unipotent_coords (by fun_prop)
    _ = ∫⁻ p : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ × (Fin 𝔰.ϱ → ℂ) × ℝ,
          (2 ^ 𝔰.ϱ)⁻¹ * sphereMass 𝔰.k (1 + p.2.2) *
            ∫⁻ s : 𝔰.G₁, movedIntegrand p s ∂fixerHaar 𝔰 := by
      rw [volume_eq_prod (Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ), lintegral_prod _ (by fun_prop),
        ← lintegral_const_mul _ (by fun_prop)]
      refine lintegral_congr fun t ↦ ?_
      rw [lintegral_congr (h_last_vector t), lintegral_lintegral_swap (by fun_prop),
        ← lintegral_const_mul _ (by fun_prop)]
      refine lintegral_congr fun p ↦ ?_
      rw [lintegral_const_mul _ (by fun_prop), lintegral_fixerHaar_eq_unipotentOf (by fun_prop),
        mul_assoc]
    _ = _ := by
      rw [← φ_vol.lintegral_comp (by fun_prop)]
      refine lintegral_congr fun t ↦ ?_
      have h_tuple : tuple (φ t) = dualFrameOfGram (hermOfReal t) := by
        simp [φ_apply, tuple, firstCols, dualFrameOfGram, re_hermOfReal_apply_self,
          submatrix_hermOfReal t (castSucc_injective _), splitLast, Function.comp_def]
      simp only [movedIntegrand, h_tuple]
      simp [φ_apply, re_hermOfReal_apply_self, splitLast]

/-! ### The fibre measure on frames, over the matrix of products with the standard frame -/

/-- Coordinates on the tuples `y = J₁ e Z + R p` whose products with the frame
`e = (e₁, …, e_ϱ, z) = 𝔰.frameCols` form the invertible matrix `Z`, where `R = 𝔰.freeCols` has the
columns `e_b` and `x_i`. Write `y = y' Z`, so that `y'` is dual to the frame and has the Gram matrix
`T' = Z⁻¹ᴴ T Z⁻¹` if `y` has the Gram matrix `T = hermOfReal t`. Then `y' = s · dualFrameOfGram T'`
is the standard dual tuple with the Gram matrix `T'`, moved by an element `s` of the fixer `𝖴⁰ U(κ)`
of the frame, and Lebesgue measure `dp` is `|det Z| ^ (2 (k - 1)) 2 ^ (-ϱ) sphereMass k r dt ds`,
where `k = |κ|` and `r = 1 + T'_{last,last}`. Here `sphereMass k r` is the mass
`π ^ k r ^ (k - 1) / (k - 1)!` of the sphere `⟨x, x⟩ = r` in `ℂ ^ k` if `r > 0`, and `0` otherwise;
`ds = fixerHaar 𝔰` is Lebesgue measure in the parameter of `unipotentOf` on `𝖴⁰` times the Haar
probability measure on `U(κ)`; and `s.val.val` is the matrix of `s`. -/
theorem lintegral_eq_dualFrameOfGram_mul {Z : 𝔰.FrameMatrix} (hZ : Z.det ≠ 0)
    {K : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ, K (𝔰.J₁ * 𝔰.frameCols * Z + 𝔰.freeCols * p) =
      ∫⁻ t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ,
        ‖Z.det‖ₑ ^ (2 * (𝔰.k - 1)) * (2 ^ 𝔰.ϱ)⁻¹ *
            sphereMass 𝔰.k (1 + ((Z⁻¹ᴴ * hermOfReal t * Z⁻¹) 𝔰.top 𝔰.top).re) *
          ∫⁻ s : 𝔰.G₁, K (s.val.val * dualFrameOfGram (Z⁻¹ᴴ * hermOfReal t * Z⁻¹) * Z)
            ∂fixerHaar 𝔰 := by
  -- The substitution costs `|det Z| ^ (2 (ϱ + k))` in `dp` and `|det Z| ^ (2 (ϱ + 1))` in `dT`.
  let dualIntegrand (T : 𝔰.FrameMatrix) : ℝ≥0∞ :=
    (2 ^ 𝔰.ϱ)⁻¹ * sphereMass 𝔰.k (1 + (T 𝔰.top 𝔰.top).re) *
      ∫⁻ s : 𝔰.G₁, K (s.val.val * dualFrameOfGram T * Z) ∂fixerHaar 𝔰
  have h_exp : 2 * card (Fin 𝔰.ϱ ⊕ 𝔰.κ) = 2 * (𝔰.k - 1) + 2 * card (Fin (𝔰.ϱ + 1)) := by
    grind [card_sum, card_fin, card_pos_iff.2 (⟨𝔰.k₀⟩ : Nonempty 𝔰.κ)]
  calc
    _ = ‖Z.det‖ₑ ^ (2 * card (Fin 𝔰.ϱ ⊕ 𝔰.κ)) * ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ,
          K ((𝔰.J₁ * 𝔰.frameCols + 𝔰.freeCols * p) * Z) := by
      rw [lintegral_eq_det_mul_comp_mul_mul (P := 1) (by simp) hZ (by fun_prop)]
      simp [Matrix.add_mul, Matrix.mul_assoc]
    _ = ‖Z.det‖ₑ ^ (2 * card (Fin 𝔰.ϱ ⊕ 𝔰.κ)) * ∫⁻ t, dualIntegrand (hermOfReal t) := by
      rw [lintegral_eq_lintegral_sphereMass_mul_dualFrameOfGram (K := fun y ↦ K (y * Z))
        (by fun_prop)]
    _ = ‖Z.det‖ₑ ^ (2 * (𝔰.k - 1)) * ∫⁻ t, dualIntegrand (Z⁻¹ᴴ * hermOfReal t * Z⁻¹) := by
      rw [lintegral_eq_det_mul_comp_congruence hZ (G := fun T ↦ dualIntegrand (Z⁻¹ᴴ * T * Z⁻¹))
        (by fun_prop), h_exp, pow_add, mul_assoc]
      simp [← Matrix.mul_assoc, ← conjTranspose_mul, hZ]
    _ = _ := by simp (disch := finiteness) only [dualIntegrand, mul_assoc, lintegral_const_mul']

/-- The Gram matrix of the frame is `diag(0, …, 0, -1)`; so its congruence by `Z⁻¹` is `-ζᴴ ζ` for
the last row `ζ` of `Z⁻¹`. -/
theorem inv_frameGram_inv_apply (Z : 𝔰.FrameMatrix) (a b : Fin (𝔰.ϱ + 1)) :
    (Z⁻¹ᴴ * (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols) * Z⁻¹) a b =
      -(starRingEnd ℂ (Z⁻¹ 𝔰.top a) * Z⁻¹ 𝔰.top b) := by
  simp [Matrix.mul_apply, splitGram, middleGram, inclMatrix, one_apply, sum_univ_castSucc]

/-- For the congruence `T` by `Z⁻¹` of the Gram matrix of the frame, `1 + T_{last,last}` is
`oneSubNormSqInvCorner Z = 1 - |ξ|²`, with `ξ` the last diagonal entry of `Z⁻¹`. -/
theorem one_add_inv_frameGram_inv_top (Z : 𝔰.FrameMatrix) :
    1 + ((Z⁻¹ᴴ * (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols) * Z⁻¹) 𝔰.top 𝔰.top).re =
      oneSubNormSqInvCorner Z := by
  rw [inv_frameGram_inv_apply, conj_mul', ← Complex.ofReal_pow, neg_re, ofReal_re,
    oneSubNormSqInvCorner, invCorner, sub_eq_add_neg]

/-- Let `ζ` be the last row of `Z⁻¹`. Row `a < ϱ` of `sectionCoeff Z Zᴴ` is row `a` of `-ζᴴ ζ`,
halved in the first `ϱ` columns. The matrix `sectionCoeff Z W` is built from the last row of `Z⁻¹`
and the last column of `W⁻¹`. -/
theorem sectionCoeff_conjTranspose_castSucc_apply (Z : 𝔰.FrameMatrix) (a : Fin 𝔰.ϱ)
    (b : Fin (𝔰.ϱ + 1)) :
    sectionCoeff Z Zᴴ a.castSucc b =
      (if b = 𝔰.top then 1 else 2⁻¹) * -(starRingEnd ℂ (Z⁻¹ 𝔰.top a.castSucc) * Z⁻¹ 𝔰.top b) := by
  -- The last factor of `sectionCoeff` doubles the last column of the product of the others.
  have h_prod : (diagLast (𝔰 := 𝔰) 0 * Zᴴ⁻¹ * (1 - diagLast (𝔰 := 𝔰) 2⁻¹) * Z⁻¹) a.castSucc b =
      2⁻¹ * (starRingEnd ℂ (Z⁻¹ 𝔰.top a.castSucc) * Z⁻¹ 𝔰.top b) := by
    simp [diagLast, Matrix.mul_apply, sum_univ_castSucc, one_apply, diagonal_apply,
      (castSucc_lt_last _).ne', ← conjTranspose_nonsing_inv, mul_comm, mul_left_comm,
      show (1 - 2⁻¹ : ℂ) = 2⁻¹ by norm_num]
  have h_two : diagLast (𝔰 := 𝔰) 2 = diagonal (snoc 1 2) := rfl
  rw [sectionCoeff, h_two, Matrix.sub_apply, mul_diagonal, h_prod]
  induction b using lastCases <;> simp [diagLast, one_apply, diagonal_apply,
    mul_right_comm _ _ (2 : ℂ)]

/-- The last row of `sectionCoeff Z Zᴴ` is `(0, …, 0, -1)`. For `Z` in the open cell, the columns of
`sectionCoeff Z W` at `W = Zᴴ` are the coefficients of `e₁, …, e_ϱ, z` in the tuple `y'` that is
dual to the frame `e` and has `γ_Z e = y' Z`. -/
theorem sectionCoeff_conjTranspose_top_apply (Z : 𝔰.FrameMatrix) (b : Fin (𝔰.ϱ + 1)) :
    sectionCoeff Z Zᴴ 𝔰.top b = if b = 𝔰.top then -1 else 0 := by
  induction b using lastCases <;>
    simp [sectionCoeff, diagLast, Matrix.mul_assoc, (castSucc_lt_last _).ne']

/-- For `Z` in the open cell and `γ_Z = gramSection Z`, the chosen element of `G₁` for which the
products of `e` with `γ_Z e` form `Z`, the image `γ_Z e` of the frame `e = 𝔰.frameCols` is `y' Z`,
where `y'` is the tuple dual to `e` that `New.RealPlace.dualFrameOfGram` attaches to the congruence
by `Z⁻¹` of the Gram matrix of `e`. -/
theorem dualFrameOfGram_mul_eq_gramSection_mul {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    dualFrameOfGram (Z⁻¹ᴴ * (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols) * Z⁻¹) * Z =
      ((gramSection Z : GL 𝔰.BesselIndex ℂ) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) *
        𝔰.frameCols := by
  -- Compare the coefficients of the vectors e_a, x_i, z and e*_a in the two tuples.
  rw [coe_gramSection hZ, sectionMatrix_mul_frameCols, sectionFrame,
    sqrt_eq_sqrt_oneSubNormSqInvCorner hZ]
  suffices h_dual : dualFrameOfGram (Z⁻¹ᴴ * (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols) * Z⁻¹) =
      𝔰.frameCols * sectionCoeff Z Zᴴ +
        𝔰.dualFrameCols * diagLast (𝔰 := 𝔰) (√(oneSubNormSqInvCorner Z) : ℂ) by rw [h_dual]
  ext (a | (i | i) | a) b
  -- the coefficient of `e_a`
  · rw [dualFrameOfGram_apply_inl, inv_frameGram_inv_apply,
      ← sectionCoeff_conjTranspose_castSucc_apply]
    simp [Matrix.mul_apply, inclMatrix, one_apply, sum_univ_castSucc]
  -- the coefficient of `x_i`, in either case for the last column and for the others
  · rw [dualFrameOfGram_apply_indexX₀, one_add_inv_frameGram_inv_top]
    induction b using lastCases <;>
      simp [Matrix.mul_apply, inclMatrix, one_apply, sum_univ_castSucc, diagLast, diagonal_apply]
  -- the coefficient of `z`
  · rw [dualFrameOfGram_apply_z, ← sectionCoeff_conjTranspose_top_apply Z]
    simp [Matrix.mul_apply, inclMatrix, one_apply, sum_univ_castSucc]
  -- the coefficient of `e*_a`
  · rw [dualFrameOfGram_apply_eStar]
    induction b using lastCases <;>
      simp [Matrix.mul_apply, inclMatrix, one_apply, sum_univ_castSucc, diagLast, diagonal_apply,
        eq_comm, (castSucc_lt_last _).ne]

/-- The measure on `G₁` that is the law of `s γ_Z`, for `Z` in the open cell and `s` in the fixer
`R°` of the frame, under `dZ ds` with the density `2 ^ (-ϱ) π ^ k 𝗀(Z) ^ (k - 1) / (k - 1)!`. Here
`γ_Z = New.RealPlace.gramSection Z` and `𝗀 = New.RealPlace.gramDiscReal`. -/
def gramSectionMeasure (𝔰 : Shape) : Measure 𝔰.G₁ :=
  (((volume.restrict 𝔰.openCell).prod (fixerHaar 𝔰)).withDensity
      fun p : 𝔰.FrameMatrix × 𝔰.G₁ ↦ ENNReal.ofReal
        (sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal p.1 ^ (𝔰.k - 1))).map
    fun p : 𝔰.FrameMatrix × 𝔰.G₁ ↦ p.2 * gramSection p.1

instance : SFinite (gramSectionMeasure 𝔰) := by
  unfold gramSectionMeasure
  infer_instance

/-- Let `T = hermOfReal t`, let `Z` be invertible and put `T' = Z⁻¹ᴴ T Z⁻¹`. If
`1 + T'_{last,last} ≥ 0`, then for all `s` in `G₁` the tuple `s (dualFrameOfGram T') Z` has the
Gram matrix `T`, that is, its Gram coordinates `gramCoords` are `t`. -/
theorem gramCoords_dualFrameOfGram_mul {Z : 𝔰.FrameMatrix} (hZ : Z.det ≠ 0)
    {t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ}
    (h_corner : 0 ≤ 1 + ((Z⁻¹ᴴ * hermOfReal t * Z⁻¹) 𝔰.top 𝔰.top).re) (s : 𝔰.G₁) :
    gramCoords 𝔰.J₁ (s.val.val * dualFrameOfGram (Z⁻¹ᴴ * hermOfReal t * Z⁻¹) * Z) = t := by
  rw [Matrix.mul_assoc, gramCoords_U_mul, gramCoords_eq_iff, gram_mul,
    gram_dualFrameOfGram (by simp [Matrix.mul_assoc]) h_corner]
  simp [← Matrix.mul_assoc, ← conjTranspose_mul, hZ]

/-- A matrix in the open cell, the set of invertible `Z` whose inverse has last diagonal entry of
absolute value less than `1`, has nonzero determinant. -/
theorem det_ne_zero_of_mem_openCell {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) : Z.det ≠ 0 := hZ.left

/-- Let `𝔰` be a shape with `ϱ` hyperbolic pairs and index set `κ`, and let `k = |κ|`. Let `Z` lie
in the open cell `𝔰.openCell`: `Z` is invertible and the last diagonal entry of `Z⁻¹` has absolute
value less than 1. Let `𝗀(Z) = gramDiscReal Z` be `|det Z|²` minus the squared absolute value of the
leading minor of order `ϱ` of `Z`. Take the mass `sphereMass` of the sphere in `ℂ ^ k` of squared
radius `oneSubNormSqInvCorner Z = 𝗀(Z) / |det Z|²`, and multiply it by
`|det Z| ^ (2 (k - 1)) 2 ^ (-ϱ)`. The result is the density
`2 ^ (-(ϱ + 1)) sphereDensity k 1 · 𝗀(Z) ^ (k - 1)` of `New.RealPlace.gramSectionMeasure`. -/
theorem enorm_det_pow_mul_sphereMass {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    ‖Z.det‖ₑ ^ (2 * (𝔰.k - 1)) * (2 ^ 𝔰.ϱ)⁻¹ * sphereMass 𝔰.k (oneSubNormSqInvCorner Z) =
      ENNReal.ofReal (sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal Z ^ (𝔰.k - 1)) := by
  have h_real : sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal Z ^ (𝔰.k - 1) =
      ‖Z.det‖ ^ (2 * (𝔰.k - 1)) * (2 ^ 𝔰.ϱ)⁻¹ *
        (sphereDensity 𝔰.k (oneSubNormSqInvCorner Z) / 2) := by
    simp only [sphereDensity, gramDiscReal_eq_norm_det_sq_mul (det_ne_zero_of_mem_openCell hZ)]
    ring
  rw [h_real, sphereMass_of_pos (oneSubNormSqInvCorner_pos hZ), ENNReal.ofReal_mul (by positivity)]
  simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos]

/-- The integral of `K ≥ 0` over the tuples `J₁ e Z + R p` with `Z` in the open cell, where `e` is
the frame and `R = 𝔰.freeCols`, is at most its integral over all tuples. -/
theorem setLIntegral_openCell_frame_coords_le
    {K : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ Z : 𝔰.FrameMatrix in 𝔰.openCell, ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ,
        K (𝔰.J₁ * 𝔰.frameCols * Z + 𝔰.freeCols * p) ≤
      ∫⁻ y : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ, K y := by
  have h_vol : MeasurePreserving fun p : 𝔰.FrameMatrix × Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ ↦
      𝔰.J₁ * 𝔰.frameCols * p.1 + 𝔰.freeCols * p.2 :=
    measurePreserving_mul_mul_add_mul conjTranspose_frameCols_mul_self
      conjTranspose_freeCols_mul_self frameCols_gram_freeCols
      card_frame_add_card_free
  rw [← h_vol.lintegral_comp hK, volume_eq_prod, lintegral_prod _ (by fun_prop)]
  exact setLIntegral_le_lintegral _ _

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `e = 𝔰.frameCols` be the matrix with the columns `e₁, …, e_ϱ, z` of the frame and `𝔰.J₁` the
matrix of the hermitian form that defines `G₁`. The measure `gramSectionMeasure 𝔰` is the law of
`s γ_Z` under `2 ^ (-ϱ) π ^ k / (k - 1)! · 𝗀(Z) ^ (k - 1) dZ ds`, where `Z` runs over the open cell,
`s` over the fixer of `e` with `ds = fixerHaar 𝔰`, `γ_Z = gramSection Z`, `k = |κ|`, and
`𝗀(Z) = gramDiscReal Z` is `|det Z|²` less the squared absolute value of the leading minor of order
`ϱ`. The image `l` of this measure under `g ↦ g e` is at most the fibre measure `dY / dT` of the
Gram map `Y ↦ T = Yᴴ J₁ Y` over the Gram matrix `T₀` of `e`. Here `dY` is Lebesgue measure on the
matrices `Y` of the size of `e`, and `dT` is Lebesgue measure in the real coordinates of `T`
(`hermOfReal`). By the definition of `LeGramFibre` this means: if `K ≥ 0` is lower semicontinuous
and `∫_{T(Y) ∈ S} K dY ≤ C vol(S)` for all open `S` inside some neighbourhood of `T₀`, then
`∫ K dl ≤ C`. -/
theorem leGramFibre_gramSectionMeasure :
    LeGramFibre 𝔰.J₁ 𝔰.frameCols (gramSectionMeasure 𝔰) := by
  -- The tuples with `Z` in the open cell have the coordinates `tuple t (Z, s)`, with the density
  -- `density t (Z, s)` for `dt` and `μ = dZ ds`. At the coordinates `t₀` of the Gram matrix of `e`
  -- the point is `s γ_Z e` and the sphere has the squared radius `oneSubNormSqInvCorner Z`.
  let μ : Measure (𝔰.FrameMatrix × 𝔰.G₁) := (volume.restrict 𝔰.openCell).prod (fixerHaar 𝔰)
  let congrGram (t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ) (Z : 𝔰.FrameMatrix) :
      𝔰.FrameMatrix := Z⁻¹ᴴ * hermOfReal t * Z⁻¹
  let tuple (t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ) (p : 𝔰.FrameMatrix × 𝔰.G₁) :
      Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ :=
    p.2.val.val * dualFrameOfGram (congrGram t p.1) * p.1
  let density (t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ) (p : 𝔰.FrameMatrix × 𝔰.G₁) : ℝ≥0∞ :=
    ‖p.1.det‖ₑ ^ (2 * (𝔰.k - 1)) * (2 ^ 𝔰.ϱ)⁻¹ *
      sphereMass 𝔰.k (1 + (congrGram t p.1 𝔰.top 𝔰.top).re)
  let t₀ : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ := gramCoords 𝔰.J₁ 𝔰.frameCols
  have ht₀ : hermOfReal t₀ = 𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols :=
    hermOfReal_gramCoords IsHermitianInvolution.isHermitian _
  have h_cell : ∀ᵐ p ∂μ, p.1 ∈ 𝔰.openCell :=
    quasiMeasurePreserving_fst.ae (ae_restrict_mem isOpen_openCell.measurableSet)
  have h_corner (Z : 𝔰.FrameMatrix) :
      1 + (congrGram t₀ Z 𝔰.top 𝔰.top).re = oneSubNormSqInvCorner Z := by
    simp only [congrGram, ht₀, one_add_inv_frameGram_inv_top]
  have h_fibre (t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ) :
      ∀ᵐ p ∂μ, density t p ≠ 0 → gramCoords 𝔰.J₁ (tuple t p) = t := by
    filter_upwards [h_cell] with p hp h_ne_zero
    have h_pos : 0 < 1 + (congrGram t p.1 𝔰.top 𝔰.top).re :=
      Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h_ne_zero)
    exact gramCoords_dualFrameOfGram_mul (det_ne_zero_of_mem_openCell hp) h_pos.le p.2
  have h_cont : ∀ᵐ p ∂μ, ContinuousAt (tuple · p) t₀ ∧ ContinuousAt (density · p) t₀ := by
    filter_upwards [h_cell] with p hp
    have h_mass : ContinuousAt (fun t ↦ sphereMass 𝔰.k (1 + (congrGram t p.1 𝔰.top 𝔰.top).re)) t₀ :=
      (continuousAt_sphereMass (oneSubNormSqInvCorner_pos hp)).comp_of_eq (by fun_prop)
        (h_corner p.1)
    exact ⟨by fun_prop, ENNReal.Tendsto.const_mul h_mass (.inr (by finiteness))⟩
  have h_le (K : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ → ℝ≥0∞) (hK : Measurable K) :
      ∫⁻ t in Set.univ, ∫⁻ p, density t p * K (tuple t p) ∂μ ≤ ∫⁻ y, K y := calc
    _ = ∫⁻ Z in 𝔰.openCell, ∫⁻ t, ∫⁻ s, density t (Z, s) * K (tuple t (Z, s)) ∂fixerHaar 𝔰 := by
      rw [restrict_univ, lintegral_lintegral_swap (by fun_prop), lintegral_prod _ (by fun_prop)]
      exact lintegral_congr fun Z ↦ lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ Z in 𝔰.openCell, ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ,
          K (𝔰.J₁ * 𝔰.frameCols * Z + 𝔰.freeCols * p) := by
      refine setLIntegral_congr_fun isOpen_openCell.measurableSet fun Z hZ ↦ ?_
      simp (disch := fun_prop) only [density, tuple, congrGram, lintegral_const_mul,
        lintegral_eq_dualFrameOfGram_mul (det_ne_zero_of_mem_openCell hZ) hK]
    _ ≤ ∫⁻ y, K y := setLIntegral_openCell_frame_coords_le hK
  have h_density : ∀ᵐ p ∂μ, density t₀ p =
      ENNReal.ofReal (sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal p.1 ^ (𝔰.k - 1)) :=
    h_cell.mono fun p hp ↦ by simp only [density, h_corner, enorm_det_pow_mul_sphereMass hp]
  have h_point : ∀ᵐ p ∂μ, (p.2 * gramSection p.1).val.val * 𝔰.frameCols = tuple t₀ p :=
    h_cell.mono fun p hp ↦ by simp only [tuple, congrGram, ht₀, Subgroup.coe_mul, Units.val_mul,
      Matrix.mul_assoc p.2.val.val, dualFrameOfGram_mul_eq_gramSection_mul hp]
  have h_law : (gramSectionMeasure 𝔰).map (fun g : 𝔰.G₁ ↦ g.val.val * 𝔰.frameCols) =
      (μ.withDensity (density t₀)).map (tuple t₀) := by
    rw [gramSectionMeasure, Measure.map_map (by fun_prop) (by fun_prop),
      ← withDensity_congr_ae h_density]
    exact Measure.map_congr (withDensity_absolutelyContinuous μ (density t₀) h_point)
  rw [LeGramFibre, h_law]
  exact .of_coordinates (ψ := tuple) (w := density) (by fun_prop) (by fun_prop) (by fun_prop)
    Filter.univ_mem (fun t _ ↦ h_fibre t) h_cont h_le

/-- The mean value inequality. For measurable `f ≥ 0` on `G₁`, the integral of `f (s' γ_Z s)` over
`s, s'` in the fixer `R°` of the frame and `Z` in the open cell, with density `c 𝗀(Z) ^ (k - 1)`, is
at most the integral of `f` over `G₁` for Haar measure. Here `γ_Z = New.RealPlace.gramSection Z` is
the element with the matrix `Z` of products of the frame `e` with `γ_Z e`, `k = |κ|`,
`r = k + 2 ϱ + 1`, `c = New.Shape.openCellConst` is `vol U(k) / vol U(r)` times the area of the unit
sphere in `ℂ ^ k`, and `𝗀 = New.RealPlace.gramDiscReal` is `|det Z|²` less the squared absolute
value of the leading minor of order `ϱ`. -/
theorem lintegral_gramSection_le {f : 𝔰.G₁ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ Z : 𝔰.FrameMatrix in 𝔰.openCell,
        ENNReal.ofReal (𝔰.openCellConst * gramDiscReal Z ^ (𝔰.k - 1)) *
          ∫⁻ s' : 𝔰.G₁, ∫⁻ s : 𝔰.G₁, f (s' * gramSection Z * s) ∂fixerHaar 𝔰 ∂fixerHaar 𝔰 ≤
      ∫⁻ γ : 𝔰.G₁, f γ := by
  -- The image of `gramSectionMeasure 𝔰` is at most the fibre measure on frames, so its
  -- convolution with `fixerHaar 𝔰` is at most `ratio` times Haar measure.
  let ratio : ℝ := volU 𝔰.r / volU 𝔰.k / 2 ^ (𝔰.ϱ + 1)
  have h_volU_r_pos : 0 < volU 𝔰.r := volU_pos 𝔰.r
  have h_volU_k_pos : 0 < volU 𝔰.k := volU_pos 𝔰.k
  have h_ratio_pos : 0 < ratio := by positivity
  have h_const (Z : 𝔰.FrameMatrix) : ratio * (𝔰.openCellConst * gramDiscReal Z ^ (𝔰.k - 1)) =
      sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal Z ^ (𝔰.k - 1) := by
    simp only [ratio, openCellConst]
    field
  rw [← ENNReal.mul_le_mul_iff_right (ofReal_pos.2 h_ratio_pos).ne' ofReal_ne_top]
  calc
    _ = ∫⁻ Z in 𝔰.openCell,
          ENNReal.ofReal (sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal Z ^ (𝔰.k - 1)) *
            ∫⁻ s', ∫⁻ s, f (s' * gramSection Z * s) ∂fixerHaar 𝔰 ∂fixerHaar 𝔰 := by
      rw [← lintegral_const_mul _ (by fun_prop)]
      simp only [← mul_assoc, ← ENNReal.ofReal_mul h_ratio_pos.le, h_const]
    _ = ∫⁻ g, ∫⁻ s, f (g * s) ∂fixerHaar 𝔰 ∂gramSectionMeasure 𝔰 := by
      rw [gramSectionMeasure, lintegral_map (by fun_prop) (by fun_prop),
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
        lintegral_prod _ (by fun_prop)]
      exact lintegral_congr fun Z ↦ (lintegral_const_mul _ (by fun_prop)).symm
    _ = ∫⁻ γ, f γ ∂gramSectionMeasure 𝔰 ∗ₘ fixerHaar 𝔰 := (lintegral_mconv hf).symm
    _ ≤ ENNReal.ofReal ratio * ∫⁻ γ, f γ := by
      grw [leGramFibre_gramSectionMeasure.mconv_fixerHaar_le, lintegral_smul_measure, smul_eq_mul]

end New.RealPlace

end
