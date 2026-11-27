import Lib.General.Groups.IndexOfProduct
import New.Spanning.Unfolding.FrameMass
import New.Spanning.Unfolding.PoincareSeries
import New.Spanning.Unfolding.ReducedGroups
import New.UpperBound.Seesaw.EdgePairEvaluation
import New.UpperBound.Size.ShortColumns

/-!
# Filling data for admissible data: fit to Y₀, Bessel bounds, standing hypotheses

For admissible data `D`, the file shows that the filling data `New.Data.filling` fit the space `Y₀`.
It also shows that they satisfy the standing hypotheses `New.Filling.IsAdmissible`, so that the
general filling theorem applies.

## Main definitions and results

* `New.Data.filling_fits`: the filling data `New.Data.filling` fit the space `Y₀`
  (`New.Filling.Fits`).
* `New.Data.sourceFormCoords`: source forms in coordinates, indexed by pairs (class, Bessel
  coordinate).
* `New.Data.goodProjTranslate`: the map from forms of level `M` on `Y₀` to the image of the good
  idempotent `New.Data.e₀`. It is a translation followed by this idempotent, scaled by the order of
  the finite group `𝖦`.
* `New.Data.card_besselSystem_le_pow`, `New.Data.card_besselCoord_le_pow`: the Bessel system at one
  place has at most `b ^ (2 k)` coordinates, and their tensor product at most `b ^ (2 k f)`.
* `New.Data.log_filling_besselDegree_mem_Icc`: two-sided bounds for the logarithm of the degree of
  the Bessel systems.
* `New.Data.card_mul_card_classes_mul_prod_le`, `New.Data.card_sq_mul_mass_mul_prod_le`: two
  products built from group orders, class number, masses, dimensions and degrees are at most
  `(1 + b⁻⁹)` times `New.Filling.mainSecondMoment`. `New.Data.card_mul_prod_frameMass_le` states
  both.

Notions from other files:
* `New.Data.spaceY`: for an index `j`, the hermitian space `Y_j` with its adelic frame, hence its
  lattice `𝖬_j`, chosen as in `New.Data.exists_space_isStd_of_le_and_gram_eq_of_lt`. Only `j = 0`
  occurs in this file.
* `New.Data.chosenGL`: The finite group 𝖦 = ∏ GL_r(𝔽_w), over the chosen places w above p₀ and p₁.
* `New.Data.targetParameter`: The entry i (from 0) of the target parameter at v: k/2 − 1 − i for
  i < k − 1, and Δ/2 − w_{i+2−k}(v) otherwise, where Δ/2 = `D.halfGap` and
  w_j(v) = `D.liftWeight j v`.
* `New.Filling.besselDegree`: The product over infinite places of the degrees of the Bessel systems.
* `New.Data.logLevelTarget`: a number `λ`, built from the mean of the `log (D.weight v)`, from
  `log (M rootDisc / 2π)` and from `log b`, with `λ ≤ log N ≤ λ + √(log b)`.
-/

noncomputable section

/-! ## Fit to Y₀, source forms in coordinates and the projection to target forms -/

namespace New.Data

open Matrix Shape Unitary Units

variable {P : Parameters} (D : Data P)

/-- The filling data of D fit the hermitian space Y₀ = `D.spaceY 0` in the sense of
`New.Filling.Fits`. -/
lemma filling_fits :
    D.filling.Fits (D.spaceY 0) D.paramW D.columnCount (D.gradingY 0)
      (scalarFin D.shape.κ (D.latticeScale 0))⁻¹ := by
  -- The finite frame of `Y₀` is `gradedLatticeBasis` times an integral `γ` that is `≡ 1` at the
  -- chosen places, by the choice of `D.spaceY`.
  obtain ⟨γ, hγ_red, (hγ : (D.spaceY 0).xFin.1 =
      gradedLatticeBasis D.shape.besselIndexEquiv D.ideleA D.piNIdele (D.latticeScale 0) *
        γ.1.1)⟩ :=
    D.exists_spaceY_xFin_eq 0 D.nat_le_of_hasLogBound
  -- `gradedLatticeBasis` scales only the string by `u = D.latticeScale 0`. So it is the lattice
  -- basis of the filling data scaled by `u` on the whole space and then by `u⁻¹` on `X₀`.
  have h_lat :
      gradedLatticeBasis D.shape.besselIndexEquiv D.ideleA D.piNIdele (D.latticeScale 0) =
        (Unitary.toUnits (D.latticeScale 0) •
            (toBesselH D.shape (D.N : 𝔸f D.E) (scalarFin D.shape.κ (D.latticeScale 0))⁻¹).1 *
          D.filling.latticeBasis).1 := by
    let u : 𝔸f D.E := (D.latticeScale 0).1
    -- `u⁻¹ = star u` multiplies only the `X₀` rows of the lattice basis.
    have h_prod :
        (toBesselH D.shape (D.N : 𝔸f D.E) (scalarFin D.shape.κ (D.latticeScale 0))⁻¹).1.1 *
            D.filling.latticeBasis.1 =
          fromBlocks 1 0 0 (fromBlocks
            (fromBlocks (star u • Filling.scaleAt (star D.piNIdele⁻¹.1) D.shape.k₀) 0
              (of fun (_ : Unit) (j : D.shape.κ) ↦
                if j = D.shape.k₀ then (D.piNIdele * star D.piNIdele)⁻¹.1 else 0) 1)
            0 0 1) := by
      have h_embed (a : Gf D.E D.shape.κ) : (toBesselH D.shape (D.N : 𝔸f D.E) a).1.1 =
          fromBlocks 1 0 0 (fromBlocks (fromBlocks a.1.1 0 0 1) 0 0 1) := rfl
      rw [h_embed, ← map_inv]
      simp [u, filling, besselLatticeBasis, fromBlocks_multiply, scalarFin,
        ← Unitary.star_eq_inv, smul_eq_diagonal_mul]
    have h_unit (c : 𝔸f D.E) : u * (star u * c) = c := by simp [u, ← mul_assoc]
    rw [Units.val_mul, Units.val_smul, smul_mul_assoc, h_prod]
    -- Compare the entries: equal indices give the scalars, by `h_unit`. Otherwise both are 0, as
    -- the string indices `a`, `ϱ`, `2 ϱ - b` for `a, b < ϱ` are different.
    simp [u, h_unit, ← ext_iff, besselIndexEquiv, gradedLatticeBasis, diagonal_apply, smul_def,
      fromBlocks_smul, Matrix.one_apply, Fin.ext_iff, Fin.val_rev]
    and_intros <;> grind
  rw [h_lat] at hγ
  exact
    { isDiscreteSeriesBessel := D.isDiscreteSeriesBessel_filling_besselSystem
      index_eq := rfl
      isIdempotentKernel := D.isCuspKernel_typeKernel_paramW.1
      exists_point_eq := ⟨γ, fun i w ↦ hγ_red ⟨i, w⟩, toUnits (D.latticeScale 0), ext hγ⟩
      central a := (Seesaw.commute_scalarFin a).inv_left }

/-- A finite adelic point of U(X₀) preserves the lattice of Y₀ if and only if it is integral and
its last row is that of 1 modulo π. In the coordinates of the filling data this is
`New.Filling.inclHFin_mem_latticeStabilizer_iff`. -/
lemma inclXFin_zero_mem_stdLevel_iff {a : Gf D.E (D.X 0)} :
    (D.gradingY 0).inclXFin a ∈ stdLevel D.E (D.Y 0) ↔
      a.val ∈ congruenceGL (Ô D.E ∙ D.piNIdele.val) Sum.inr :=
  -- Both sides say that `D.filling.inclHFin a` lies in `D.filling.latticeStabilizer`.
  (D.filling_fits.inclXFin_mem_stdLevel_iff a).trans D.filling.inclHFin_mem_latticeStabilizer_iff

/-- The finite adelic points of U(X₀) that lie in the principal level of Y₀ at the chosen places
form the level `New.Data.levelX` of X₀. In the coordinates of the filling data this is
`New.Data.levelX_zero_eq_comap`. -/
lemma comap_inclXFin_zero_chosenLevel :
    (D.chosenLevel (n := D.Y 0)).comap (D.gradingY 0).inclXFin = D.levelX 0 := by
  ext a
  rw [levelX_zero_eq_comap]
  -- `D.chosenLevel` is the standard principal level of the filling data.
  exact D.filling_fits.inclXFin_mem_stdPrincipalLevel_iff a

/-- The isomorphism that applies the central translation by `D.latticeScale 0` to a source form on
X₀ and takes its values at the class representatives, in the coordinates of the Bessel systems. -/
def sourceFormCoords :
    ↥D.SourceForm ≃ₗ[ℂ] EuclideanSpace ℂ (D.filling.Classes × D.filling.BesselCoord) :=
  LinearEquiv.ofBijective (D.centralRep (D.latticeScale 0))
    (D.centralRep.apply_bijective (D.latticeScale 0)) ≪≫ₗ D.filling_fits.sourceFormCoords

/-- For s in 𝖦, the linear map from forms of parameter ς and level M on Y₀ to the image of the good
idempotent e₀. It is the translation by s, followed by |𝖦| times the action of e₀. -/
abbrev goodProjTranslate (s : D.chosenGL) :
    ↥(D.principalForms (D.spaceY 0)) →ₗ[ℂ]
      LinearMap.range ((D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀) :=
  (Nat.card D.chosenGL : ℂ) •
    ((D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀).rangeRestrict ∘ₗ D.principalRep (D.spaceY 0) s

end New.Data

/-!
## Bessel systems: number of coordinates, target parameter and degree

`New.Data.targetParameter v i` is numbered from 0, and `f` is the number of infinite places.
-/

section DegreeBounds

open Nat Finset Real

namespace New.Data

variable {P : Parameters} (D : Data P)

/-- At each infinite place `v`, the Bessel system of `D` has at most `(k + a) ^ k` coordinates, `k`
the rank of `X₀`. Their number is the dimension of the representation of `U(X₀)` at `v`, which is
that of a symmetric power of degree at most `a = D.a` of a space of dimension `k`. -/
lemma card_besselSystem_le_add_pow (v : D.Φ) :
    Fintype.card (D.filling.besselSystem v).Index ≤ (D.k + D.a) ^ D.k := by
  -- The coordinates correspond to a basis of the Schur module of weight `D.columnCount v` (`A`,
  -- `A'` are inverse matrices); this weight has no columns of height `2, …, k - 1`, so the basis is
  -- in bijection `e` with the monomials of degree `D.columnCount v 1` in the variables `D.X 0`.
  obtain ⟨A, A', hAA', hA'A, -⟩ := (D.filling_fits.isDiscreteSeriesBessel
    v).exists_conj_rep_eq_schur
  have h_degree : D.columnCount v 1 ≤ D.a := by by_cases hv : v ∈ D.aPlaces <;>
                                                  simp [columnCount, hv]
  have one_lt_k : 1 < D.k := D.nat_le_of_hasLogBound
  have h_row (i : ℕ) (_ : 0 < i) (hi_lt : i < Fintype.card (D.X 0)) :
      D.columnCount v i = if i = 1 then D.columnCount v 1 else 0 := by
    rw [D.card_X₀] at hi_lt
    by_cases hi_one : i = 1 <;> simp [columnCount, hi_one, hi_lt.ne, hi_lt.not_gt]
  obtain ⟨(e : WeylIndexFamily (fun _ ↦ D.X 0) (fun _ ↦ D.columnCount v) ≃ Monomials (D.X 0)
    (D.columnCount v 1)), -⟩ :=
    exists_equiv_schur_one_row_eq_symPowMatrix (.refl (D.X 0)) (one_lt_k.trans_eq D.card_X₀.symm)
      h_row
  -- There are `choose (k + a' - 1) a'` monomials of degree `a' ≤ a` in `k` variables.
  calc Fintype.card (D.filling.besselSystem v).Index
    _ = #((univ : Finset (D.X 0)).finsuppAntidiag (D.columnCount v 1)) := by
      rw [A'.square_of_invertible A hA'A hAA', ← card_eq_of_equiv_fintype e.symm]
    _ = (D.k + D.columnCount v 1 - 1).choose (D.columnCount v 1) := by
      rw [card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, D.card_X₀]
    _ ≤ (D.k + D.columnCount v 1).choose D.k := by grw [sub_le, choose_symm_add]
    _ ≤ (D.k + D.a) ^ D.k := by grw [choose_le_pow, h_degree]

/-- At each infinite place `v`, the number of coordinates of the Bessel system of `D`, that is the
dimension of the representation of `U(X₀)` at `v`, is at most `b ^ (2 k)`, `k` the rank of `X₀`. -/
lemma card_besselSystem_le_pow (v : D.Φ) :
    (Fintype.card (D.filling.besselSystem v).Index : ℝ) ≤ D.b ^ (2 * D.k) := by
  calc (Fintype.card (D.filling.besselSystem v).Index : ℝ)
    _ ≤ (D.k + D.a : ℝ) ^ D.k := mod_cast D.card_besselSystem_le_add_pow v
    _ ≤ (D.b ^ 2) ^ D.k := pow_le_pow_left₀ (by positivity) D.le_of_hasLogBound _
    _ = D.b ^ (2 * D.k) := (pow_mul _ _ _).symm

/-- The tensor product of the Bessel systems of `D` over the `f` infinite places has at most
`b ^ (2 k f)` coordinates, `k` the rank of `X₀`. -/
lemma card_besselCoord_le_pow :
    (Fintype.card D.filling.BesselCoord : ℝ) ≤ D.b ^ (2 * D.k * D.f) := by
  rw [Fintype.card_pi, Nat.cast_prod]
  calc
    _ ≤ ∏ _v : D.Φ, D.b ^ (2 * D.k) := by
      gcongr with v
      exact D.card_besselSystem_le_pow v
    _ = D.b ^ (2 * D.k * D.f) := by rw [prod_const, Finset.card_univ, ← pow_mul]

/-- For admissible data `D`, let `d` be the number of coordinates of the tensor product of the
Bessel systems, `k` the rank of `X₀`, `f` the number of infinite places and `b = D.b` the weight at
the `b`-places. Then `d ((k - 1)!)^f ≤ (b^{5/4})^{k f}`, where `b^{5/4}` is written `(√√b)^5`. -/
lemma card_besselCoord_mul_factorial_le :
    (Fintype.card D.filling.BesselCoord * (D.k - 1)! ^ D.f : ℝ) ≤ ((√√D.b ^ 5) ^ D.k) ^ D.f := by
  -- Multiply `card_besselSystem_le_add_pow` over the `f` places, with `(k - 1)! ≤ k ^ k` and
  -- `(k + a) * k ≤ √√b ^ 5`.
  have h_coords : Fintype.card D.filling.BesselCoord ≤ ((D.k + D.a) ^ D.k) ^ D.f := by
    simpa [Fintype.card_pi] using prod_le_pow_card univ _ _ fun v _ ↦
      D.card_besselSystem_le_add_pow v
  have h_factorial : (D.k - 1)! ≤ D.k ^ D.k := by grw [sub_le, factorial_le_pow]
  have h_size : (D.k + D.a : ℝ) * D.k ≤ √√D.b ^ 5 := D.le_of_hasLogBound
  calc
    _ ≤ ((D.k + D.a : ℝ) ^ D.k) ^ D.f * ((D.k : ℝ) ^ D.k) ^ D.f := by
      exact_mod_cast Nat.mul_le_mul h_coords (Nat.pow_le_pow_left h_factorial D.f)
    _ = (((D.k + D.a : ℝ) * D.k) ^ D.k) ^ D.f := by simp [mul_pow]
    _ ≤ ((√√D.b ^ 5) ^ D.k) ^ D.f := by gcongr

/-- For `i < l` and an infinite place `v`, the difference
`D.targetParameter v i - D.targetParameter v l` of entries of the target parameter lies between `1`
and the lift weight `D.liftWeight (l + 2 - D.k) v`. Here `k = D.k` is the rank of the source, and
`l + 2 - D.k` is truncated subtraction of natural numbers. -/
lemma targetParameter_sub_mem_Icc (v : D.Φ) {i l : ℕ} (hil : i < l) :
    (D.targetParameter v i - D.targetParameter v l : ℝ) ∈ Set.Icc 1
      ↑(D.liftWeight (l + 2 - D.k) v) := by
  -- `1 ≤`: the integers `D.targetParameter v i` strictly decrease. `≤ w`: unfold `targetParameter`;
  -- the entries numbered below `k - 1` are small, the others are `D.halfGap - w`.
  have h_anti : D.targetParameter v l < D.targetParameter v i := D.targetParameter_strictAnti v hil
  rw [Set.mem_Icc]
  norm_cast
  grind [targetParameter_eq]

/-- The degree `D.filling.besselDegree` of the Bessel systems of `D` is the exponential of the sum,
over the infinite places `v` and over `k - 1 ≤ l < r`, of `∑_{i<l} log (ς_i - ς_l) - log l!`. Here
`ς = D.targetParameter v` is the sequence of `r = D.r` entries from which the Harish-Chandra
parameters at `v` are read off, and `k = D.k`. -/
lemma filling_besselDegree_eq_exp_sum :
    D.filling.besselDegree = exp (∑ v : D.Φ, ∑ l ∈ Ico (D.k - 1) D.r,
      (∑ i ∈ range l, log (D.targetParameter v i - D.targetParameter v l) - Real.log l !)) := by
  push_cast [Filling.besselDegree, (D.filling_fits.isDiscreteSeriesBessel _).deg_eq, ↓card_rowIndex,
    exp_sum,
    exp_sub, weylDimensionPoly, ↓paramW_lt_iff, paramW]
  congr! with v
  -- Index the pairs by their numbers under `basisNumber`.
  suffices h_ranges : ∏ l ∈ range D.r, (∏ i ∈ range (min D.r l),
        (2 * (D.targetParameter v i : ℝ) - 2 * D.targetParameter v l) / 2) / l ! =
      ∏ l ∈ Ico (D.k - 1) D.r,
        (∏ i ∈ range l, exp (log (D.targetParameter v i - D.targetParameter v l : ℝ))) /
          exp (log (l ! : ℝ)) by
    simpa [prod_comm, prod_filter, reindex_equiv D.basisNumber.symm, prod_fin_eq_prod_range,
      ← mem_range, ← prod_div_distrib] using h_ranges
  apply prod_congr_of_eq_on_inter
  · -- `l < k - 1`: the differences are `l - i`, with product `l!`.
    intro l hl hl'
    field_simp
    norm_cast
    have h_diff (i : ℕ) (hi : i ∈ range l) :
        D.targetParameter v i - D.targetParameter v l = (l - 1 - i : ℕ) + 1 := by
          grind [targetParameter_eq]
    simp [min_eq_right (mem_range.1 hl).le, prod_congr rfl h_diff,
      prod_range_reflect (fun i : ℕ ↦ (i : ℤ) + 1), ← prod_range_add_one_eq_factorial]
  · exact fun l hl hl' ↦ absurd (mem_range.2 (mem_Ico.1 hl).2) hl' -- the left range is larger
  · -- `k - 1 ≤ l < r`: the numbers under `log` are positive by `targetParameter_sub_mem_Icc`.
    intro l hl _
    rw [min_eq_right (mem_range.1 hl).le, exp_log (mod_cast l.factorial_pos)]
    refine congrArg (· / (l ! : ℝ)) (prod_congr rfl fun i hi ↦ ?_)
    rw [exp_log (one_pos.trans_le (D.targetParameter_sub_mem_Icc v (mem_range.1 hi)).1)]
    ring

/-- The logarithm of the degree of the Bessel systems of `D`, plus `f` times the sum of `log l!`
over `k − 1 ≤ l < r`, lies between `∑_v m (k − 1) log W_v` and `∑_v m r (log W_v + 1/x)`. Here `v`
runs over the `f` infinite places, `k` is the rank of `X₀`, `r` is the number of entries of the
target parameter, `m = r - k + 1`, `x` is the parameter `D.x` of the data and `W_v` is
`D.weight v`. -/
lemma log_filling_besselDegree_mem_Icc :
    Real.log D.filling.besselDegree + D.f * ∑ l ∈ Ico (D.k - 1) D.r, Real.log l ! ∈ Set.Icc
      (∑ v : D.Φ, D.m * ((D.k - 1) * Real.log (D.weight v)))
      (∑ v : D.Φ, D.m * (D.r * (Real.log (D.weight v) + D.x⁻¹))) := by
  -- After inserting the formula for the degree the factorials cancel; it remains to bound, for each
  -- `l`, the sum of `log (ς_i - ς_l)` over `i < l`.
  have deg_eq : D.filling.besselDegree = exp (∑ v, ∑ l ∈ Ico (D.k - 1) D.r,
      (∑ i ∈ range l, log (D.targetParameter v i - D.targetParameter v l) - Real.log l !)) :=
    D.filling_besselDegree_eq_exp_sum
  have h_low (v : D.Φ) (l : ℕ) (hl : l ∈ Ico (D.k - 1) D.r) : (D.k - 1) * Real.log (D.weight v) ≤
      ∑ i ∈ range l, log (D.targetParameter v i - D.targetParameter v l) := by
    -- Keep only the terms `i < k - 1`; each of these differences is at least `weight v`.
    have h_diff (i : ℕ) (hi : i ∈ range (D.k - 1)) :
        (D.weight v : ℝ) ≤ D.targetParameter v i - D.targetParameter v l :=
      (D.weight_le_liftWeight_sub 0 v).trans (by norm_cast; grind [targetParameter_eq])
    calc
      _ ≤ ∑ i ∈ range (D.k - 1), log (D.targetParameter v i - D.targetParameter v l) := by
        simpa using sum_le_sum fun i hi ↦ log_le_log (HasLogBound.pos D) (h_diff i hi)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (mem_Ico.1 hl).1) fun i hi _ ↦
        log_nonneg (D.targetParameter_sub_mem_Icc v (mem_range.1 hi)).1
  have h_up (v : D.Φ) (l : ℕ) (hl : l ∈ Ico (D.k - 1) D.r) :
      ∑ i ∈ range l, log (D.targetParameter v i - D.targetParameter v l) ≤
        D.r * (Real.log (D.weight v) + D.x⁻¹) := by
    -- Each of the `l < r` differences is at most `liftWeight (l + 2 - k) v` by
    -- `targetParameter_sub_mem_Icc`.
    calc
      _ ≤ ∑ i ∈ range l, Real.log (D.liftWeight (l + 2 - D.k) v) := sum_le_sum fun i hi ↦ by
        obtain ⟨h_one_le, h_le_w⟩ := D.targetParameter_sub_mem_Icc v (mem_range.1 hi)
        exact log_le_log (one_pos.trans_le h_one_le) h_le_w
      _ = l * Real.log (D.liftWeight (l + 2 - D.k) v) := by simp
      _ ≤ D.r * (Real.log (D.weight v) + D.x⁻¹) := by
        grw [(mem_Ico.1 hl).2, D.log_liftWeight_le (by grind)]
  -- Sum both bounds over `v` and over the `m` values of `l`.
  have h_card : D.r - (D.k - 1) = D.m := by grind
  constructor
  · simpa [deg_eq, h_card] using sum_le_sum (s := univ) fun (v : D.Φ) _ ↦ sum_le_sum (h_low v)
  · simpa [deg_eq, h_card] using sum_le_sum (s := univ) fun (v : D.Φ) _ ↦ sum_le_sum (h_up v)

end New.Data

end DegreeBounds

/-!
## Number of classes, mean values and the standing hypotheses

The ratio of the main second moment to the second moment of the Bessel group is computed exactly
(`New.Data.mainSecondMoment_div_identitySecondMoment_eq`). The sizes of the degree, of the ratio of
the masses and of `N` then give the range of this ratio
(`New.Data.mainSecondMoment_div_identitySecondMoment_mem_Icc`).
-/

namespace New.Data

open Finset Real Filling Subgroup MulAction Fintype Shape NeZero NumberField

variable {P : Parameters} (D : Data P)

/-- The finite points of `U(X₀)` that `New.Filling.inclHFin` sends into the integral group
`New.Filling.latticeStabilizer` have index `(N^k - 1)^f` in the group `New.stdLevel` of integral
points, `N` being the prime level, `k` the rank of `X₀` and `f` the number of infinite places. -/
lemma relIndex_latticeStabilizer :
    (D.filling.latticeStabilizer.comap D.filling.inclHFin).relIndex (stdLevel D.E D.shape.κ) =
      (D.N ^ D.k - 1 : ℝ) ^ D.f := by
  -- An integral x lies in this preimage iff its row `k₀` is the unit vector modulo every place
  -- of `D.piNPlaces`; each such stabiliser has index N ^ k - 1, and there are f places.
  -- `H w` fixes the unit vector under the inverse transpose: row `k₀` is the unit vector.
  let H (w : D.piNPlaces) : Subgroup (GL (D.X 0) (ResField w.1)) :=
    (stabilizer _ (Pi.single D.shape.k₀ 1 : D.X 0 → ResField w.1)).comap invTransposeGL.toMonoidHom
  have h_level :
      D.filling.latticeStabilizer.comap D.filling.inclHFin = levelOf Subtype.val (pi ⊤ H) := by
    ext x
    rw [Subgroup.mem_comap, mem_levelOf, D.filling.inclHFin_mem_latticeStabilizer_iff]
    -- Both sides say that `x` is integral, with a condition on its row `k₀`.
    change (x.1 ∈ intGL D.shape.κ (Ô D.E) ∧ ∀ (_ : Unit) (j : D.shape.κ),
      (x.1.1 - 1) D.shape.k₀ j ∈ Ô D.E ∙ D.piNIdele.val) ↔ _
    refine exists_prop.symm.trans (exists_congr fun hx : x.1 ∈ intGL D.shape.κ (Ô D.E) ↦ ?_)
    -- π divides an integral adele iff it reduces to zero at every place of `D.piNPlaces`, and `H w`
    -- says that the entries `r j` of row `k₀` of `x - 1` reduce to zero at `w`.
    let r (j : D.shape.κ) : Ô D.E :=
      ⟨x.1.1 D.shape.k₀ j, hx.isIntMatrix D.shape.k₀ j⟩ - if j = D.shape.k₀ then 1 else 0
    have h_mem (j : D.shape.κ) : (x.1.1 - 1) D.shape.k₀ j ∈ Ô D.E ∙ D.piNIdele.val ↔
        algebraMap (RingOfIntegers D.E) (Ô D.E) D.piN ∣ r j := by
      by_cases hj : j = D.shape.k₀ <;>
        simp [hj, Ne.symm, r, Submodule.mem_span_singleton, dvd_def, Subtype.ext_iff,
          Subring.smul_def, piNIdele, mul_comm, eq_comm]
    have h_fix (w : D.piNPlaces) : stdLevel.reduceFamily Subtype.val ⟨x, hx⟩ w ∈ H w ↔
        ∀ j : D.shape.κ, reduceAt w.1 (r j) = 0 := by
      -- The inverse transpose fixes the unit vector iff row `k₀` of the reduction is that vector.
      have h_mem_H (M : GL (D.X 0) (ResField w.1)) : M ∈ H w ↔
          (transposeGL M)⁻¹ ∈ stabilizer _ (Pi.single D.shape.k₀ 1 : D.X 0 → ResField w.1) := .rfl
      rw [h_mem_H]
      have h_entry (j : D.shape.κ) : (stdLevel.reduceFamily Subtype.val ⟨x, hx⟩ w).1 D.shape.k₀ j =
          reduceAt w.1 ⟨x.1.1 D.shape.k₀ j, hx.isIntMatrix D.shape.k₀ j⟩ := rfl
      simp [r, h_entry, funext_iff, Units.smul_def, -reduceAt_eq_zero, sub_eq_zero]
    simp only [Subgroup.mem_pi, h_mem, dvd_iff_reduceAt_eq_zero D.intValuation_piN, h_fix,
      forall_const, ← mem_piNPlaces]
    exact ⟨fun h w _ j ↦ h j w.1 w.2, fun h j w hw ↦ h ⟨w, hw⟩ trivial j⟩
  -- The index of a preimage under reduction is the product of the indices of the stabilisers.
  rw [h_level, relIndex_levelOf (h := ⟨by simp, by simp [D.isSplitLevel_piNPlaces.star_notMem]⟩)]
  simp [Seesaw.index_pi_univ, H, index_comap, index_stabilizer_GL_vector, card_ResField,
    D.isSplitLevel_piNPlaces.q_eq, ↓card_X₀, Fin.pos', card_piNPlaces]

/-- The number of classes of level `New.Data.levelX 0` on `U(X₀)` is `|H̄| (N^k - 1)^f` times
the mass `New.mass` in rank `k`, where `H̄` is the image (`New.Filling.reducedImage`) under
reduction of the integral points of `H = besselH`, the copy of `U(X₀)` in the unitary group, `N` is
the prime level and `f` is the number of infinite places. -/
lemma card_classes_eq_card_mul_pow_mul_mass :
    (Fintype.card D.filling.Classes : ℝ) =
      Nat.card (D.filling.reducedImage besselH) * (D.N ^ D.k - 1) ^ D.f * mass D.E D.k := by
  -- The classes have trivial automorphism groups, so their number is the index of `D.levelX 0`
  -- in `stdLevel` times the mass; the index splits along
  -- `D.levelX 0 ≤ (preimage of latticeStabilizer) ≤ stdLevel`.
  have h_card : (card D.filling.Classes : ℝ) =
      (D.levelX 0).relIndex (stdLevel D.E D.shape.κ) * mass D.E D.k := by
    erw [card_eq_nat_card, card_classes_eq_classSum D.classAut_levelX_zero_eq_bot,
      classSum_one_of_le IsLevel.le, classSum_stdRatPoints_eq_mass, card_X₀]
  -- `D.levelX 0` is the preimage of the principal congruence subgroup.
  have relIndex_levelX_eq_card_image :
      (D.levelX 0).relIndex (D.filling.latticeStabilizer.comap D.filling.inclHFin) =
        Nat.card (D.filling.reducedImage besselH) := by
    rw [levelX_zero_eq_comap]
    exact D.filling.relIndex_comap_principalLevel
  rw [h_card, ← relIndex_mul_relIndex _ _ _
    (D.levelX_zero_eq_comap.trans_le (comap_mono (map_subtype_le _)))
    fun x hx ↦ (D.filling.inclHFin_mem_latticeStabilizer_iff.1 hx).1, relIndex_levelX_eq_card_image]
  simp [D.relIndex_latticeStabilizer]

/-- With `fr_v` the frame mass, and `d_v`, `deg_v` the dimension and the degree of the Bessel system
at `v`, the product of the `fr_v d_v ^ 2 / deg_v` is `(∏ fr_v) d ^ 2 / deg`, where `d` and `deg` are
the dimension and the degree of the tensor product of the Bessel systems. -/
lemma prod_frameMass_mul_div_eq :
    ∏ v : D.Φ, D.frameMass v * Fintype.card (D.filling.besselSystem v).Index ^ 2 /
        (D.filling.besselSystem v).deg =
      (∏ v : D.Φ, D.frameMass v) * Fintype.card D.filling.BesselCoord ^ 2 /
        D.filling.besselDegree := by
  rw [prod_div_distrib, prod_mul_distrib, prod_pow, Fintype.card_pi, Nat.cast_prod, besselDegree]

/-- At an infinite place `v`, let `fr_v` be the frame mass, `sph_k` the mass of the unit sphere in
the rank `k` of `X₀`, `d_v` and `deg_v` the number of coordinates and the degree of the Bessel
system, and `c_v = fr_v N ^ k d_v ^ 2 / (sph_k deg_v)`, with `N` the prime level. The product of
the `sph_k c_v` over the `f` infinite places is `N ^ (k f) (∏ fr_v) d ^ 2 / deg`, where
`d = ∏ d_v` and `deg = ∏ deg_v`: the masses `sph_k` cancel. -/
lemma prod_unitSphereMass_mul_div_eq :
    ∏ v : D.Φ, D.unitSphereMass D.k v * (D.frameMass v * D.N ^ D.k *
        Fintype.card (D.filling.besselSystem v).Index ^ 2 /
          (D.unitSphereMass D.k v * (D.filling.besselSystem v).deg)) =
      (D.N ^ D.k) ^ D.f * ((∏ v : D.Φ, D.frameMass v) * Fintype.card D.filling.BesselCoord ^ 2 /
        D.filling.besselDegree) := by
  have h_const : ((D.N : ℝ) ^ D.k) ^ D.f = ∏ _v : D.Φ, (D.N : ℝ) ^ D.k := by simp
  rw [← D.prod_frameMass_mul_div_eq, h_const, ← prod_mul_distrib]
  congr! 1 with v
  field_simp [(D.unitSphereMass_pos D.k v).ne']

/-- The main second moment of the filling data is
`(|H̄| (N ^ k - 1) ^ f mass_k d) ^ 2 / (deg mass_r)`, where `H̄` is the reduced image of `besselH`,
`mass_l` is `New.mass` in rank `l`, and `d`, `deg` are the dimension and the degree of the tensor
product of the Bessel systems. -/
lemma filling_mainSecondMoment_eq :
    D.filling.mainSecondMoment =
      (Nat.card (D.filling.reducedImage besselH) * (D.N ^ D.k - 1) ^ D.f * mass D.E D.k *
        Fintype.card D.filling.BesselCoord) ^ 2 / (D.filling.besselDegree * mass D.E D.r) := by
  rw [mainSecondMoment, sourceDim, Nat.cast_mul, card_classes_eq_card_mul_pow_mul_mass, Shape.r,
    D.card_rowIndex]

/-- Since the prime level `N` is at least `2`, the number `N ^ k - 1` is positive. -/
lemma pow_sub_one_pos : (0 : ℝ) < D.N ^ D.k - 1 :=
  sub_pos.mpr (one_lt_pow₀ (mod_cast D.N_prime.one_lt) D.k_pos.ne')

/-- For the filling data of admissible data `D`, let `H̄` be the reduced image of `besselH`, `d_v`
and `deg_v` the dimension and the degree of the Bessel system at `v`, `fr_v` the frame mass, `sph_k`
the mass of the sphere in rank `k`, `mass_l` the mass `New.mass` in rank `l` and
`c_v = fr_v N ^ k d_v ^ 2 / (sph_k deg_v)`. Then `|H̄| ^ 2 mass_k ∏ sph_k c_v` is at most
`(1 + b⁻⁹)` times the main second moment `(n_X ∏ d_v) ^ 2 / (mass_r ∏ deg_v)`. Here `n_X` is the
number of classes, `k`, `r` are the ranks of `X₀`, `Y₀`, and `b = D.b` is the weight at the
`b`-places. -/
theorem card_sq_mul_mass_mul_prod_le :
    Nat.card (D.filling.reducedImage besselH) ^ 2 * mass D.E D.k *
        ∏ v : D.Φ, D.unitSphereMass D.k v * (D.frameMass v * D.N ^ D.k *
          Fintype.card (D.filling.besselSystem v).Index ^ 2 /
            (D.unitSphereMass D.k v * (D.filling.besselSystem v).deg)) ≤
      (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment := by
  -- The left side is the left side of `prod_frameMass_mul_le` times the number `multiplier`.
  let multiplier : ℝ := D.filling.mainSecondMoment / ((D.N ^ D.k) ^ D.f * mass D.E D.k)
  have N_pos : (0 : ℝ) < D.N := mod_cast D.N_prime.pos
  have deg_pos : 0 < D.filling.besselDegree := D.filling.besselDegree_pos
  have mass_k_pos : 0 < mass D.E D.k := mass_pos D.E D.k
  have mass_r_pos : 0 < mass D.E D.r := mass_pos D.E D.r
  have pred_pos : (0 : ℝ) < D.N ^ D.k - 1 := D.pow_sub_one_pos
  have multiplier_nonneg : 0 ≤ multiplier := by
    simp only [multiplier, filling_mainSecondMoment_eq]
    positivity
  rw [D.prod_unitSphereMass_mul_div_eq]
  calc
    _ = (∏ v : D.Φ, D.frameMass v) * mass D.E D.r * (D.N ^ D.k / (D.N ^ D.k - 1)) ^ (2 * D.f) *
        multiplier := by
      simp only [multiplier, filling_mainSecondMoment_eq, div_pow, mul_comm 2 D.f, pow_mul]
      field_simp
    _ ≤ (1 + D.b⁻¹ ^ 9) * ((D.N ^ D.k) ^ D.f * mass D.E D.k) * multiplier :=
      mul_le_mul_of_nonneg_right D.prod_frameMass_mul_le multiplier_nonneg
    _ = (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment := by
      simp only [multiplier]
      field_simp

/-- For the filling data of admissible data `D`, let `H̄` be the reduced image of `besselH`, `n_X`
the number of classes, `d_v` and `deg_v` the dimension and the degree of the Bessel system at `v`
and `fr_v` the frame mass. Then `|H̄| n_X ∏ fr_v d_v ^ 2 / deg_v` is at most `(1 + b⁻⁹)` times the
main second moment `(n_X ∏ d_v) ^ 2 / (mass_r ∏ deg_v)`. Here `mass_r` is the mass `New.mass` in the
rank `r` of `Y₀`, and `b = D.b` is the weight at the `b`-places. -/
theorem card_mul_card_classes_mul_prod_le :
    Nat.card (D.filling.reducedImage besselH) * Fintype.card D.filling.Classes *
        ∏ v : D.Φ, D.frameMass v * Fintype.card (D.filling.besselSystem v).Index ^ 2 /
          (D.filling.besselSystem v).deg ≤
      (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment := by
  -- With `n_X = |H̄| (N ^ k - 1) ^ f mass_k` the left side is at most the left side of
  -- `card_sq_mul_mass_mul_prod_le`, which has `N ^ k` in place of `N ^ k - 1`.
  let H : ℝ := Nat.card (D.filling.reducedImage besselH)
  let Q : ℝ := (∏ v : D.Φ, D.frameMass v) * Fintype.card D.filling.BesselCoord ^ 2 /
    D.filling.besselDegree
  have frame_pos : 0 < ∏ v : D.Φ, D.frameMass v := prod_pos fun v _ ↦ D.frameMass_pos v
  have deg_pos : 0 < D.filling.besselDegree := D.filling.besselDegree_pos
  have mass_k_pos : 0 < mass D.E D.k := mass_pos D.E D.k
  have pred_pos : (0 : ℝ) < D.N ^ D.k - 1 := D.pow_sub_one_pos
  rw [D.prod_frameMass_mul_div_eq, card_classes_eq_card_mul_pow_mul_mass]
  calc
    _ = H ^ 2 * mass D.E D.k * ((D.N ^ D.k - 1) ^ D.f * Q) := by ring
    _ ≤ H ^ 2 * mass D.E D.k * ((D.N ^ D.k) ^ D.f * Q) := by
      gcongr
      linarith
    _ ≤ (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment := by
      rw [← D.prod_unitSphereMass_mul_div_eq]
      exact D.card_sq_mul_mass_mul_prod_le

/-- **Mean values.** For the filling data of admissible data `D`, let `H̄` be the reduced image of
`besselH`, `n_X` the number of classes, `d_v` and `deg_v` the dimension and the degree of the Bessel
system at `v`, `fr_v` the frame mass, `sph_k` the mass of the unit sphere in rank `k`, `mass_l` the
mass `New.mass` in rank `l` and `c_v = fr_v N ^ k d_v ^ 2 / (sph_k deg_v)`. The numbers
`|H̄| n_X ∏ fr_v d_v ^ 2 / deg_v` and `|H̄| ^ 2 mass_k ∏ sph_k c_v`, which bound mean values, are at
most `(1 + b⁻⁹)` times the main second moment `(n_X ∏ d_v) ^ 2 / (mass_r ∏ deg_v)`. Here `N` is the
prime level, `k`, `r` are the ranks of `X₀`, `Y₀`, and `b = D.b` is the weight at the `b`-places. -/
theorem card_mul_prod_frameMass_le :
    Nat.card (D.filling.reducedImage besselH) * Fintype.card D.filling.Classes *
        ∏ v : D.Φ, D.frameMass v * Fintype.card (D.filling.besselSystem v).Index ^ 2 /
          (D.filling.besselSystem v).deg ≤
      (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment ∧
    Nat.card (D.filling.reducedImage besselH) ^ 2 * mass D.E D.k *
        ∏ v : D.Φ, D.unitSphereMass D.k v * (D.frameMass v * D.N ^ D.k *
          Fintype.card (D.filling.besselSystem v).Index ^ 2 /
            (D.unitSphereMass D.k v * (D.filling.besselSystem v).deg)) ≤
      (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment :=
  ⟨D.card_mul_card_classes_mul_prod_le, D.card_sq_mul_mass_mul_prod_le⟩

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- For the filling data of admissible data `D`, the scaled Siegel constant `|S̄| |Ū| n_X c_S` is at
most `(1 + b⁻⁹)` times the main second moment `(n_X d)² / (deg mass_r)` times
`deg c^f / vol^n (cov Λ / d)²`. Here `S̄` is the reduced image of the Bessel subgroup `besselS`,
`|Ū| = unipotentOrder`, `n_X` is the number of classes, `c_S = siegelConst`, `b = D.b` is the weight
at the `b`-places, `d` and `deg` are the number of coordinates and the degree of the tensor product
of the Bessel systems, and `mass_r` is the mass in the rank `r` of `Y₀`. Further
`c = openCellConst`, `f` is the number of infinite places, `vol` the volume of the integral finite
adeles, `n` the number of frame vectors, `cov = unipotentCovolume` and `Λ = frameScaleProd`. -/
lemma scaledSiegelConst_le : D.filling.scaledSiegelConst ≤
    (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment * D.filling.besselDegree * D.shape.openCellConst ^
      D.f /
      volÔ D.E ^ D.shape.n * (D.filling.unipotentCovolume * D.filling.frameScaleProd /
        Fintype.card D.filling.BesselCoord) ^ 2 := by
  -- The scaled Siegel constant is the left side of `card_mul_card_classes_mul_prod_le` times
  -- `scale`.
  let scale : ℝ := D.filling.besselDegree * D.shape.openCellConst ^ D.f / volÔ D.E ^ D.shape.n *
    (D.filling.unipotentCovolume * D.filling.frameScaleProd / Fintype.card D.filling.BesselCoord) ^
      2
  have deg_pos : 0 < D.filling.besselDegree := D.filling.besselDegree_pos
  have cell_pos : 0 < D.shape.openCellConst := D.shape.openCellConst_pos
  have vol_pos : (0 : ℝ) < volÔ D.E := by
    rw [volÔ_eq]
    positivity [rootDiscr_pos D.E]
  have N_pos : (0 : ℝ) < D.N := mod_cast D.N_prime.pos
  have h_rank : ∑ a ∈ range D.ϱ, (a + (D.k + 1) + a) = D.ϱ * (D.ϱ + D.k) := by
    induction D.ϱ with
    | zero => simp
    | succ n ih => grind [sum_range_succ]
  have h_covolume : D.filling.unipotentCovolume * D.filling.frameScaleProd =
      D.filling.unipotentOrder / (D.N ^ D.k) ^ D.f / volÔ D.E ^ (D.ϱ * (D.ϱ + D.k)) *
        √√|NumberField.discr D.E| ^ D.ϱ := by
    have h_order : ((D.filling.M : ℝ) ^ (2 * (D.ϱ * (D.ϱ + D.k)) + D.ϱ)) ^ D.f =
        D.filling.unipotentOrder := by
      rw [← pow_mul, unipotentOrder, Shape.k, card_X₀, Nat.cast_pow]
      ring_nf
    -- The factor `frameScaleProd` cancels from the definition of the covolume.
    rw [Filling.unipotentCovolume, div_mul_cancel₀ _ D.filling.frameScaleProd_pos.ne', Shape.k,
      card_X₀, h_rank, div_pow]
    erw [h_order]
    rfl
  have h_siegel : D.filling.siegelConst = (∏ v : D.Φ, D.frameMass v) *
      (D.shape.openCellConst ^ D.f * (√√|NumberField.discr D.E| ^ D.ϱ) ^ 2) /
        (((D.N ^ D.k) ^ D.f) ^ 2 * volÔ D.E ^ (D.ϱ + 1 + 2 * (D.ϱ * (D.ϱ + D.k)))) := by
    rw [D.prod_frameMass_mul_openCellConst_eq, mul_assoc, mul_div_cancel_right₀ _ (by positivity)]
  calc
    _ = Nat.card (D.filling.reducedImage besselH) * Fintype.card D.filling.Classes *
        (∏ v : D.Φ, D.frameMass v * Fintype.card (D.filling.besselSystem v).Index ^ 2 /
          (D.filling.besselSystem v).deg) * scale := by
      -- Insert the constants; the powers of N, of the volume and of the discriminant cancel.
      rw [prod_frameMass_mul_div_eq, scaledSiegelConst, card_reducedImage_besselS, h_siegel]
      simp only [scale, h_covolume, Shape.n]
      push_cast
      field_simp
      ring
    _ ≤ (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment * scale :=
      mul_le_mul_of_nonneg_right D.card_mul_card_classes_mul_prod_le (by positivity)
    _ = _ := by ring

/-- Reduction at the chosen places maps the integral group `New.Filling.latticeStabilizer` of the
filling data onto the finite group `New.Filling.ResidueGL`. -/
lemma filling_reduction_surjective : Function.Surjective D.filling.reduction := by
  intro x
  -- A preimage is the lift of the residues of `x`, written in the lattice basis of the filling.
  let lift : stdLevel D.E D.shape.BesselIndex := liftResidue (w := D.chosenPlace) (Sigma.uncurry x)
  obtain ⟨h_mem, h_reduction⟩ := (D.filling_fits.reduction_finiteEquiv_iff lift.1 x).mpr
    ⟨lift.2, reduceFamily_liftResidue (w := D.chosenPlace) (Sigma.uncurry x)⟩
  exact ⟨⟨D.filling_fits.finiteEquiv lift.1, h_mem⟩, h_reduction⟩

/-- The main second moment of the filling data, divided by their identity second moment, is
`d (N ^ k - 1) ^ f mass_k / (deg mass_r |Ū|)`. Here `d` and `deg` are the number of coordinates and
the degree of the tensor product of the Bessel systems, `mass_l` is the mass in rank `l`, and `|Ū|`
is the order `unipotentOrder` of the reduced unipotent group; `N` is the prime level, `k` and `r`
are the ranks of `X₀` and `Y₀`, and `f` is the number of infinite places. -/
lemma mainSecondMoment_div_identitySecondMoment_eq :
    D.filling.mainSecondMoment / D.filling.identitySecondMoment =
      Fintype.card D.filling.BesselCoord * (D.N ^ D.k - 1) ^ D.f * mass D.E D.k /
        (D.filling.besselDegree * mass D.E D.r * D.filling.unipotentOrder) := by
  have h_rank : D.shape.r = D.r := D.card_rowIndex
  have card_image_ne_zero : (Nat.card (D.filling.reducedImage besselH) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h_dim : (D.filling.sourceDim : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 D.filling_fits.finrank_levelSpace_eq_sourceDim.2.2.ne'
  calc
    _ = D.filling.sourceDim / (Nat.card (D.filling.reducedImage besselS) *
        (D.filling.besselDegree * mass D.E D.r)) := by
      rw [mainSecondMoment, identitySecondMoment, h_rank]
      field_simp
    _ = _ := by
      rw [sourceDim, card_reducedImage_besselS, Nat.cast_mul, Nat.cast_mul,
        card_classes_eq_card_mul_pow_mul_mass]
      field_simp

/-- Up to a factor `b ^ (± k f / 4)`, the ratio of the main second moment to the identity second
moment is `(M b ^ (-15 / 2)) ^ (k f) d ((k - 1)!) ^ f`. Here `b` is the weight at the `b`-places of
the admissible data `D`, `M = p₀ p₁` is the principal level, `d` is the number of coordinates of the
tensor product of the Bessel systems, `k` is the rank of `X₀` and `f` is the number of infinite
places. The statement is for the logarithms, with `D.logB = log b`. -/
lemma abs_log_mainSecondMoment_div_identitySecondMoment_sub_le :
    |log (D.filling.mainSecondMoment / D.filling.identitySecondMoment) -
        (D.f * D.k * (log D.M - 15 / 2 * D.logB) +
          log (Fintype.card D.filling.BesselCoord * (D.k - 1).factorial ^ D.f))| ≤
      D.f * D.k * D.logB / 4 := by
  -- Insert the sizes of the degree, of the ratio of the masses and of `N` into the formula for the
  -- ratio. All factorials cancel except `(k - 1)!`.
  have k_le_r : D.k ≤ D.r := D.k_le_r
  have k_pos : 0 < D.k := D.k_pos
  have two_le_N : 2 ≤ D.N := D.N_prime.two_le
  have pred_pos : (0 : ℝ) < D.N ^ D.k - 1 := D.pow_sub_one_pos
  have M_pos : 0 < D.M := pos D.M
  have deg_pos : 0 < D.filling.besselDegree := D.filling.besselDegree_pos
  have rd_pos : 0 < rootDiscr D.E := rootDiscr_pos D.E
  have dim_pos : 0 < Fintype.card D.filling.BesselCoord := card_pos
  have mass_k_pos : 0 < mass D.E D.k := mass_pos D.E D.k
  have mass_r_pos : 0 < mass D.E D.r := mass_pos D.E D.r
  have h_order : (D.filling.unipotentOrder : ℝ) =
      D.M ^ (D.f * (D.ϱ * (2 * D.k + 2 * D.ϱ + 1))) := by
    rw [unipotentOrder, Shape.k, card_X₀, Nat.cast_pow]
    rfl
  -- The range of `N`, and `N ^ k - 1` against `N ^ k`.
  have log_N : (D.f * D.k) • log D.N ∈
      Set.Icc ((D.f * D.k) • D.logLevelTarget) ((D.f * D.k) • (D.logLevelTarget + √D.logB)) :=
    (nsmul_right_mono _).mapsTo_Icc D.log_N_mem_Icc_logLevelTarget
  have log_pred_le : D.f • log (D.N ^ D.k - 1) ≤ D.f • log (D.N ^ D.k) :=
    nsmul_le_nsmul_right (log_le_log pred_pos (sub_one_lt _).le) _
  have log_ratio : D.f • log (D.N ^ D.k / (D.N ^ D.k - 1)) ≤ D.f • (2 / D.N : ℝ) :=
    nsmul_le_nsmul_right D.log_pow_div_pow_sub_one_le _
  have mul_mean_log_weight_eq :
      D.k * D.m * (D.f * ((∑ v : D.Φ, log (D.weight v)) / D.f)) =
      D.k * D.m * ∑ v : D.Φ, log (D.weight v) := by rw [mul_div_cancel₀ _ (ne _)]
  -- The degree and the ratio of the masses, with their factorials.
  have log_deg : log D.filling.besselDegree + D.f * ∑ l ∈ Ico (D.k - 1) D.r, log l.factorial ∈
      Set.Icc (∑ v : D.Φ, D.m * ((D.k - 1) * log (D.weight v)))
        (∑ v : D.Φ, D.m * (D.r * (log (D.weight v) + D.x⁻¹))) :=
    D.log_filling_besselDegree_mem_Icc
  have mass_ratio : |∑ i ∈ Ico D.k D.r, (log (mass D.E (i + 1)) - log (mass D.E i) -
      D.f * ((i + 1 / 2) * log D.rootDisc + log i.factorial - (i + 1) * log (2 * π)))| ≤
        log (1 + D.b⁻¹ ^ 9) - 2 * (D.f * (2 / D.N)) := D.abs_sum_log_mass_ratio_sub_le
  have first_factorial : D.f * ∑ i ∈ Ico (D.k - 1) D.k, log i.factorial =
      D.f * ∑ i ∈ {D.k - 1}, log i.factorial := by rw [D.k.Ico_pred_singleton k_pos]
  -- The remaining terms are small against `f k log b`.
  have rest_small :
      |D.f * (D.m - 1) * (D.ϱ * log (D.M * D.rootDisc / 2 / π) + log (√D.rootDisc / 2 / π)) -
      D.m * ∑ v : D.Φ, log (D.weight v)| ≤ D.f * D.k * D.logB / 4 - (log (1 + D.b⁻¹ ^ 9) +
        D.m * (D.m * ∑ v : D.Φ, log (D.weight v) + D.f * D.r * D.x⁻¹) + D.f * D.k * √D.logB) :=
    le_sub_iff_add_le.mpr D.le_of_hasLogBound
  rw [mainSecondMoment_div_identitySecondMoment_eq, h_order]
  simp only [eq_tsub_of_add_eq D.r_add_one] at *
  -- Expand the logarithms and the sums: `sum_range_sub` telescopes the mass terms, and
  -- `sum_range_id` evaluates the sums of the indices. What is left is linear in the logarithms, in
  -- the sums of `log i!` and in `log b`.
  simp (disch := intros; first | positivity | omega) only [log_div, log_mul, log_pow, log_sqrt,
    sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_range_id, ← Nat.choose_two_right,
    card_univ, logLevelTarget, abs_le, ↓sum_Ico_eq_sub, Set.mem_Icc, sum_sub_distrib, ← mul_sum,
    sum_singleton, ← sum_mul, ← Nat.cast_sum _ (·), ↓sum_range_sub (log <| mass D.E ·)] at *
  push_cast (disch := apply D.nat_le_of_hasLogBound) [Nat.cast_choose_two, ← add_assoc,
    m_eq_two_mul_varrho_add_two] at *
  constructor <;> linarith

/-- For admissible data `D`, the ratio of the main second moment to the identity second moment lies
between `b ^ (11 k f)` and `(M / b ^ 6) ^ (k f)`. Here `b = D.b` is the weight at the `b`-places,
`M = p₀ p₁` is the principal level, `k` the rank of `X₀` and `f` the number of infinite places. -/
theorem mainSecondMoment_div_identitySecondMoment_mem_Icc :
    D.filling.mainSecondMoment / D.filling.identitySecondMoment ∈
      Set.Icc (D.b ^ (11 * (D.k * D.f))) ((D.M / D.b ^ 6) ^ (D.k * D.f)) := by
  -- The factor `d ((k - 1)!) ^ f` lies between `1` and `b ^ (5 k f / 4)`, and `b ^ 19 ≤ M`.
  have M_pos : (0 : ℝ) < D.M := Nat.cast_pos.2 (pos D.M)
  have ratio_pos : 0 < D.filling.mainSecondMoment / D.filling.identitySecondMoment := by
    have order_pos : 0 < D.filling.unipotentOrder := by simp [← card_reducedImage_besselU]
    rw [mainSecondMoment_div_identitySecondMoment_eq]
    positivity [D.filling.besselDegree_pos, mass_pos D.E D.k, mass_pos D.E D.r, D.pow_sub_one_pos]
  have log_factor_nonneg :
      0 ≤ log (Fintype.card D.filling.BesselCoord * (D.k - 1).factorial ^ D.f) :=
    mod_cast log_natCast_nonneg (Fintype.card D.filling.BesselCoord * (D.k - 1).factorial ^ D.f)
  have log_factor_le : log (Fintype.card D.filling.BesselCoord * (D.k - 1).factorial ^ D.f) ≤
      D.f * D.k * (5 / 4 * D.logB) := by
    refine (log_le_log (by positivity) D.card_besselCoord_mul_factorial_le).trans_eq ?_
    rw [log_pow, log_pow, log_pow, log_sqrt (sqrt_nonneg _), log_sqrt (exp_nonneg _), log_exp]
    linarith
  have level_ge : (D.f * D.k : ℝ) * (19 * D.logB) ≤ D.f * D.k * log D.M := by
    gcongr
    simpa using log_le_log (by positivity) (D.le_of_hasLogBound : D.b ^ 19 ≤ D.M)
  have one_le_logB : 1 ≤ D.logB := D.le_of_hasLogBound
  have f_k_logB_nonneg : (0 : ℝ) ≤ D.f * D.k * D.logB := by positivity
  obtain ⟨h_lower, h_upper⟩ := abs_le.1 D.abs_log_mainSecondMoment_div_identitySecondMoment_sub_le
  constructor
  · rw [← log_le_log_iff (by positivity) ratio_pos, log_pow, log_exp]
    push_cast
    linarith
  · rw [← log_le_log_iff ratio_pos (by positivity), log_pow, log_div M_pos.ne' (by positivity),
      log_pow, log_exp]
    push_cast
    linarith

/-- The prime level `N` is at most `b ^ (60 n)`, where `n` is `D.shape.n`. -/
lemma N_le_pow : (D.N : ℝ) ≤ D.b ^ (60 * D.shape.n) := by
  have h_log : log D.N ≤ 30 * (2 * D.ϱ + 2) * D.logB := by
    simpa [D.m_eq_two_mul_varrho_add_two] using D.log_N_mem_Icc.2
  rw [← log_le_log_iff (Nat.cast_pos.2 D.N_prime.pos) (by positivity), log_pow, log_exp]
  push_cast
  linarith

/-- Replacing `N ^ k` by `N ^ k - 1` loses at most the factor `b`, as both `b` and `N ^ k` are at
least `2`. -/
lemma pow_div_le_pow_sub_one : (D.N : ℝ) ^ D.k / D.b ≤ D.N ^ D.k - 1 := by
  have two_le_b : 2 ≤ D.b := D.le_of_hasLogBound
  have two_le_pow : (2 : ℝ) ≤ D.N ^ D.k :=
    mod_cast D.N_prime.two_le.trans (Nat.le_self_pow D.k_pos.ne' _)
  calc (D.N : ℝ) ^ D.k / D.b ≤ D.N ^ D.k / 2 := by gcongr
    _ ≤ D.N ^ D.k - 1 := by linarith

/-- The filling data of `D` satisfy the standing hypotheses `New.Filling.IsAdmissible`: the level
is the preimage of the principal level, reduction is onto, and the size inequalities hold. -/
instance : D.filling.IsAdmissible := by
  have h_energy : 0 < D.filling.identitySecondMoment :=
    mul_pos (Nat.cast_pos.2 Nat.card_pos)
      (Nat.cast_pos.2 D.filling_fits.finrank_levelSpace_eq_sourceDim.2.2)
  have h_rank : D.shape.k = D.k := D.card_X₀
  have h_b : D.filling.b = D.b := rfl
  have h_varpi (v : InfinitePlace D.E) : ‖Φ v D.filling.deltaE.val‖ = v
    (P.deltaE D.towerExp).val := by
    rw [← InfinitePlace.apply, mk_Φ]
    rfl
  have h_kappa (v : InfinitePlace D.E) :
      |D.filling.realM v| = D.M * v (P.deltaE D.towerExp).val / (2 * π) := by
    rw [abs_realM_eq, ← h_varpi v]
    rfl
  exact
    { sourceLevel_eq := D.levelX_zero_eq_comap
      reduction_surjective := D.filling_reduction_surjective
      norm_deltaE_le := fun v ↦ by
                  rw [h_varpi v, h_b]
                  exact (D.apply_deltaE_mem_Icc v).2
      one_le_abs_realM := fun v ↦ D.le_of_hasLogBound.trans_eq (h_kappa v).symm
      abs_realM_le := fun v ↦ by
        rw [h_kappa v, h_b]
        exact D.le_of_hasLogBound
      N_le := D.N_le_pow
      mul_identitySecondMoment_le := by
                    rw [h_rank]
                    exact (le_div_iff₀ h_energy).1
                      D.mainSecondMoment_div_identitySecondMoment_mem_Icc.1
      mainSecondMoment_le := by
              rw [h_rank]
              exact (div_le_iff₀ h_energy).1 D.mainSecondMoment_div_identitySecondMoment_mem_Icc.2
      card_besselCoord_le := by
        rw [h_rank]
        exact D.card_besselCoord_le_pow
      le_relIndex := by
        rw [D.relIndex_latticeStabilizer, h_rank]
        exact pow_le_pow_left₀ (by positivity) D.pow_div_le_pow_sub_one _
      scaledSiegelConst_le := D.scaledSiegelConst_le }

end New.Data

end
