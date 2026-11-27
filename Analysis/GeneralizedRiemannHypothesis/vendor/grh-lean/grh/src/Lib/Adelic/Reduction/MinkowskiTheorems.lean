import Lib.General.LinearAlgebra.PolarDecomposition
import Lib.General.NumberTheory.FrobeniusOrbits

/-!
# Adelic Minkowski theorems and counts of rational points in boxes

This file proves Minkowski's first theorem and the upper bound in his second theorem over the
adeles, for the lattice attached to `y : GL n (𝔸 E)`. This lattice consists of the rational vectors
`ξ` with `y⁻¹ ξ` integral at the finite places, measured by `y⁻¹ ξ` at the infinite places. Here
`New.𝔸 E` is `ℂ ^ f × 𝔸f E` with `f = New.Core.numInfPlaces E`; here `[CMType E]` makes `E` a number
field whose infinite places are all complex, each place `w` with a chosen embedding `Φ w : E → ℂ`.
`New.toAdele` is the diagonal embedding, `New.ideleAbs` the adelic absolute value and `New.Ô` the
ring of integral finite adeles, and the unit box is `ball 0 1 ×ˢ Ô E` (sup norm) in each coordinate.

## Main definitions and results

* `New.minkowski_first`: a lower bound for the number of rational `ξ` with `y⁻¹ ξ` in the unit box.
* `New.Core.twoAtInfinity`, `New.Core.dyadicDiag`, `New.Core.profileBases`: the idele that is `2` at
  infinity, the diagonal matrices `D` of its powers, and the rational bases `Y` with `y⁻¹ Y D⁻¹` in
  a given set.
* `New.Core.frameLattice`, `New.Core.frameLength`: the lattice of `y` and the Euclidean length of
  `y⁻¹ ξ` at infinity.
* `New.Core.minkowski_second_theorem`: the second theorem. The lattice contains a basis of `E ^ n`
  for which `|det y|` times the product of the `2 f`-th powers of the lengths is bounded in terms of
  `f`, `n` and the discriminant. The proof takes successive minima and applies the first theorem to
  a box without nonzero lattice vectors.
* `New.exists_basis_frameLength_le_two_zpow`: a bound of the same kind, with a larger constant, for
  the lengths rounded up to powers `2 ^ x j`.
* `New.Core.encard_le_of_dyadic_box`: at most `C * 4 ^ (f * ∑ i, (x i)⁺)` rational vectors `ξ` have
  the vector of the `twoAtInfinity E ^ (-x i) * ξ i` in a given compact set.
* `New.Core.exists_eq_zero_of_zpow_mul_mem`: for a compact set `B` of adeles and all large `m`, no
  nonzero `a` in `E` has `twoAtInfinity E ^ m * a` in `B`.

Notions from other files:
* `New.ratVectors`: the image of `E ^ n` in `𝔸 E ^ n` under the diagonal embedding, as an additive
  subgroup.

## Relation to the literature

Part of a known result: Reduction theory, here the adelic Minkowski theorems. For Mahler-Godement
compactness and finite covolume see `Lib.Adelic.Reduction.FiniteVolume`.
-/

noncomputable section

/-! ## Minkowski's first theorem with multiplicity -/

section MinkowskiFirst

open Set ENNReal Fintype Matrix MeasureTheory Metric NumberField Measure

namespace New

variable {E : Type*} [Field E] [CMType E] {n : Type*} [Fintype n] [DecidableEq n] (y : GL n (𝔸 E))

/-- Unfolding: the number of rational `ξ` with `y⁻¹ (ξ + x) ∈ S`, integrated over the quotient of
`𝔸 ^ n` by the subgroup `E ^ n = ratVectors E n`, is `|det y| * volume S`. The integral over the
quotient is taken against `quotMeasure`, the measure on `𝔸 ^ n` given by `volume` weighted by a
cutoff for this subgroup; its total mass is the covolume `1`. -/
lemma lintegral_encard_rat_points {S : Set (n → 𝔸 E)} (hS : MeasurableSet S) :
    ENNReal.ofReal (ideleAbs y.det) * volume S =
      ∫⁻ x : n → 𝔸 E, {ξ : n → E |
        y⁻¹.val *ᵥ (toAdele ∘ ξ + x) ∈ S}.encard ∂(ratVectors E n).quotMeasure := by
  -- Unfolding: `(x, ξ) ↦ y⁻¹ (ξ + x)` carries `quotMeasure ⊗ count` to `|det y| • volume`. The
  -- measure of the preimage of `S` is the left side, and by Fubini it is also the right side.
  have h_scale : MeasurePreserving (y⁻¹.1 *ᵥ ·) volume (ENNReal.ofReal (ideleAbs y.det) • volume) :=
    ⟨by fun_prop, (volume_map_mulVec_adele y⁻¹).trans (by simp)⟩
  have h_unfold : MeasurePreserving (fun p : (n → 𝔸 E) × ratVectors E n ↦ y⁻¹.1 *ᵥ (p.2 +ᵥ p.1))
      ((ratVectors E n).quotMeasure.prod count) (ENNReal.ofReal (ideleAbs y.det) • volume) :=
    h_scale.comp measurePreserving_addOrbitMeasure
  rw [← smul_eq_mul, ← Measure.smul_apply, ← h_unfold.measure_preimage hS.nullMeasurableSet,
    Measure.prod_apply (h_unfold.measurable hS)]
  refine lintegral_congr fun x ↦ ?_
  -- the fibre over `x` is counted in `ratVectors E n`, the image of `n → E` under `toAdele ∘ ·`
  rw [count_apply .of_discrete]
  let e : (n → E) ≃ ratVectors E n := .ofInjective _ (toAdele (E := E)).injective.comp_left
  exact_mod_cast encard_congr e.subtypeEquivOfSubtype.symm

omit [DecidableEq n] in
/-- The box of radius `r`, the adelic vectors with all entries of absolute value below `r` at the
`f = numInfPlaces E` infinite places and integral at the finite places, has volume
`((r ^ 2 * π * (2 / rd)) ^ f) ^ card n`, where `rd = rootDiscr E` is the root discriminant. -/
lemma volume_pi_ball_prod_integral {r : ℝ} (hr : 0 < r) :
    volume (univ.pi fun _ : n ↦ (ball 0 r ×ˢ Ô E : Set (𝔸 E))) = ENNReal.ofReal
      (((r ^ 2 * Real.pi * (2 / rootDiscr E)) ^ Core.numInfPlaces E) ^ card n) := by
  have h_inf : volume (ball (0 : InfinitePlace E → ℂ) r) =
      ENNReal.ofReal (r ^ 2 * Real.pi) ^ Core.numInfPlaces E := by
    simp [volume_pi, ball_pi _ hr, ofReal_mul (sq_nonneg r), ofReal_pow hr.le, ← NNReal.coe_real_pi]
  have h_entry : volume (ball 0 r ×ˢ Ô E : Set (𝔸 E)) =
      ENNReal.ofReal ((r ^ 2 * Real.pi * (2 / rootDiscr E)) ^ Core.numInfPlaces E) := by
    rw [volume_eq_prod, prod_prod, h_inf, volume_Ô, mul_pow (r ^ 2 * Real.pi), ← inv_div, inv_pow,
      ← volÔ_eq, ← ofReal_pow (by positivity), ofReal_mul (by positivity), ofReal_coe_nnreal]
  rw [volume_pi, pi_pi, h_entry, Finset.prod_const, Finset.card_univ,
    ← ofReal_pow (by positivity [rootDiscr_pos E])]

open Pointwise in
/-- Minkowski's first theorem with multiplicity: for `y` in `GL n (𝔸 E)`, the adelic absolute value
`|det y|` is at most `(2 rd) ^ (f n)` times the number of `ξ` in `E ^ n` with `y⁻¹ ξ` integral at
the finite places and all its entries of absolute value below `1` at the infinite places. Here
`rd = rootDiscr E` is the root discriminant, `f` the number of infinite places and `n` stands for
`card n`. -/
lemma minkowski_first :
    ENNReal.ofReal (ideleAbs y.det) ≤
      ENNReal.ofReal (((2 * rootDiscr E) ^ Core.numInfPlaces E) ^ card n) *
        {ξ : n → E | ∀ i : n, (y⁻¹.val *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E}.encard := by
  -- Blichfeldt's argument for the box `S` of radius `1 / 2`: two rational points of a translate of
  -- `y S` differ by a point of `y` times the box of radius `1`.
  let box : Set (𝔸 E) := ball 0 2⁻¹ ×ˢ Ô E
  let S : Set (n → 𝔸 E) := univ.pi fun _ ↦ box
  set N : ℕ∞ := {ξ : n → E | ∀ i : n, (y⁻¹.1 *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E}.encard
  have h_count (x : n → 𝔸 E) : {ξ : n → E | y⁻¹.1 *ᵥ (toAdele ∘ ξ + x) ∈ S}.encard ≤ N := by
    obtain h_empty | ⟨ξ₀, hξ₀⟩ := {ξ | y⁻¹.1 *ᵥ (toAdele ∘ ξ + x) ∈ S}.eq_empty_or_nonempty
    · simp only [h_empty, encard_empty, zero_le]
    refine encard_le_encard_of_injOn (f := (· - ξ₀)) (fun ξ hξ i ↦ ?_) sub_left_injective.injOn
    simpa [box, mulVec_add, mulVec_sub, ← two_mul] using
      sub_mem_sub (hξ i (mem_univ i)) (hξ₀ i (mem_univ i))
  -- Averaging the count over the translates gives `|det y| vol S`.
  have h_mean : .ofReal (ideleAbs y.det) * volume S ≤ (N : ℝ≥0∞) := by
    rw [lintegral_encard_rat_points y (.univ_pi fun _ ↦ (isOpen_ball.prod isOpen_Ô).measurableSet)]
    exact lintegral_le_const (.of_forall fun x ↦ mod_cast h_count x)
  -- It remains to see `1 ≤ ((2 rd) ^ f) ^ n * vol S`, and the right side is `π ^ (f n)`.
  set c : ℝ := ((2 * rootDiscr E) ^ Core.numInfPlaces E) ^ card n with hc
  have h_base : 2 * rootDiscr E * (2⁻¹ ^ 2 * Real.pi * (2 / rootDiscr E)) = Real.pi := by
    field [(rootDiscr_pos E).ne']
  have h_vol : 1 ≤ ENNReal.ofReal c * volume S := by
    rw [volume_pi_ball_prod_integral (by positivity),
      ← ofReal_mul (by positivity [rootDiscr_pos E]), hc, ← mul_pow, ← mul_pow, h_base,
      one_le_ofReal]
    exact one_le_pow₀ (one_le_pow₀ (by linarith [Real.two_le_pi]))
  calc _ ≤ ENNReal.ofReal c * volume S * ENNReal.ofReal (ideleAbs y.det) :=
        le_mul_of_one_le_left' h_vol
    _ ≤ ENNReal.ofReal c * N := by grw [mul_assoc, mul_comm (volume S), h_mean]

/-- Minkowski's first theorem: if `|det y| > (2 * rootDiscr E) ^ (f * n)`, with `f` the number of
infinite places, some nonzero rational `ξ` has `y⁻¹ ξ` integral at the finite places and all
its entries of absolute value `< 1` at the infinite places. -/
lemma exists_ne_zero_inv_mulVec_mem
    (h_det : ((2 * rootDiscr E) ^ Core.numInfPlaces E) ^ card n < ideleAbs y.det) :
    ∃ ξ : n → E, (∀ i : n, (y⁻¹.val *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E) ∧ ξ ≠ 0 := by
  -- more than one rational `ξ` has `y⁻¹ ξ` in the box, so one of them is not zero
  have h_count : 1 < {ξ : n → E | ∀ i : n, (y⁻¹.1 *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E}.encard :=
    mod_cast one_lt_of_lt_mul_right (α := ℝ≥0∞)
      (((ofReal_lt_ofReal_iff ideleAbs_pos).2 h_det).trans_le (minkowski_first y))
  exact exists_ne_of_one_lt_encard h_count 0

end New

end MinkowskiFirst

/-! ## Minkowski's second theorem and counts of rational points in boxes -/

section MinkowskiSecond

open NumberField Finset Fintype Prod Complex Int Matrix Real Function Metric

namespace New.Core

variable (E : Type _) [Field E] [CMType E] {n : Type _} [Fintype n] [DecidableEq n]

/-! ### Isometries, determinants and powers of two at infinity -/

/-- The idele of `E` that is `2` at all infinite places and `1` at the finite places. -/
def twoAtInfinity (E : Type _) [Field E] [NumberField E] : (𝔸 E)ˣ :=
  Units.map ⟨⟨fun z : ℂ ↦ (fun _ ↦ z, 1), rfl⟩, by aesop⟩ (Units.mk0 2 (by simp))

variable {E}

/-- A matrix `Q` with orthonormal columns, that is `Qᴴ * Q = 1`, preserves the sum of the squared
absolute values of the entries of a vector. -/
lemma sum_norm_sq_mulVec_of_isometry {m : Type*} [Fintype m] {Q : Matrix m n ℂ} (hQ : Qᴴ * Q = 1)
    (v : n → ℂ) : ∑ i : m, ‖(Q *ᵥ v) i‖ ^ 2 = ∑ i : n, ‖v i‖ ^ 2 := by
  have h_inner : star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = star v ⬝ᵥ v := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hQ, one_mulVec]
  simpa [dotProduct, ← ofReal_inj, ← conj_mul'] using h_inner

/-- The adelic absolute value of the determinant of the adelic matrix with components `a w` at the
infinite places `w` and finite part `b` (`mkAdelicGL`) is the product of the `‖det (a w)‖ ^ 2` and
of the absolute value `finIdeleAbs` of the finite idele `det b`. -/
lemma ideleAbs_det_mkAdelicGL (a : InfinitePlace E → GL n ℂ) (b : GL n (𝔸f E)) :
    ideleAbs (mkAdelicGL (a, b)).det =
      (∏ w : InfinitePlace E, ‖(a w).val.det‖ ^ 2) * finIdeleAbs b.det := by
  simp [finIdeleAbs, ideleAbs, det_apply, fst_sum, fst_prod, snd_sum, snd_prod]

/-- For an integer vector `x`, the diagonal adelic matrix whose `i`-th entry is `2 ^ x i` at the
infinite places and `1` at the finite places. -/
def dyadicDiag {E : Type _} [Field E] [NumberField E]
    (x : n → ℤ) : GL n (𝔸 E) := diagGL fun i : n ↦ twoAtInfinity E ^ x i

/-- The set of `Y` in `GL n E` with `y⁻¹ Y D⁻¹` in `M`, where `D = dyadicDiag x` is diagonal with
entries `2 ^ x i` at infinity and `1` at the finite places. -/
def profileBases (M : Set (GL n (𝔸 E))) (x : n → ℤ) (y : GL n (𝔸 E)) : Set (GL n E) :=
  {Y : GL n E | y⁻¹ * Y.map toAdele * (dyadicDiag x)⁻¹ ∈ M}

/-- The adeles with components of absolute value at most `r` (by default `1`) at the infinite places
and integral at the finite places form a compact set. -/
lemma isCompact_closedBall_prod_integral (r : ℝ := 1) :
    IsCompact (closedBall 0 r ×ˢ Ô E : Set (𝔸 E)) :=
  (isCompact_closedBall 0 r).prod isCompact_Ô

/-- The matrix `dyadicDiag x`, with diagonal entries `2 ^ x i` at the infinite places and `1` at
the finite ones, has determinant of adelic absolute value `(2 ^ (2 f)) ^ ∑ i, x i`, with `f` the
number of infinite places. -/
lemma ideleAbs_det_dyadicDiag (x : n → ℤ) :
    ideleAbs (dyadicDiag x : GL n (𝔸 E)).det = (2 ^ (2 * numInfPlaces E)) ^ ∑ i : n, x i := by
  have h_two : ideleAbs (twoAtInfinity E) = 2 ^ (2 * numInfPlaces E) := by
    simp [ideleAbs, twoAtInfinity, pow_mul]
  have h_det : (dyadicDiag x : GL n (𝔸 E)).det = ∏ i : n, twoAtInfinity E ^ x i :=
    Units.ext (by simp [dyadicDiag, diagGL])
  simp [h_det, h_two, DiscreteSeries.zpow_sum_of_ne_zero]

/-- The matrix `dyadicDiag x` for natural exponents `x i` has determinant of adelic absolute value
`((2 ^ f) ^ ∑ i, x i) ^ 2`, with `f` the number of infinite places. -/
lemma ideleAbs_det_dyadicDiag_natCast (x : n → ℕ) :
    ideleAbs (dyadicDiag fun i : n ↦ (x i : ℤ) : GL n (𝔸 E)).det =
      ((2 ^ numInfPlaces E) ^ ∑ i : n, x i) ^ 2 := by
  rw [ideleAbs_det_dyadicDiag, ← Nat.cast_sum, zpow_natCast]
  ring

/-- For natural exponents `x i`, all entries of the inverse of `dyadicDiag x` (the diagonal matrix
with entries `2 ^ x i` at the infinite places and `1` at the finite ones) have absolute value at
most `1` at the infinite places and lie in the ring `Ô E` of integral finite adeles. -/
lemma dyadicDiag_inv_mem (x : n → ℕ) :
    (dyadicDiag fun i : n ↦ (x i : ℤ) : GL n (𝔸 E))⁻¹.val ∈
      Set.matrix (closedBall (0 : InfinitePlace E → ℂ) 1 ×ˢ Ô E) := by
  simpa [dyadicDiag, diagonal_mem_matrix_iff, Pi.pow_def, twoAtInfinity, ← map_inv] using
    fun i ↦ inv_le_one_of_one_le₀ (one_le_pow₀ (n := x i) (one_le_two (α := ℝ)))

/-- The inverse of `dyadicDiag x` multiplies the `i`-th entry of an adelic vector by
`twoAtInfinity E ^ (-x i)`. -/
lemma dyadicDiag_inv_mulVec_apply (x : n → ℤ) (v : n → 𝔸 E) (i : n) :
    ((dyadicDiag x)⁻¹.val *ᵥ v) i = (twoAtInfinity E ^ (-x i)).val * v i := by
  simp [dyadicDiag, diagGL, mulVec_diagonal, ← map_inv, -map_zpow]

/-- An invertible matrix with entries in `E` has, over the adeles, a determinant of absolute value
`1`: this is the product formula for `det Y`. -/
@[simp↓]
lemma ideleAbs_det_map_toAdele (Y : GL n E) : ideleAbs (Y.map toAdele).det = 1 := by
  rw [Y.map_det toAdele, ideleAbs_toAdele]

/-! ### Successive minima -/

/-- A real function `len` attains its minimum on a nonempty set `S` that has only finitely many
points below each bound. -/
lemma exists_min_of_finite_le {V : Type*} {S : Set V} (len : V → ℝ)
    (h_finite : ∀ r : ℝ, {v ∈ S | len v ≤ r}.Finite) (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ u ∈ S, len v ≤ len u := by
  obtain ⟨v₀, hv₀⟩ := hS
  obtain ⟨v, hv, hv_least⟩ :=
    Set.exists_min_image {u ∈ S | len u ≤ len v₀} len (h_finite _) ⟨v₀, hv₀, le_rfl⟩
  exact ⟨v, hv.1, by grind⟩

/-- Successive minima. Let `L` be a spanning set of a vector space `V` with finitely many vectors
below each bound for the length `len`. For `k` at most the dimension of `V` there are `k`
independent vectors in `L`, each of least length among the vectors of `L` outside the span of the
earlier ones. -/
lemma exists_successive_minima {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {L : Set V}
    (h_span : Submodule.span K L = ⊤) (len : V → ℝ)
    (h_finite : ∀ r : ℝ, {v ∈ L | len v ≤ r}.Finite) {k : ℕ} (hk : k ≤ Module.finrank K V) :
    ∃ y : Fin k → V,
      (∀ j : Fin k, y j ∈ L) ∧
      LinearIndependent K y ∧
      ∀ j : Fin k, ∀ v ∈ L, v ∉ Submodule.span K (y '' Set.Iio j) → len (y j) ≤ len v := by
  induction k with
  | zero => exact ⟨Fin.elim0, by simp, linearIndependent_empty_type, by simp⟩
  | succ k ih =>
    obtain ⟨y, hy_mem, hy_indep, hy_least⟩ := ih (Nat.le_of_succ_le hk)
    -- Fewer vectors than the dimension do not span, so part of `L` lies outside their span.
    have h_lt : Submodule.span K (Set.range y) < ⊤ :=
      Submodule.lt_top_of_finrank_lt_finrank (by simpa [finrank_span_eq_card hy_indep] using hk)
    have h_nonempty : (L \ Submodule.span K (Set.range y)).Nonempty :=
      Set.sdiff_nonempty.2 fun h_le ↦ h_lt.not_ge (h_span.ge.trans (Submodule.span_le.2 h_le))
    -- Take `v` of least length among such vectors.
    obtain ⟨v, ⟨hv_mem, hv_out⟩, hv_least⟩ :=
      exists_min_of_finite_le len (fun r ↦ (h_finite r).subset (by grind)) h_nonempty
    have h_image (S : Set (Fin k)) :
        (Fin.snoc y v : Fin (k + 1) → V) '' (Fin.castSucc '' S) = y '' S := by
      simp [Set.image_image]
    refine ⟨Fin.snoc y v, by simp [Fin.forall_fin_succ', hy_mem, hv_mem],
      linearIndependent_finSnoc.2 ⟨hy_indep, hv_out⟩, fun j ↦ ?_⟩
    induction j using Fin.lastCases with
    | last =>
      have h_last : Set.Iio (Fin.last k) = Fin.castSucc '' Set.univ := by
        simp [Set.ext_iff, Fin.lt_def]
      rw [h_last, h_image, Set.image_univ, Fin.snoc_last]
      exact fun u hu_mem hu_out ↦ hv_least u ⟨hu_mem, hu_out⟩
    | cast j => simpa [← Fin.image_castSucc_Iio, h_image] using hy_least j

/-- The lattice `E ^ n ∩ z_f Ô ^ n` of an adelic frame `z`: the rational vectors `ξ` such that
`z⁻¹ ξ` is integral at the finite places. -/
def frameLattice (z : GL n (𝔸 E)) : Set (n → E) :=
  {ξ : n → E | ∀ i : n, ((z⁻¹.val *ᵥ toAdele ∘ ξ) i).2 ∈ Ô E}

/-- The length of a rational vector `ξ` at an adelic frame `z`: the Euclidean norm of the
coordinates of `z⁻¹ ξ` at all infinite places together. -/
def frameLength (z : GL n (𝔸 E)) (ξ : n → E) : ℝ :=
  ‖WithLp.toLp 2 fun p : InfinitePlace E × n ↦ ((z⁻¹.val *ᵥ toAdele ∘ ξ) p.2).1 p.1‖

/-- Each coordinate of `z⁻¹ ξ` at an infinite place `w` has absolute value at most the length
`frameLength z ξ`, the Euclidean norm of all these coordinates together. -/
lemma norm_apply_le_frameLength (z : GL n (𝔸 E)) (ξ : n → E) (w : InfinitePlace E) (i : n) :
    ‖((z⁻¹.val *ᵥ toAdele ∘ ξ) i).1 w‖ ≤ frameLength z ξ :=
  PiLp.norm_apply_le
    (WithLp.toLp 2 fun p : InfinitePlace E × n ↦ ((z⁻¹.val *ᵥ toAdele ∘ ξ) p.2).1 p.1) (w, i)

/-- The lattice `frameLattice z` of the rational `ξ` with `z⁻¹ ξ` integral at the finite places
spans `E ^ n` over `E`. -/
lemma span_frameLattice (z : GL n (𝔸 E)) : Submodule.span E (frameLattice z) = ⊤ := by
  -- A multiple `N • ξ` that clears the denominators of `z⁻¹ ξ` lies in the lattice.
  refine top_unique fun ξ _ ↦ ?_
  obtain ⟨N, hN, h_integral⟩ :=
    exists_forall_mul_mem_Ô fun i : n ↦ ((z⁻¹.val *ᵥ toAdele ∘ ξ) i).2
  have h_mem : (N : E) • ξ ∈ frameLattice z := fun i ↦ by
    simpa [show toAdele ∘ ((N : E) • ξ) = (N : 𝔸 E) • toAdele ∘ ξ from funext fun j ↦ by simp,
      mulVec_smul] using h_integral i
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hN)).1 (Submodule.subset_span h_mem)

/-- Only finitely many vectors of the lattice `frameLattice z` have length `frameLength z` at most
`r`, that length being the Euclidean norm of `z⁻¹ ξ` at all infinite places together. -/
lemma finite_frameLattice_of_frameLength_le (z : GL n (𝔸 E)) (r : ℝ) :
    {ξ ∈ frameLattice z | frameLength z ξ ≤ r}.Finite := by
  -- These vectors lie in `z` times a compact box, and `E ^ n` is a lattice in the adelic vectors.
  have h_finite : {ξ : n → E | toAdele ∘ ξ ∈
      z.val.mulVec '' Set.univ.pi fun _ ↦ closedBall 0 r ×ˢ Ô E}.Finite :=
    isCovolOneLattice_ratVectors.finite_preimage
      ((isCompact_univ_pi fun _ ↦ isCompact_closedBall_prod_integral r).image (by fun_prop))
  refine h_finite.subset fun ξ ⟨h_integral, h_le⟩ ↦
    ⟨z⁻¹.val *ᵥ toAdele ∘ ξ, fun i _ ↦ ⟨?_, h_integral i⟩, by simp⟩
  exact mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonempty _).2 fun w ↦
    (norm_apply_le_frameLength z ξ w i).trans h_le)

/-- A nonzero rational vector `ξ` has positive length `frameLength z ξ`, the Euclidean norm of
`z⁻¹ ξ` at all infinite places together. -/
lemma frameLength_pos (z : GL n (𝔸 E)) {ξ : n → E} (hξ : ξ ≠ 0) : 0 < frameLength z ξ := by
  -- If the length vanishes, so does `ξ = z (z⁻¹ ξ)` at the infinite places.
  refine lt_of_not_ge fun h_le ↦ hξ (funext fun i ↦ ?_)
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have h_coord (j : n) : ((z⁻¹.val *ᵥ toAdele ∘ ξ) j).1 w = 0 :=
    norm_le_zero_iff.1 ((norm_apply_le_frameLength z ξ w j).trans h_le)
  have h_frame : ((z.val *ᵥ z⁻¹.val *ᵥ toAdele ∘ ξ) i).1 w = 0 := by
    rw [mulVec, dotProduct, fst_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun j _ ↦ by simp [-coe_units_inv, h_coord j]
  simpa using h_frame

/-- Let `b` be triangular for the weight `wt` (`b k l = 0` if `wt l < wt k`) and `X * b` unitary, so
that `b⁻¹ c` gives the coordinates of `X c` in the orthonormal basis formed by the columns of
`X * b`. If `c` vanishes at the weights above `wt j` and the coordinates of weight at most `wt j`
have absolute value below `ρ > 0`, then the squared Euclidean norm of `X c` is below
`card n * ρ ^ 2`. -/
lemma sum_norm_sq_mulVec_lt_of_blockTriangular [Nonempty n] {ι : Type*} [LinearOrder ι]
    {wt : n → ι} {X : Matrix n n ℂ} {b : GL n ℂ} (b_tri : b.val.BlockTriangular wt)
    (b_orth : (X * b.val)ᴴ * (X * b.val) = 1) {c : n → ℂ} {j : n}
    (h_last : ∀ k : n, c k ≠ 0 → wt k ≤ wt j) {ρ : ℝ} (hρ : 0 < ρ)
    (h_box : ∀ l : n, wt l ≤ wt j → ‖(b⁻¹.val *ᵥ c) l‖ < ρ) :
    ∑ i : n, ‖(X *ᵥ c) i‖ ^ 2 < Fintype.card n * ρ ^ 2 := by
  -- The coordinates after `j` vanish, because `b⁻¹` is triangular.
  have coord_lt (l : n) : ‖(b⁻¹.val *ᵥ c) l‖ < ρ := by
    rcases le_or_gt (wt l) (wt j) with h_le | h_gt
    · exact h_box l h_le
    have h_zero : (b⁻¹.val *ᵥ c) l = 0 := Finset.sum_eq_zero fun k _ ↦ by
      by_cases hk : c k = 0
      · simp [hk]
      · simp [blockTriangular_inv_of_blockTriangular b_tri ((h_last k hk).trans_lt h_gt)]
    rwa [h_zero, norm_zero]
  calc ∑ i : n, ‖(X *ᵥ c) i‖ ^ 2 = ∑ i : n, ‖((X * b.val) *ᵥ b⁻¹.val *ᵥ c) i‖ ^ 2 := by
        rw [mulVec_mulVec, Units.mul_inv_cancel_right]
    _ = ∑ l : n, ‖(b⁻¹.val *ᵥ c) l‖ ^ 2 := sum_norm_sq_mulVec_of_isometry b_orth _
    _ < ∑ _ : n, ρ ^ 2 := sum_lt_sum_of_nonempty univ_nonempty fun l _ ↦
        pow_lt_pow_left₀ (coord_lt l) (norm_nonneg _) two_ne_zero
    _ = Fintype.card n * ρ ^ 2 := by simp

/-- The square of the length `frameLength z ξ` is the sum over the infinite places `w` of the
squared Euclidean norm of `z_w⁻¹ ξ_w`, where `z_w` is the component of `z` at `w` and `ξ_w` the
image of `ξ` under the embedding `Φ w`. -/
lemma frameLength_sq (z : GL n (𝔸 E)) (ξ : n → E) :
    frameLength z ξ ^ 2 = ∑ w : InfinitePlace E, ∑ i : n,
      ‖((z.map (evalInf w))⁻¹.val *ᵥ fun k : n ↦ Φ w (ξ k)) i‖ ^ 2 := by
  -- the component at `w` of `z⁻¹ ξ` is `z_w⁻¹ ξ_w`, as `evalInf w` is a ring homomorphism
  have h_coord (w : InfinitePlace E) (i : n) : ((z⁻¹.val *ᵥ toAdele ∘ ξ) i).1 w =
      ((z.map (evalInf w))⁻¹.val *ᵥ fun k : n ↦ Φ w (ξ k)) i := by
    rw [← map_inv]
    exact RingHom.map_mulVec (evalInf w) z⁻¹.val (toAdele ∘ ξ) i
  simp only [frameLength, PiLp.norm_sq_eq_of_L2, sum_prod_type, h_coord]

/-- At each infinite place `w` let `b w` be triangular for the weight `wt` and make the columns of
`g_w⁻¹ * b w` orthonormal, with `g_w` the component of `g` at `w`. Let the rational vector `c`
vanish at the weights above `wt j`. If at every `w` the coordinates of `(b w)⁻¹ c` of weight at
most `wt j` have absolute value below `ρ > 0`, then the length `frameLength g c` (the Euclidean norm
of `g⁻¹ c` at infinity) has square below `f * card n * ρ ^ 2`, with `f` the number of infinite
places. -/
lemma frameLength_sq_lt_of_blockTriangular [Nonempty n] (g : GL n (𝔸 E)) {ι : Type*}
    [LinearOrder ι] {wt : n → ι} {b : InfinitePlace E → GL n ℂ}
    (b_tri : ∀ w : InfinitePlace E, (b w).val.BlockTriangular wt)
    (b_orth : ∀ w : InfinitePlace E,
      ((g.map (evalInf w))⁻¹.val * (b w).val)ᴴ * ((g.map (evalInf w))⁻¹.val * (b w).val) = 1)
    {c : n → E} {j : n} (h_last : ∀ k : n, c k ≠ 0 → wt k ≤ wt j) {ρ : ℝ} (hρ : 0 < ρ)
    (h_box : ∀ (w : InfinitePlace E) (l : n), wt l ≤ wt j →
      ‖((b w)⁻¹.val *ᵥ fun k : n ↦ Φ w (c k)) l‖ < ρ) :
    frameLength g c ^ 2 < numInfPlaces E * Fintype.card n * ρ ^ 2 :=
  calc frameLength g c ^ 2
      = ∑ w : InfinitePlace E, ∑ i : n,
          ‖((g.map (evalInf w))⁻¹.val *ᵥ fun k : n ↦ Φ w (c k)) i‖ ^ 2 := frameLength_sq g c
    _ < ∑ _ : InfinitePlace E, card n * ρ ^ 2 :=
        sum_lt_sum_of_nonempty univ_nonempty fun w _ ↦
          sum_norm_sq_mulVec_lt_of_blockTriangular (b_tri w) (b_orth w)
            (fun k hk ↦ h_last k (by simpa using hk)) hρ (h_box w)
    _ = numInfPlaces E * Fintype.card n * ρ ^ 2 := by simp [numInfPlaces, mul_assoc]

/-- If the columns of `A⁻¹ * b` are orthonormal, then `det A` and `det b` have the same absolute
value. -/
lemma norm_det_eq_of_orthonormal_inv_mul {A b : GL n ℂ}
    (h_orth : (A⁻¹.val * b.val)ᴴ * (A⁻¹.val * b.val) = 1) : ‖A.val.det‖ = ‖b.val.det‖ := by
  have h_norm : ‖(A⁻¹.val * b.val).det‖ = 1 :=
    CStarRing.norm_of_mem_unitary (det_of_mem_unitary (mem_unitaryGroup_iff'.2 h_orth))
  rw [← A.mul_inv_cancel_left b.val, det_mul, norm_mul, h_norm, mul_one]

/-- If the columns of `A⁻¹ * b` are orthonormal, then `det A` and `det b` have the same squared
absolute value. -/
lemma norm_det_sq_eq_of_orthonormal_inv_mul {A b : GL n ℂ}
    (h_orth : (A⁻¹.val * b.val)ᴴ * (A⁻¹.val * b.val) = 1) :
    ‖A.val.det‖ ^ 2 = ‖b.val.det‖ ^ 2 := by
  rw [norm_det_eq_of_orthonormal_inv_mul h_orth]

/-- Let `b w` make the columns of `g_w⁻¹ * b w` orthonormal at each infinite place `w`, with `g_w`
the component of `g` at `w`, and let `c ^ n * ‖det D‖ ^ 2 = ∏ j, α j ^ 2`. Then
`|det g| * ∏ j, α j ^ (2 f)` is `c ^ (f n)` times the adelic absolute value of the determinant of
the adelic matrix with the components `b w * D` at infinity and the finite part of `g`. Here `f` is
the number of infinite places and `n` stands for `card n`. -/
lemma ideleAbs_det_mul_prod_eq (g : GL n (𝔸 E)) {b : InfinitePlace E → GL n ℂ} (D : GL n ℂ)
    {c : ℝ} {α : n → ℝ}
    (h_orth : ∀ w : InfinitePlace E,
      ((g.map (evalInf w))⁻¹.val * (b w).val)ᴴ * ((g.map (evalInf w))⁻¹.val * (b w).val) = 1)
    (h_det : c ^ card n * ‖D.val.det‖ ^ 2 = ∏ j : n, α j ^ 2) :
    ideleAbs g.det * ∏ j : n, α j ^ (2 * numInfPlaces E) = c ^ (numInfPlaces E * card n) *
      ideleAbs (mkAdelicGL (fun w : InfinitePlace E ↦ b w * D,
        g.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E)))).det := by
  let g_inf (w : InfinitePlace E) : GL n ℂ := g.map (evalInf w)
  let g_fin : GL n (𝔸f E) := g.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E))
  have g_eq_mk : g = mkAdelicGL (g_inf, g_fin) := Units.ext (Matrix.ext fun i j ↦ rfl)
  have abs_det_g : ideleAbs g.det =
      (∏ w : InfinitePlace E, ‖(b w).val.det‖ ^ 2) * finIdeleAbs g_fin.det := by
    rw [← prod_congr rfl fun w _ ↦ norm_det_sq_eq_of_orthonormal_inv_mul (h_orth w),
      ← ideleAbs_det_mkAdelicGL g_inf g_fin, ← g_eq_mk]
  have abs_det_mul_D : ideleAbs (mkAdelicGL (fun w ↦ b w * D, g_fin)).det =
      (∏ w : InfinitePlace E, ‖(b w).val.det‖ ^ 2) *
        (‖D.val.det‖ ^ 2) ^ numInfPlaces E * finIdeleAbs g_fin.det := by
    simp [ideleAbs_det_mkAdelicGL, mul_pow, prod_mul_distrib, numInfPlaces]
  rw [abs_det_g, abs_det_mul_D]
  simp only [pow_mul, prod_pow, ← h_det]
  ring

/-- The volume bound from a box without nonzero lattice vectors. Let the numbers `α j > 0` increase
with the weight `wt j`. Suppose that every rational `c` in `frameLattice g` (that is, with `g⁻¹ c`
integral at the finite places) has length `frameLength g c` (the Euclidean norm of `g⁻¹ c` at
infinity) at least `α j` whenever `j` has the largest weight among the indices with `c j ≠ 0`. Then
`|det g| * ∏ j, α j ^ (2 f) ≤ (2 f n rd) ^ (f n)`, where `|det g|` is the adelic absolute value,
`f` the number of infinite places, `n` stands for `card n` and `rd` is the root discriminant. -/
lemma ideleAbs_det_mul_prod_le_of_le_frameLength (g : GL n (𝔸 E)) {ι : Type*} [LinearOrder ι]
    (wt : n → ι) {α : n → ℝ} (α_pos : ∀ j : n, 0 < α j)
    (α_mono : ∀ l j : n, wt l ≤ wt j → α l ≤ α j)
    (h_long : ∀ c ∈ frameLattice g, ∀ j : n, c j ≠ 0 → (∀ k : n, c k ≠ 0 → wt k ≤ wt j) →
      α j ≤ frameLength g c) :
    ideleAbs g.det * ∏ j : n, α j ^ (2 * numInfPlaces E) ≤
      (2 * (numInfPlaces E * Fintype.card n) * rootDiscr E) ^
        (numInfPlaces E * Fintype.card n) := by
  -- Orthonormalise the columns of `g⁻¹` in the order of `wt` at each infinite place. The box of
  -- radii `α j / √(f n)` in these bases holds no nonzero lattice vector, so Minkowski's first
  -- theorem bounds its volume.
  obtain _ | _ := isEmpty_or_nonempty n
  · simp [univ_eq_empty, ideleAbs]
  let g_fin : GL n (𝔸f E) := g.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E))
  have h_gram (w : InfinitePlace E) : ∃ b : GL n ℂ, b.val.BlockTriangular wt ∧
      ((g.map (evalInf w))⁻¹.val * b.val)ᴴ * ((g.map (evalInf w))⁻¹.val * b.val) = 1 :=
    exists_orthonormal_mul wt ⟨_, (g.map (evalInf w))⁻¹.inv_val⟩
  choose b b_tri b_orth using h_gram
  let R : ℝ := √(numInfPlaces E * card n)
  have R_pos : 0 < R := by simp [R, Fintype.card_pos]
  have R_sq : R ^ 2 = numInfPlaces E * card n := sq_sqrt (by positivity)
  let D : GL n ℂ := diagGL fun l ↦ .mk0 (α l / R : ℝ) (by simp [(α_pos l).ne', R_pos.ne'])
  let box : GL n (𝔸 E) := mkAdelicGL (fun w ↦ b w * D, g_fin)
  have box_empty (c : n → E) (hc : ∀ i : n, (box⁻¹.val *ᵥ toAdele ∘ c) i ∈ ball 0 1 ×ˢ Ô E) :
      c = 0 := by
    by_contra c_ne
    have c_box (w : InfinitePlace E) (l : n) :
        ‖((b w)⁻¹.val *ᵥ fun k ↦ Φ w (c k)) l‖ < α l / R := by
      have h_scale : ((box⁻¹.val *ᵥ toAdele ∘ c) l).1 w =
          (R / α l : ℝ) * ((b w)⁻¹.val *ᵥ fun k ↦ Φ w (c k)) l := by
        simp [box, D, ← map_inv, mkAdelicGL, mulVec, dotProduct, fst_sum, mul_sum, mul_assoc,
          -coe_units_inv]
      have h_ball : ‖((box⁻¹.val *ᵥ toAdele ∘ c) l).1 w‖ < 1 :=
        (norm_le_pi_norm _ w).trans_lt (mem_ball_zero_iff.1 (hc l).1)
      rwa [h_scale, norm_mul, Complex.norm_of_nonneg (div_pos R_pos (α_pos l)).le,
        ← lt_inv_mul_iff₀ (div_pos R_pos (α_pos l)), mul_one, inv_div] at h_ball
    have c_mem : c ∈ frameLattice g := fun i ↦ by
      simpa [box, g_fin, ← map_inv, mkAdelicGL, mulVec, dotProduct, snd_sum, -coe_units_inv]
        using (hc i).2
    -- If `j` is the last index with `c j ≠ 0`, then `c` would be shorter than `α j`.
    obtain ⟨j, hj, j_last⟩ : ∃ j : n, c j ≠ 0 ∧ ∀ k : n, c k ≠ 0 → wt k ≤ wt j :=
      c.support.exists_max_image wt Subtype.finite (by simpa using c_ne)
    have c_short : frameLength g c ^ 2 < α j ^ 2 :=
      calc frameLength g c ^ 2 < numInfPlaces E * card n * (α j / R) ^ 2 :=
            frameLength_sq_lt_of_blockTriangular g b_tri b_orth j_last (div_pos (α_pos j) R_pos)
              fun w l hl ↦ (c_box w l).trans_le (by grw [α_mono l j hl])
        _ = α j ^ 2 := by rw [← R_sq, div_pow, mul_div_cancel₀ _ (pow_pos R_pos 2).ne']
    exact (h_long c c_mem j hj j_last).not_gt (lt_of_pow_lt_pow_left₀ 2 (α_pos j).le c_short)
  have box_le : ideleAbs box.det ≤ ((2 * rootDiscr E) ^ numInfPlaces E) ^ card n :=
    le_of_not_gt fun h_large ↦
      have ⟨c, hc, c_ne⟩ := exists_ne_zero_inv_mulVec_mem box h_large
      c_ne (box_empty c hc)
  have det_D : (numInfPlaces E * card n) ^ card n * ‖D.val.det‖ ^ 2 = ∏ j : n, α j ^ 2 := by
    simp [D, ← R_sq, prod_pow, div_pow, abs_of_pos (α_pos _), abs_of_pos R_pos, ← pow_mul, field,
      mul_comm]
  calc ideleAbs g.det * ∏ j : n, α j ^ (2 * numInfPlaces E)
      = (numInfPlaces E * card n) ^ (numInfPlaces E * card n) * ideleAbs box.det :=
        ideleAbs_det_mul_prod_eq g D b_orth det_D
    _ ≤ (numInfPlaces E * card n) ^ (numInfPlaces E * card n) *
          ((2 * rootDiscr E) ^ numInfPlaces E) ^ card n := by gcongr
    _ = (2 * (numInfPlaces E * card n) * rootDiscr E) ^ (numInfPlaces E * card n) := by ring

/-- Minkowski's second theorem over `E`. For `z` in `GL n (𝔸 E)` the lattice `frameLattice z`, of
the rational `ξ` with `z⁻¹ ξ` integral at the finite places, contains a basis `y 0, …, y (n - 1)`
of `E ^ n`, ordered by length, with `|det z| * ∏ j, ‖y j‖ ^ (2 f) ≤ (2 f n rd) ^ (f n)`. Here
`‖ξ‖ = frameLength z ξ` is the Euclidean norm of `z⁻¹ ξ` at all infinite places together, `f` is
the number of infinite places, `n` stands for `card n`, `rd` is the root discriminant and
`|det z|` the adelic absolute value. Only the upper bound of the theorem is proved. -/
theorem minkowski_second_theorem (z : GL n (𝔸 E)) :
    ∃ y : Fin (Fintype.card n) → n → E,
      LinearIndependent E y ∧
      (∀ j : Fin (Fintype.card n), y j ∈ frameLattice z) ∧
      (Monotone fun j : Fin (Fintype.card n) ↦ frameLength z (y j)) ∧
      ideleAbs z.det * ∏ j : Fin (Fintype.card n), frameLength z (y j) ^ (2 * numInfPlaces E) ≤
        (2 * (numInfPlaces E * Fintype.card n) * rootDiscr E) ^
          (numInfPlaces E * Fintype.card n) := by
  -- Choose the `y j` in turn, each of least length outside the span of the earlier ones.
  obtain ⟨y, hy_mem, hy_indep, hy_least⟩ : ∃ y : Fin (card n) → n → E,
      (∀ j : Fin (card n), y j ∈ frameLattice z) ∧ LinearIndependent E y ∧
        ∀ j : Fin (card n), ∀ v ∈ frameLattice z, v ∉ Submodule.span E (y '' Set.Iio j) →
          frameLength z (y j) ≤ frameLength z v :=
    exists_successive_minima (span_frameLattice z) (frameLength z)
      (finite_frameLattice_of_frameLength_le z) (Module.finrank_fintype_fun_eq_card E).ge
  have h_mono : Monotone fun j : Fin (card n) ↦ frameLength z (y j) := fun i j hij ↦
    hy_least i (y j) (hy_mem j) (hy_indep.notMem_span_image (by simpa using hij))
  refine ⟨y, hy_indep, hy_mem, h_mono, ?_⟩
  -- Pass to coordinates in this basis: `Y` has the columns `y (e a)`, and `g = Y⁻¹ z`.
  let e : n ≃ Fin (card n) := equivFin n
  obtain ⟨Y, hY⟩ : IsUnit (of fun i a : n ↦ y (e a) i) :=
    linearIndependent_col_iff_isUnit.1 (hy_indep.comp e e.injective)
  let g : GL n (𝔸 E) := (GeneralLinearGroup.map toAdele Y)⁻¹ * z
  have h_map (c : n → E) : toAdele ∘ (Y.val *ᵥ c) = Y.val.map toAdele *ᵥ toAdele ∘ c :=
    funext fun i ↦ RingHom.map_mulVec toAdele Y.val c i
  have h_coord (c : n → E) : g⁻¹.val *ᵥ toAdele ∘ c = z⁻¹.val *ᵥ toAdele ∘ (Y.val *ᵥ c) := by
    simp [g, h_map]
  have h_abs : ideleAbs z.det = ideleAbs g.det := by simp [g]
  rw [h_abs, ← e.prod_comp]
  refine ideleAbs_det_mul_prod_le_of_le_frameLength g e
    (fun a ↦ frameLength_pos z (hy_indep.ne_zero (e a))) (fun _ _ h_le ↦ h_mono h_le)
    fun c hc j hj j_last ↦ ?_
  -- The lattice vector `Y c` lies outside the span of the `y i` with `i < e j`, as `c j ≠ 0`.
  have h_mem : Y.val *ᵥ c ∈ frameLattice z := by
    simpa only [frameLattice, Set.mem_ofPred_eq, h_coord] using hc
  have h_out : Y.val *ᵥ c ∉ Submodule.span E (y '' Set.Iio (e j)) := by
    have h_earlier : ∑ k ∈ univ.erase j, c k • y (e k) ∈ Submodule.span E (y '' Set.Iio (e j)) := by
      refine Submodule.sum_mem _ fun k hk ↦ ?_
      obtain h_zero | h_ne := eq_or_ne (c k) 0
      · simp [h_zero]
      have h_lt : e k < e j := (j_last k h_ne).lt_of_ne (by simpa using hk)
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e k, h_lt, rfl⟩)
    have h_sum : Y.val *ᵥ c = c j • y (e j) + ∑ k ∈ univ.erase j, c k • y (e k) := by
      rw [add_sum_erase _ (fun k ↦ c k • y (e k)) (mem_univ j)]
      ext i
      simp [hY, mulVec, dotProduct, mul_comm]
    rw [h_sum, Submodule.add_mem_iff_left _ h_earlier, Submodule.smul_mem_iff _ hj]
    exact hy_indep.notMem_span_image (by simp)
  simpa only [frameLength, h_coord] using hy_least (e j) _ h_mem h_out

/-- Minkowski's second theorem with dyadic bounds. For `y` in `GL n (𝔸 E)` there are an invertible
matrix `Y` over `E` and integers `x j` such that each row `Y j` lies in `frameLattice y` (the
vectors `ξ ∈ Eⁿ` with `y⁻¹ ξ` integral at all finite places) and has `frameLength` at most
`2 ^ x j`, and `|det y| * (2 ^ (2 f)) ^ ∑ j, x j ≤ (8 f n rd) ^ (f n)`. Here `frameLength y ξ` is
the Euclidean norm of the coordinates of `y⁻¹ ξ` at all infinite places together, `f` is the number
of infinite places, `n` stands for `card n`, `rd` is the root discriminant and `|det y|` is the
adelic absolute value. -/
theorem _root_.New.exists_basis_frameLength_le_two_zpow (y : GL n (𝔸 E)) :
    ∃ (Y : Matrix n n E) (x : n → ℤ),
      Y.det ≠ 0 ∧
      (∀ j : n, Y j ∈ frameLattice y) ∧
      (∀ j : n, frameLength y (Y j) ≤ 2 ^ x j) ∧
      ideleAbs y.det * (2 ^ (2 * numInfPlaces E)) ^ ∑ j : n, x j ≤
        (8 * (numInfPlaces E * Fintype.card n) * rootDiscr E) ^
          (numInfPlaces E * Fintype.card n) := by
  -- Round the lengths of the basis of `minkowski_second_theorem` up to powers of `2`; this
  -- at most doubles each of them.
  obtain ⟨v, h_indep, h_mem, -, h_prod⟩ := minkowski_second_theorem y
  let e : n ≃ Fin (card n) := equivFin n
  let len (j : n) : ℝ := frameLength y (v (e j))
  have len_pos (j : n) : 0 < len j := frameLength_pos y (h_indep.ne_zero (e j))
  have pow_le (j : n) : (2 : ℝ) ^ clog 2 (len j) ≤ 2 * len j := by
    have h_lt : (2 : ℝ) ^ (clog 2 (len j) - 1) < len j :=
      mod_cast zpow_pred_clog_lt_self one_lt_two (len_pos j)
    rw [zpow_sub_one₀ two_ne_zero] at h_lt
    linarith
  have h_det : det (of fun j ↦ v (e j)) ≠ 0 := ((isUnit_iff_isUnit_det _).1
    (linearIndependent_row_iff_isUnit.1 (h_indep.comp e e.injective))).ne_zero
  refine ⟨of fun j ↦ v (e j), fun j ↦ clog 2 (len j), h_det, fun j ↦ h_mem (e j),
    fun j ↦ mod_cast self_le_zpow_clog one_lt_two (len j), ?_⟩
  set f : ℕ := numInfPlaces E
  calc ideleAbs y.det * (2 ^ (2 * f)) ^ ∑ j : n, clog 2 (len j)
      = ideleAbs y.det * ∏ j : n, ((2 : ℝ) ^ clog 2 (len j)) ^ (2 * f) := by
        rw [prod_pow, ← DiscreteSeries.zpow_sum_of_ne_zero two_ne_zero, ← zpow_natCast,
          ← zpow_natCast, zpow_comm]
    _ ≤ ideleAbs y.det * ∏ j : n, (2 * len j) ^ (2 * f) := by
        gcongr with j
        exacts [ideleAbs_pos.le, pow_le j]
    _ = 4 ^ (f * card n) * (ideleAbs y.det * ∏ j, frameLength y (v j) ^ (2 * f)) := by
        simp only [mul_pow, prod_mul_distrib, prod_const, card_univ, len, ← e.prod_comp]
        rw [pow_mul 2, ← pow_mul]
        ring
    _ ≤ 4 ^ (f * card n) * (2 * (f * card n) * rootDiscr E) ^ (f * card n) := by gcongr
    _ = (8 * (f * card n) * rootDiscr E) ^ (f * card n) := by rw [← mul_pow]; ring

open MeasureTheory ENNReal Set

/-! ### Counting rational points -/

/-- The sum over all tuples `x : n → α` of the product of the `f (x i)` is at most the product over
`n` of the sums of `f`. -/
lemma tsum_prod_le_prod_tsum {α : Type*} (f : α → ℝ≥0∞) :
    ∑' x : n → α, ∏ i : n, f (x i) ≤ ∏ _ : n, tsum f := by
  classical
  refine tsum_le_of_sum_le' bot_le fun s ↦ ?_
  -- a finite set of tuples lies in the product of its projections, over which the sum factors
  have h_sub : s ⊆ piFinset (fun i ↦ s.image (eval i)) := fun x hx ↦
    mem_piFinset.2 fun i ↦ mem_image_of_mem (eval i) hx
  grw [h_sub, ← prod_univ_sum, ENNReal.sum_le_tsum]

open Pointwise in
/-- Let `box` be the set of adelic vectors with entries of size at most `1` at infinity and
integral at the finite places, and let `t = twoAtInfinity E` be the idele that is `2` at infinity
and `1` at the finite places. If the vector of the `t ^ (-x i) * u i` lies in `B` and `v` lies in
`F`, then `u + v` multiplied by the inverse of the diagonal matrix of the `t ^ max (x i) 0` lies in
`box * B + box * F`. -/
lemma dyadicDiag_toNat_inv_mulVec_add_mem {B F : Set (n → 𝔸 E)} (x : n → ℤ) {u v : n → 𝔸 E}
    (hu : (fun i : n ↦ (twoAtInfinity E ^ (-x i)).val * u i) ∈ B) (hv : v ∈ F) :
    (dyadicDiag fun i : n ↦ ((x i).toNat : ℤ))⁻¹.val *ᵥ (u + v) ∈
      (univ.pi fun _ : n ↦ (closedBall 0 1 ×ˢ Ô E : Set (𝔸 E))) * B +
        (univ.pi fun _ : n ↦ (closedBall 0 1 ×ˢ Ô E : Set (𝔸 E))) * F := by
  -- nonpositive powers of `twoAtInfinity E` lie in the box, and `-x⁺ = (-x⁺ + x) - x`
  set box : Set (n → 𝔸 E) := univ.pi fun _ ↦ closedBall 0 1 ×ˢ Ô E
  have pow_mem (m : n → ℤ) (hm : m ≤ 0) : (fun i ↦ (twoAtInfinity E ^ m i).val) ∈ box := by
    simpa [box, field, twoAtInfinity, ← map_zpow, Pi.le_def] using hm
  have h_eq : (dyadicDiag fun i ↦ ((x i).toNat : ℤ))⁻¹.val *ᵥ (u + v) =
      (fun i ↦ (twoAtInfinity E ^ (-x⁺ + x) i).val) *
          (fun i ↦ (twoAtInfinity E ^ (-x i)).val * u i) +
        (fun i ↦ (twoAtInfinity E ^ (-x⁺) i).val) * v := by
    ext1 i
    simp only [dyadicDiag_inv_mulVec_apply, show ((x i).toNat : ℤ) = x⁺ i by simp [posPart],
      Pi.add_apply, Pi.mul_apply, Pi.neg_apply, ← mul_assoc, ← Units.val_mul, ← _root_.zpow_add,
      add_neg_cancel_right, mul_add]
  rw [h_eq]
  exact Set.add_mem_add (Set.mul_mem_mul (pow_mem _ (neg_add_nonpos_iff.2 (le_posPart x))) hu)
    (Set.mul_mem_mul (pow_mem _ (neg_nonpos.2 (posPart_nonneg x))) hv)

open Pointwise in
/-- Counting rational points in a box. For a compact set `B` of adelic vectors there is a finite `C`
with the following property. For every `x : n → ℤ`, let `f a` (`a ∈ S`) be a family of distinct
rational vectors such that the vector with entries `twoAtInfinity E ^ (-x i) * f a i` lies in `B`
for every `a`, where `twoAtInfinity E` is the idele that is `2` at infinity and `1` at the finite
places. Then the family has at most `C * ((2 ^ r) ^ ∑ i, max (x i) 0) ^ 2` members, with
`r = numInfPlaces E` the number of infinite places. -/
lemma encard_le_of_dyadic_box {α : Type*} {B : Set (n → 𝔸 E)} (hB : IsCompact B) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (x : n → ℤ) {S : Set α} (f : α → n → E),
        (h_inj : InjOn f S) →
        (h_mem : ∀ a ∈ S, (fun i : n ↦ (twoAtInfinity E ^ (-x i)).val * toAdele (f a i)) ∈ B) →
        S.encard ≤ C * ENNReal.ofReal (((2 ^ numInfPlaces E) ^ ∑ i : n, (x i).toNat) ^ 2) := by
  -- Let `F` be a compact set into which every `v` is moved by a rational vector. Translate the
  -- points `f a` so that all land in `D K`, with `K = box * B + box * F` and `D = dyadicDiag x⁺`,
  -- and count the rational points there on average (`lintegral_encard_rat_points`).
  obtain ⟨F, hF, h_move⟩ := IsCovolOneLattice.exists_compact_cover (ratVectors E n)
  let box : Set (n → 𝔸 E) := univ.pi fun _ ↦ closedBall 0 1 ×ˢ Ô E
  let K : Set (n → 𝔸 E) := box * B + box * F
  have hK : IsCompact K :=
    have h_box := isCompact_univ_pi fun _ ↦ isCompact_closedBall_prod_integral
    (h_box.mul hB).add (h_box.mul hF)
  refine ⟨volume K, hK.measure_ne_top, fun x S f h_inj h_mem ↦ ?_⟩
  let D : GL n (𝔸 E) := dyadicDiag fun i ↦ ((x i).toNat : ℤ)
  -- for each shift `v`, add to the points `f a` the rational vector `ξ` that moves `v` into `F`
  have h_count (v : n → 𝔸 E) :
      S.encard ≤ {η : n → E | D⁻¹.val *ᵥ (toAdele ∘ η + v) ∈ K}.encard := by
    obtain ⟨r, ⟨ξ, rfl⟩, hξ : toAdele ∘ ξ + v ∈ F⟩ := h_move v
    refine encard_le_encard_of_injOn (f := fun a ↦ f a + ξ) (fun a ha ↦ ?_)
      ((add_left_injective ξ).comp_injOn h_inj)
    have h_add : toAdele ∘ (f a + ξ) + v = toAdele ∘ f a + (toAdele ∘ ξ + v) := by
      simp [add_assoc]
    rw [mem_ofPred_eq, h_add]
    exact dyadicDiag_toNat_inv_mulVec_add_mem x (h_mem a ha) hξ
  -- the mean of these counts over `v` is `|det D| * volume K`
  rw [mul_comm (volume K), ← ideleAbs_det_dyadicDiag_natCast,
    lintegral_encard_rat_points D hK.measurableSet]
  exact (le_iInf fun v ↦ mod_cast h_count v).trans (iInf_le_lintegral _)

end New.Core

end MinkowskiSecond

/-! ## Rational elements scaled into a compact set of adeles -/

open Pointwise in
/-- For a compact set `B` of adeles there is an integer `c` such that, for every integer `e < c`, an
element `a` of `E` (embedded diagonally by `toAdele`) that lies in `B` after multiplication by
`2 ^ (-e)` at the infinite places, that is by `twoAtInfinity E ^ (-e)`, is zero. -/
lemma New.Core.exists_eq_zero_of_zpow_mul_mem {E : Type*} [Field E] [CMType E] {B : Set (𝔸 E)}
    (hB : IsCompact B) :
    ∃ c : ℤ, ∀ e : ℤ, e < c → ∀ {a : E},
      (twoAtInfinity E ^ (-e)).val * toAdele a ∈ B → a = 0 := by
  -- The set `F` of rational points of `box * B` is finite, so some `N : ℕ` is not a quotient of two
  -- of its elements. But for `e < -N` both `N * a` and `a` lie in `F`, which forces `a = 0`.
  let box : Set (𝔸 E) := Metric.closedBall 0 1 ×ˢ Ô E
  let F : Set E := {x | toAdele x ∈ box * B}
  have F_finite : F.Finite :=
    finite_setOf_toAdele_mem (isCompact_closedBall_prod_integral.mul hB)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : E) ∉ F / F :=
    ((F_finite.div F_finite).preimage_embedding Nat.castEmbedding).exists_notMem
  refine ⟨-N, fun e he a ha ↦ by_contra fun ha_ne ↦ ?_⟩
  have h_multiple (k : ℕ) (hk : k * (2 : ℝ) ^ e ≤ 1) : k * a ∈ F := by
    have h_box : k * (twoAtInfinity E ^ e).val ∈ box := by
      simpa [box, twoAtInfinity, ← map_zpow, Pi.mul_def] using hk
    -- `toAdele (k * a) = (k * 2 ^ e) * (2 ^ (-e) * a)`
    simpa [F, mul_assoc] using Set.mul_mem_mul h_box ha
  have h_scale : (N : ℝ) * 2 ^ e ≤ 2 ^ N * 2 ^ (-N : ℤ) := by
    gcongr
    exacts [mod_cast N.lt_two_pow_self.le, one_le_two]
  have h_one : (2 : ℝ) ^ e ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by lia)
  have ha_mem : a ∈ F := by simpa using h_multiple 1 (by simpa using h_one)
  exact hN ⟨N * a, h_multiple N (by simpa using h_scale), a, ha_mem,
    mul_div_cancel_right₀ (N : E) ha_ne⟩

end
