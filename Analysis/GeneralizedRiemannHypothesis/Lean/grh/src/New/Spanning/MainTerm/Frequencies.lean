import Lib.ClassField.HeckeL.EulerProduct
import Lib.General.Analysis.PackingAndSobolev

/-!
# Sums over frequencies

The frequencies are the elements `ν` of a totally complex number field `E`. If `E` has `f` infinite
places, the sum of `∏_v [ν]_v ^ (-3)` over any finite subset of `E` is at most `C ^ f` with
`C = 64 * 38 * e ^ 4`. At an infinite place `[ν]_v` is `(max 1 |ν|_v) ^ 2`, with `|ν|_v` the usual
absolute value, and the finite places together give the norm of the denominator of `ν`. The numbers
with a given denominator `𝔟` lie in `N 𝔟` cosets of the ring of integers, each coset is counted by
small squares, and the sum over `𝔟` is at most the value at `2` of the Dedekind zeta function.

Notions from other files:
* `Φ v`: the chosen complex embedding of `E` that induces the infinite place `v`
  (`PlaceEmbedding E`).
-/

open NumberField Finset

noncomputable section

namespace New

variable {E : Type} [Field E] [NumberField E]

/-- The denominator of `ν`: the ideal of the integers `a` such that `a ν` is integral. -/
def denominator (ν : E) : Ideal (𝓞 E) where
  carrier := {a : 𝓞 E | IsIntegral ℤ (algebraMap (𝓞 E) E a * ν)}
  zero_mem' := by simpa using isIntegral_zero
  add_mem' ha hb := by simpa [add_mul] using IsIntegral.add ha hb
  smul_mem' c a ha := by simpa [mul_assoc] using IsIntegral.mul c.isIntegral_coe ha

omit [NumberField E] in
lemma mem_denominator {ν : E} {a : 𝓞 E} :
    a ∈ denominator ν ↔ IsIntegral ℤ (algebraMap (𝓞 E) E a * ν) :=
  Iff.rfl

lemma denominator_ne_bot (ν : E) : denominator ν ≠ ⊥ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) ν
  refine (Submodule.ne_bot_iff _).2 ⟨b, ?_, nonZeroDivisors.ne_zero hb⟩
  simpa [mem_denominator, mul_div_cancel₀, nonZeroDivisors.ne_zero hb] using a.isIntegral_coe

/-- Suppose that `(a) = 𝔟 𝔠` with `𝔟 ≠ 0` and that `r ν` is integral for all `r ∈ 𝔟`, that is,
`𝔟 ≤ denominator ν`. Then `a ν` is an integer in `𝔠`. -/
lemma exists_mem_algebraMap_eq_mul {a : 𝓞 E} {𝔟 𝔠 : Ideal (𝓞 E)} (h𝔟 : 𝔟 ≠ ⊥)
    (h𝔠 : Ideal.span {a} = 𝔟 * 𝔠) {ν : E} (hν : 𝔟 ≤ denominator ν) :
    ∃ x : 𝔠, algebraMap (𝓞 E) E (x : 𝓞 E) = algebraMap (𝓞 E) E a * ν := by
  have h_lift (r : 𝓞 E) (hr : r ∈ 𝔟) :
      ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = algebraMap (𝓞 E) E r * ν :=
    ⟨⟨_, mem_denominator.1 (hν hr)⟩, rfl⟩
  have ha : a ∈ 𝔟 := Ideal.dvd_span_singleton.1 ⟨𝔠, h𝔠⟩
  obtain ⟨x, hx⟩ := h_lift a ha
  have h_le : 𝔟 * Ideal.span {x} ≤ 𝔟 * 𝔠 := by
    rw [← h𝔠, mul_comm, Ideal.span_singleton_mul_le_iff]
    intro r hr
    obtain ⟨y, hy⟩ := h_lift r hr
    have h_eq : y * a = x * r := RingOfIntegers.coe_injective <| by
      simp only [map_mul, hx, hy]
      ring
    exact Ideal.mem_span_singleton'.2 ⟨y, h_eq⟩
  have h_dvd : 𝔠 ∣ Ideal.span {x} := (mul_dvd_mul_iff_left h𝔟).1 (Ideal.dvd_iff_le.2 h_le)
  exact ⟨⟨x, Ideal.dvd_span_singleton.1 h_dvd⟩, hx⟩

/-- For a nonzero ideal `𝔟`, the numbers `ν` whose denominator (the ideal of the integers `a`
with `a ν` integral) contains `𝔟` can be given `N 𝔟` labels so that two numbers with the same
label differ by an algebraic integer. -/
lemma exists_coset_label {𝔟 : Ideal (𝓞 E)} (h𝔟 : 𝔟 ≠ ⊥) :
    ∃ label : E → Fin (Ideal.absNorm 𝔟), ∀ ν ν' : E,
      𝔟 ≤ denominator ν → 𝔟 ≤ denominator ν' → label ν = label ν' → IsIntegral ℤ (ν - ν') := by
  -- Write `(a) = 𝔟 𝔠` with `a ≠ 0`. Multiplication by `a` maps these numbers into `𝔠` and the
  -- integers onto `(a)`, and `𝔠 / (a)` has `N 𝔟` elements.
  obtain ⟨a, ha, ha_ne⟩ := (Submodule.ne_bot_iff 𝔟).1 h𝔟
  obtain ⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {a} := Ideal.dvd_span_singleton.2 ha
  have h_mul (ν : E) (hν : 𝔟 ≤ denominator ν) :
      ∃ x : 𝔠, algebraMap (𝓞 E) E (x : 𝓞 E) = algebraMap (𝓞 E) E a * ν :=
    exists_mem_algebraMap_eq_mul h𝔟 h𝔠 hν
  choose! x hx using h_mul
  let A : AddSubgroup 𝔠 := (Ideal.span {a}).toAddSubgroup.addSubgroupOf 𝔠.toAddSubgroup
  have h_index : A.index = Ideal.absNorm 𝔟 := by
    -- the norm of an ideal is the index of its additive group
    have h_tower : A.index * Ideal.absNorm 𝔠 = Ideal.absNorm (Ideal.span {a}) := by
      rw [Ideal.absNorm_apply, Ideal.absNorm_apply]
      exact AddSubgroup.relIndex_mul_index (h𝔠.trans_le Ideal.mul_le_right)
    have h𝔠_ne : 𝔠 ≠ ⊥ := fun h_bot ↦ ha_ne (by simpa [h_bot] using h𝔠)
    simpa [h𝔠, Ideal.absNorm_eq_zero_iff, h𝔠_ne] using h_tower
  have : Finite (𝔠 ⧸ A) := AddSubgroup.index_ne_zero_iff_finite.1 <| by
    rwa [h_index, Ne, Ideal.absNorm_eq_zero_iff]
  let e : 𝔠 ⧸ A ≃ Fin (Ideal.absNorm 𝔟) := Finite.equivFinOfCardEq h_index
  refine ⟨fun ν : E ↦ e (QuotientAddGroup.mk (x ν)), fun ν ν' hν hν' h_label ↦ ?_⟩
  have h_mem : x ν - x ν' ∈ A := QuotientAddGroup.eq_iff_sub_mem.1 (e.injective h_label)
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 E, t * a = x ν - x ν' :=
    Ideal.mem_span_singleton'.1 (AddSubgroup.mem_addSubgroupOf.1 h_mem)
  have h_eq : algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E a * (ν - ν') := by
    rw [mul_comm, ← map_mul, ht, map_sub, hx ν hν, hx ν' hν', mul_sub]
  rw [← mul_left_cancel₀ (by simpa using ha_ne) h_eq]
  exact t.isIntegral_coe

/-- The sum of `Ideal.absNorm 𝔟 ^ (-2)` over a finite set `s` of ideals of the ring of integers of
`E` is at most `exp (2 [E : ℚ])`, where `[E : ℚ] = Module.finrank ℚ E`: it is at most the value at
`2` of the Euler product with all coefficients equal to `1`, that is `ζ_E(2)`. -/
lemma sum_absNorm_inv_sq_le (s : Finset (Ideal (𝓞 E))) :
    ∑ 𝔟 ∈ s, (Ideal.absNorm 𝔟 : ℝ)⁻¹ ^ 2 ≤ Real.exp (2 * Module.finrank ℚ E) := by
  let ζ : ℂ := eulerProd (fun _ : FinPlace E ↦ 1) 2
  have h_sum : HasSum (fun 𝔟 : Ideal (𝓞 E) ↦ (Ideal.absNorm 𝔟 : ℝ)⁻¹ ^ 2) ζ.re := by
    have h_euler : HasSum (fun 𝔟 : Ideal (𝓞 E) ↦ (Ideal.absNorm 𝔟 : ℂ) ^ (-2 : ℂ)) ζ := by
      simpa using hasSum_eulerProd (K := E) (s := 2) 1 (by simp) (by simp)
    refine (Complex.hasSum_re h_euler).congr_fun fun 𝔟 ↦ ?_
    simp [Complex.cpow_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  have h_log : Real.log ‖ζ‖ ≤ 2 * Module.finrank ℚ E := by
    obtain ⟨-, h_abs⟩ : ζ ≠ 0 ∧ |Real.log ‖ζ‖| ≤ 2 * Module.finrank ℚ E * 2 ^ (2 - 2 : ℝ) :=
      eulerProd_ne_zero_and_abs_log_norm_le (s := 2) (by simp) le_rfl le_rfl
    simpa using le_of_abs_le h_abs
  calc _ ≤ ζ.re := sum_le_hasSum s (fun _ _ ↦ by positivity) h_sum
    _ ≤ ‖ζ‖ := Complex.re_le_norm ζ
    _ ≤ _ := Real.le_exp_of_log_le h_log

/-- The lower left corner `m.1 / 2 + (m.2 / 2) * I` of the square of side `1 / 2` with index
`m`. -/
def squareCorner (m : ℤ × ℤ) : ℂ := ⟨m.1 / 2, m.2 / 2⟩

/-- The index `(⌊2 * z.re⌋, ⌊2 * z.im⌋)` of the square of side `1 / 2` that contains `z`. The
square with index `(a, b)` is `[a / 2, (a + 1) / 2) × [b / 2, (b + 1) / 2)`. -/
def squareIndex (z : ℂ) : ℤ × ℤ := (⌊2 * z.re⌋, ⌊2 * z.im⌋)

lemma norm_lt_one_of_abs_lt {z : ℂ} (h_re : |z.re| < 1 / 2) (h_im : |z.im| < 1 / 2) : ‖z‖ < 1 := by
  linarith [Complex.norm_le_abs_re_add_abs_im z]

/-- If `z` and `w` have the same index `squareIndex z = (⌊2 * z.re⌋, ⌊2 * z.im⌋)`, that is, if they
lie in the same half-open square `[a / 2, (a + 1) / 2) × [b / 2, (b + 1) / 2)` with `a` and `b`
integers, then their distance is less than one. -/
lemma norm_sub_lt_one_of_squareIndex_eq {z w : ℂ} (h_index : squareIndex z = squareIndex w) :
    ‖z - w‖ < 1 := by
  obtain ⟨h_re, h_im⟩ : ⌊2 * z.re⌋ = ⌊2 * w.re⌋ ∧ ⌊2 * z.im⌋ = ⌊2 * w.im⌋ := by
    simpa [squareIndex] using h_index
  have h_half {a b : ℝ} (h_floor : ⌊2 * a⌋ = ⌊2 * b⌋) : |a - b| < 1 / 2 := by
    have h_double : |2 * a - 2 * b| < 1 := Int.abs_sub_lt_one_of_floor_eq_floor h_floor
    rw [← mul_sub, abs_mul, abs_two] at h_double
    linarith
  exact norm_lt_one_of_abs_lt (by simpa using h_half h_re) (by simpa using h_half h_im)

/-- The corner `squareCorner m = m.1 / 2 + (m.2 / 2) * I` lies in the square with index `m`, where
`squareIndex z = (⌊2 * z.re⌋, ⌊2 * z.im⌋)`. -/
lemma squareIndex_squareCorner (m : ℤ × ℤ) : squareIndex (squareCorner m) = m := by
  simp [squareIndex, squareCorner, mul_div_cancel₀]

/-- The weight `(max 1 ‖z‖)⁻¹ ^ 6` of a complex number `z` is at most `64` times the weight of the
lower left corner of the square of side `1 / 2` that contains `z`. -/
lemma weight_le_weight_corner (z : ℂ) :
    (max 1 ‖z‖)⁻¹ ^ 6 ≤ 64 * (max 1 ‖squareCorner (squareIndex z)‖)⁻¹ ^ 6 := by
  have h_near : ‖squareCorner (squareIndex z) - z‖ < 1 :=
    norm_sub_lt_one_of_squareIndex_eq (squareIndex_squareCorner _)
  have h_le : max 1 ‖squareCorner (squareIndex z)‖ ≤ 2 * max 1 ‖z‖ := by
    have h_sub : ‖squareCorner (squareIndex z)‖ - ‖z‖ ≤ ‖squareCorner (squareIndex z) - z‖ :=
      norm_sub_norm_le _ _
    have h_one : 1 ≤ max 1 ‖z‖ := le_max_left 1 ‖z‖
    have h_norm : ‖z‖ ≤ max 1 ‖z‖ := le_max_right 1 ‖z‖
    exact max_le (by linarith) (by linarith)
  calc _ = 64 * (2 * max 1 ‖z‖)⁻¹ ^ 6 := by ring
    _ ≤ _ := by gcongr

/-- For distinct index pairs `m ≠ m'` in `ℤ × ℤ`, the grid corners
`squareCorner m = m.1 / 2 + (m.2 / 2) * I` and `squareCorner m'` have distance at least `1 / 2`. -/
lemma pairwise_half_le_norm_squareCorner_sub :
    Pairwise fun m m' : ℤ × ℤ ↦ 1 / 2 ≤ ‖squareCorner m - squareCorner m'‖ := by
  intro m m' h_ne
  by_contra! h_lt
  have h_eq {a b : ℤ} (h_half : |(a : ℝ) / 2 - b / 2| < 1 / 2) : a = b := by
    rw [← sub_div, abs_div, abs_two, div_lt_div_iff_of_pos_right two_pos] at h_half
    exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 (mod_cast h_half))
  refine h_ne (Prod.ext (h_eq ?_) (h_eq ?_))
  · simpa [squareCorner] using (Complex.abs_re_le_norm _).trans_lt h_lt
  · simpa [squareCorner] using (Complex.abs_im_le_norm _).trans_lt h_lt

/-- Over any finitely many indices `m`, the weights `(max 1 ‖z‖)⁻¹ ^ 6` at the grid points
`z = squareCorner m = m.1 / 2 + (m.2 / 2) * I` add up to at most `38`. -/
lemma sum_weight_corner_le (s : Finset (ℤ × ℤ)) :
    ∑ m ∈ s, (max 1 ‖squareCorner m‖)⁻¹ ^ 6 ≤ 38 := by
  -- Distinct corners have distance at least `1 / 2`, so the packing bound for separated points
  -- applies to the sum over all corners.
  let u (m : ℤ × ℤ) : ℝ := max 1 ‖squareCorner m‖
  obtain ⟨h_summable, h_tsum⟩ : Summable (fun m : ℤ × ℤ ↦ u m ^ (-6 : ℝ)) ∧
      ∑' m : ℤ × ℤ, u m ^ (-6 : ℝ) ≤ (1 + 2 * 1 / (1 / 2)) ^ Module.finrank ℝ ℂ * (3 / 2) :=
    tsum_le_of_separated (hf := pairwise_half_le_norm_squareCorner_sub) (hm := one_half_pos)
      (hR := zero_le_one) (hu_one := by simp [u]) (hu := by simp [u]) (hA := by norm_num)
      (hc := by norm_num)
  calc _ = ∑ m ∈ s, u m ^ (-6 : ℝ) := by simp [u, Real.rpow_neg_ofNat]
    _ ≤ ∑' m : ℤ × ℤ, u m ^ (-6 : ℝ) := h_summable.sum_le_tsum s fun _ _ ↦ by positivity
    _ ≤ (1 + 2 * 1 / (1 / 2)) ^ Module.finrank ℝ ℂ * (3 / 2) := h_tsum
    _ ≤ 38 := by norm_num

variable [PlaceEmbedding E]

/-- Let `X` be a finite subset of a totally complex field `E` any two elements of which differ by
an algebraic integer. Then the sum over `ν ∈ X` of the archimedean weights
`∏_v (max 1 ‖Φ v ν‖)⁻¹ ^ 6` is at most `(64 * 38) ^ f`, where `Φ v` is the chosen embedding at `v`
and `f` is the number of infinite places. -/
lemma sum_coset_weight_le [IsTotallyComplex E] {X : Finset E}
    (hX : ∀ ν ∈ X, ∀ ν' ∈ X, IsIntegral ℤ (ν - ν')) :
    ∑ ν ∈ X, ∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6 ≤ (64 * 38) ^ Core.numInfPlaces E := by
  -- A product of squares of side `1 / 2` holds at most one point of `X`, since the product of the
  -- absolute values of a nonzero algebraic integer is at least one. So the sum is at most a
  -- product of sums over squares.
  let cell (ν : E) (v : InfinitePlace E) : ℤ × ℤ := squareIndex (Φ v ν)
  let w (m : ℤ × ℤ) : ℝ := 64 * (max 1 ‖squareCorner m‖)⁻¹ ^ 6
  have h_inj : Set.InjOn cell X := by
    intro ν hν ν' hν' h_cell
    by_contra h_ne
    have h_lt : ∏ v : InfinitePlace E, ‖Φ v (ν - ν')‖ < ∏ _ : InfinitePlace E, 1 :=
      prod_lt_prod_of_nonempty₀ (fun v _ ↦ by simpa [sub_ne_zero] using (Φ v).injective.ne h_ne)
        (fun v _ ↦ by simpa using norm_sub_lt_one_of_squareIndex_eq (congrFun h_cell v))
        univ_nonempty
    exact (one_le_prod_norm_Φ (hX ν hν ν' hν') (sub_ne_zero.2 h_ne)).not_gt (by simpa using h_lt)
  let cells (v : InfinitePlace E) : Finset (ℤ × ℤ) := X.image fun ν : E ↦ cell ν v
  calc
    _ ≤ ∑ ν ∈ X, ∏ v : InfinitePlace E, w (cell ν v) := by grw [weight_le_weight_corner]
    _ = ∑ c ∈ X.image cell, ∏ v : InfinitePlace E, w (c v) := by rw [sum_image h_inj]
    _ ≤ ∑ c ∈ Fintype.piFinset cells, ∏ v : InfinitePlace E, w (c v) := by
      gcongr
      exact image_subset_iff.2 fun ν hν ↦ Fintype.mem_piFinset.2 fun v ↦ mem_image_of_mem _ hν
    _ = ∏ v : InfinitePlace E, ∑ m ∈ cells v, w m := (prod_univ_sum cells fun _ ↦ w).symm
    _ ≤ ∏ _ : InfinitePlace E, (64 * 38 : ℝ) := by
      gcongr with v
      grw [← mul_sum, sum_weight_corner_le]
    _ = _ := by simp

/-- Let `X` be a finite subset of a totally complex field `E`. The archimedean weights
`∏_v (max 1 ‖Φ v ν‖)⁻¹ ^ 6` of those `ν ∈ X` with a given nonzero denominator `𝔟` add up to at most
`Ideal.absNorm 𝔟 * (64 * 38) ^ Core.numInfPlaces E`, as these `ν` lie in at most `Ideal.absNorm 𝔟`
cosets of the integers. -/
lemma sum_weight_filter_denominator_eq_le [IsTotallyComplex E] [DecidableEq (Ideal (𝓞 E))]
    (X : Finset E) {𝔟 : Ideal (𝓞 E)} (h𝔟 : 𝔟 ≠ ⊥) :
    ∑ ν ∈ X with denominator ν = 𝔟, ∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6 ≤
      Ideal.absNorm 𝔟 * (64 * 38) ^ Core.numInfPlaces E := by
  obtain ⟨label, h_label⟩ : ∃ label : E → Fin (Ideal.absNorm 𝔟), ∀ ν ν' : E,
      𝔟 ≤ denominator ν → 𝔟 ≤ denominator ν' → label ν = label ν' → IsIntegral ℤ (ν - ν') :=
    exists_coset_label h𝔟
  calc
    _ = ∑ k : Fin (Ideal.absNorm 𝔟), ∑ ν ∈ {ν ∈ X | denominator ν = 𝔟} with label ν = k,
          ∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6 := by rw [sum_fiberwise]
    _ ≤ ∑ _ : Fin (Ideal.absNorm 𝔟), (64 * 38 : ℝ) ^ Core.numInfPlaces E := by
      -- numbers with denominator `𝔟` and the same label differ by an integer
      refine sum_le_sum fun k _ ↦ sum_coset_weight_le fun ν hν ν' hν' ↦ ?_
      simp only [mem_filter] at hν hν'
      obtain ⟨⟨-, h_den⟩, h_class⟩ := hν
      obtain ⟨⟨-, h_den'⟩, h_class'⟩ := hν'
      exact h_label ν ν' h_den.ge h_den'.ge (h_class.trans h_class'.symm)
    _ = _ := by simp

/-- Let `E` be a totally complex number field with `f = Core.numInfPlaces E` infinite places. For a
finite set `X ⊂ E`, the sum of `∏_v [ν]_v ^ (-3)` over `ν ∈ X` is at most
`(64 * 38 * e ^ 4) ^ f`. -/
theorem sum_height_inv_cube_le [IsTotallyComplex E] (X : Finset E) :
    ∑ ν ∈ X, (∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6) *
      (Ideal.absNorm (denominator ν) : ℝ)⁻¹ ^ 3 ≤
      (64 * 38 * Real.exp 4) ^ Core.numInfPlaces E := by
  classical
  -- Group the numbers by denominator. Those with denominator `𝔟` give at most `N 𝔟` sums over
  -- cosets, and what remains is the sum of `N 𝔟 ^ (-2)`.
  calc
    _ = ∑ 𝔟 ∈ X.image denominator, (∑ ν ∈ X with denominator ν = 𝔟,
          ∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6) * (Ideal.absNorm 𝔟 : ℝ)⁻¹ ^ 3 := by
      rw [← sum_fiberwise_of_maps_to fun ν hν ↦ mem_image_of_mem denominator hν]
      simp_rw [sum_mul]
      exact sum_congr rfl fun 𝔟 _ ↦ sum_congr rfl fun ν hν ↦ by rw [(mem_filter.1 hν).2]
    _ ≤ ∑ 𝔟 ∈ X.image denominator,
          (64 * 38) ^ Core.numInfPlaces E * (Ideal.absNorm 𝔟 : ℝ)⁻¹ ^ 2 := by
      refine sum_le_sum (forall_mem_image.2 fun ν _ ↦ ?_)
      grw [sum_weight_filter_denominator_eq_le X (denominator_ne_bot ν)]
      exact le_of_eq (by field_simp)
    _ ≤ (64 * 38) ^ Core.numInfPlaces E * Real.exp (2 * Module.finrank ℚ E) := by
      grw [← mul_sum, sum_absNorm_inv_sq_le]
    _ = _ := by
      have h_rank : (2 * Module.finrank ℚ E : ℝ) = Core.numInfPlaces E * 4 := by
        rw [finrank_eq_two_mul_card_infinitePlace]
        push_cast
        ring
      rw [h_rank, Real.exp_nat_mul, ← mul_pow]

end New

end
