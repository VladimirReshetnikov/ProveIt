import Lib.Adelic.Adeles.IdeleModulus
import Lib.General.Measure.IntegralOperators

/-!
# Sums over frequencies

A finite set of elements of a number field of degree `d` and multiplicative height at most `B`
has at most `2 * (2 ^ d) ^ 2 * B ^ 2` elements. At a place above 2 we use the integral chart
coordinate `x` or `x⁻¹`. The chart and its residue modulo a suitable power of 2 determine `x`.

Integrating the quadratic count bounds the sum of the inverse cubes of the heights. For a
totally complex field with `f` infinite places the sum is at most `96 ^ f`.
-/

open NumberField Height Ideal Finset Function
open scoped Classical

noncomputable section
namespace New
variable {E : Type} [Field E] [NumberField E]

/-- Each finite absolute value is bounded by the multiplicative height. -/
lemma finitePlace_le_mulHeight (w : FinitePlace E) (x : E) : w x ≤ mulHeight₁ x := by
  let g (v : FinitePlace E) := max (v x) 1
  have h : g.HasFiniteMulSupport := by
    by_cases hx : x = 0
    · simp only [g, hx, map_zero, max_eq_right zero_le_one]; fun_prop
    · unfold g; fun_prop (disch := assumption)
  have hv : w x ≤ ∏ᶠ v : FinitePlace E, g v := by
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ h (Finset.subset_insert w _)]
    exact le_prod_max_one (mem_insert_self w _) (fun v ↦ v x)
  rw [NumberField.mulHeight₁_eq]
  exact hv.trans (le_mul_of_one_le_left ((apply_nonneg w x).trans hv)
    (one_le_prod₀ fun _ _ ↦ one_le_pow₀ (le_max_right ..)))

/-- A bounded-height ball embeds into two copies of the residue ring at a prime over 2. -/
lemma card_height_ball {w : FinitePlace E} (hw : w 2 < 1) {B : ℝ} (hB : 1 ≤ B)
    (X : Finset E) (hX : ∀ x ∈ X, mulHeight₁ x ≤ B) :
    (X.card : ℝ) ≤ 2 * (2 ^ totalWeight E) ^ 2 * B ^ 2 := by
  let q := (w (2 : E))⁻¹
  have hpos : 0 < w (2 : E) := w.val.pos (by norm_num)
  have hq : 1 < q := one_lt_inv_iff₀.2 ⟨hpos, hw⟩
  have hqHeight : q ≤ 2 ^ totalWeight E := by
    calc q = w (2⁻¹ : E) := (map_inv₀ w 2).symm
      _ ≤ mulHeight₁ (2⁻¹ : E) := finitePlace_le_mulHeight _ _
      _ = mulHeight₁ (1 + 1 : E) := by rw [mulHeight₁_inv, one_add_one_eq_two]
      _ ≤ _ := by simpa using mulHeight₁_add_le (1 : E) 1
  -- Choose the least quotient precision above the height bound for a difference.
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near (x := 2 ^ totalWeight E * B ^ 2)
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (one_le_pow₀ hB))
    hq
  let ι : E →+* LocField w.maximalIdeal := FinitePlace.embedding w.maximalIdeal
  let u : LocField w.maximalIdeal := ι 2 ^ (k + 1)
  have hu : u ≠ 0 := pow_ne_zero _ ((map_ne_zero ι).2 (by norm_num))
  have normu : ‖u‖ = (w 2) ^ (k + 1) := by simp [u, ι, FinitePlace.norm_embedding_eq]
  have huint : u ∈ LocInt w.maximalIdeal := by
    change Valued.v u ≤ 1
    apply Valued.toNormedField.norm_le_one_iff.1
    rw [normu]
    exact pow_le_one₀ hpos.le hw.le
  let J := Ideal.span {(⟨u, huint⟩ : LocInt w.maximalIdeal)}
  have hcard : (Nat.card (LocInt w.maximalIdeal ⧸ J) : ℝ) = q ^ (k + 1) := by
    calc _ = genIndex u := (genIndex_eq_card (Valued.isOpen_valuationSubring _)
              (isCompact_LocInt _) huint (isUnit_iff_ne_zero.2 hu)).symm
      _ = ‖u‖⁻¹ := genIndex_eq_inv_norm (Units.mk0 u hu)
      _ = _ := by rw [normu, ← inv_pow]
  have : Finite (LocInt w.maximalIdeal ⧸ J) := Nat.finite_of_card_ne_zero fun h ↦ by
    rw [h, Nat.cast_zero] at hcard
    exact (pow_pos (zero_lt_one.trans hq) (k + 1)).ne hcard
  -- Record which affine chart contains the point and the residue of its coordinate.
  let small (x : E) := if w x ≤ 1 then x else x⁻¹
  have hsmall (x : E) : w (small x) ≤ 1 := by
    by_cases hx : w x ≤ 1
    · simp [small, hx]
    · simpa [small, hx] using inv_le_one_of_one_le₀ (le_of_not_ge hx)
  let rep (x : E) : LocInt w.maximalIdeal := ⟨ι (small x), Valued.toNormedField.norm_le_one_iff.1 <|
    (FinitePlace.norm_embedding_eq w _).trans_le (hsmall x)⟩
  let code (x : E) := (decide (w x ≤ 1), Ideal.Quotient.mk J (rep x))
  have h_inj : Set.InjOn code X := by
    intro x hx y hy heq
    have hchart : decide (w x ≤ 1) = decide (w y ≤ 1) := congrArg Prod.fst heq
    have hmod : (⟨u, huint⟩ : LocInt w.maximalIdeal) ∣ rep x - rep y :=
      Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 (congrArg Prod.snd heq))
    have hl : ‖ι (small x - small y)‖ ≤ ‖u‖ := by
      rw [map_sub, Valued.toNormedField.norm_le_iff]
      exact (Valuation.integer.integers Valued.v).le_of_dvd hmod
    -- Distinct coordinates would give an inverse difference taller than the global bound.
    have hxy : small x = small y := by
      by_contra hn
      have h₁ : q ^ (k + 1) ≤ w ((small x - small y)⁻¹) := by
        have hdiff : 0 < w (small x - small y) := w.val.pos (sub_ne_zero.mpr hn)
        rw [map_inv₀, le_inv_comm₀ (pow_pos (zero_lt_one.trans hq) _) hdiff]
        simpa only [normu, ι, FinitePlace.norm_embedding_eq, q, inv_pow, inv_inv] using hl
      have hb (z : E) (hz : z ∈ X) : mulHeight₁ (small z) ≤ B := by
        unfold small; split <;> simpa only [mulHeight₁_inv] using hX z hz
      apply hk'.not_ge
      calc
        q ^ (k + 1) ≤ mulHeight₁ ((small x - small y)⁻¹) := h₁.trans (finitePlace_le_mulHeight _ _)
        _ = _ := mulHeight₁_inv _
        _ ≤ _ := mulHeight₁_sub_le _ _
        _ ≤ _ := by grw [hb x hx, hb y hy, sq, mul_assoc]
    by_cases h₁ : w x ≤ 1 <;> by_cases h₂ : w y ≤ 1 <;> simp_all [small]
  have hsize := Nat.card_le_card_of_injective (fun z : X ↦ code z) h_inj.injective
  have hsize' : (X.card : ℝ) ≤ 2 * q ^ (k + 1) := by
    simpa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), ← hcard] using
      (Nat.cast_le (α := ℝ)).2 hsize
  refine hsize'.trans ?_
  rw [pow_succ]
  calc 2 * (q ^ k * q) ≤ 2 * ((2 ^ totalWeight E * B ^ 2) * (2 ^ totalWeight E)) := by gcongr
       _ = _ := by ring

private lemma exists_place_two (E : Type) [Field E] [NumberField E] : ∃ w : FinitePlace E, w 2 < 1 := by
  by_contra! h
  have hi := one_le_finprod h
  rw [FinitePlace.prod_eq_inv_abs_norm (by norm_num : (2 : E) ≠ 0)] at hi
  have hn : (Algebra.norm ℚ) (2 : E) = 2 ^ Module.finrank ℚ E := by
    simpa using Algebra.norm_algebraMap (S := E) (2 : ℚ)
  rw [hn] at hi
  have hh : (1 : ℚ) < 2 ^ Module.finrank ℚ E := one_lt_pow₀ (by norm_num) Module.finrank_pos.ne'
  norm_cast at hi
  exact (inv_lt_one_of_one_lt₀ (by exact_mod_cast hh)).not_ge hi

/-- The sum over any finite set of frequencies in a totally complex field. -/
theorem sum_height_inv_cube_le [IsTotallyComplex E] (X : Finset E) :
    ∑ x ∈ X, (mulHeight₁ x)⁻¹ ^ 3 ≤ 96 ^ Core.numInfPlaces E := by
  obtain ⟨w, hw⟩ := exists_place_two E
  calc
    (∑ x ∈ X, (mulHeight₁ x)⁻¹ ^ 3) ≤ (2 * (2 ^ totalWeight E) ^ 2) * 3 := by
      simpa [Real.rpow_neg_ofNat] using sum_rpow_neg_le_of_card_sublevel_le mulHeight₁
        one_le_mulHeight₁ (by positivity) (card_height_ball hw) (A := 3) (c := 3)
        (by norm_num) (by norm_num) X
    _ ≤ 96 ^ Core.numInfPlaces E := by
      let f := Core.numInfPlaces E
      have h6 : (6 : ℝ) ≤ 6 ^ f := le_self_pow₀ (by norm_num) NeZero.out
      rw [NumberField.totalWeight_eq_finrank, finrank_eq_two_mul_card_infinitePlace]
      calc
        (2 * ((2 : ℝ) ^ (2 * f)) ^ 2) * 3 = 6 * 16 ^ f := by rw [pow_mul, pow_right_comm]; norm_num; ring
        _ ≤ 6 ^ f * 16 ^ f := by gcongr
        _ = 96 ^ f := by rw [← mul_pow]; norm_num

end New
