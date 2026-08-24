import IntegerPoints.IwaniecMozzochiRanges
import IntegerPoints.IwaniecMozzochiSection12Blocks
import IntegerPoints.GKLemma36
import IntegerPoints.Lemma9Sum

/-!
# Iwaniec--Mozzochi (13.12): dyadic and endpoint-safe Farey-majorant pair counts

This file proves the dyadic pair-count estimate underlying Section 13,
conditional on the quoted Bombieri--Iwaniec Theorem 4.1, and proves the
endpoint-safe nominal-block majorant statement conditional on the matching
Farey-majorant spacing premise.  The analytic premises apply on `1 ≤ C`,
whereas the formal conclusions only assume `mu1 * G < C`.  We therefore also
prove the elementary small-`C` arguments.  In that range either denominator
finset is empty or every denominator is one, and the product-spacing condition
leaves only `O(A (1 + Delta2 * A * C))` pairs.

The analytic spacing theorem remains an explicit premise.  Everything proved
here is finite-set counting, positivity, or exact scale algebra.  The dyadic
specialization has `a, a₁ ∈ (A, 2A]` and therefore proves exactly
`iwaniecMozzochi_eq1312_dyadicPairCount`.  The corrected endpoint-safe count
and its nominal-block proposition are `fareyMajorantPairCount` and
`iwaniecMozzochi_eq1312_nominalBlock`; their large-`C` analytic boundary is
the exact-range premise `bombieriIwaniec_theorem41_fareyMajorant`, which
includes the six cross-range numerator interactions.  The exact-range
small-`C` count is proved below, and the scale algebra is shared between the
dyadic and Farey-majorant conditional theorems.  Finally, the strengthened,
`Fin`-indexed bare `iwaniecMozzochi_eq1312` follows by monotonicity: every
block threshold is bounded by the nominal threshold with `mu` replaced by
`2 * mu`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

/-- Enlarging both spacing thresholds can only enlarge the endpoint-safe
Farey-majorant pair count.  Nonnegativity of `A` and `C` is needed because the
second threshold occurs as `Delta2 * A * C`. -/
theorem fareyMajorantPairCount_mono
    {Δ₁ Δ₂ Δ₁' Δ₂' A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hΔ₁ : Δ₁ ≤ Δ₁') (hΔ₂ : Δ₂ ≤ Δ₂') :
    fareyMajorantPairCount Δ₁ Δ₂ A C ≤
      fareyMajorantPairCount Δ₁' Δ₂' A C := by
  classical
  unfold fareyMajorantPairCount
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_filter] at hq ⊢
  refine ⟨hq.1, hq.2.1, hq.2.2.1, ?_, ?_⟩
  · exact hq.2.2.2.1.trans hΔ₁
  · exact hq.2.2.2.2.trans_le
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hΔ₂ hA) hC)

/-- A natural number in `(C, 2C]`, for `0 < C < 1`, can only be one. -/
theorem eq1312_mem_dyadic_eq_one_of_lt_one {C : ℝ} (hC0 : 0 < C) (hC1 : C < 1)
    {c : ℕ} (hc : c ∈ dyadic C) : c = 1 := by
  obtain ⟨hcLower, hcUpper⟩ := L9.mem_dyadic_bounds hC0.le hc
  have hcPosReal : 0 < (c : ℝ) := hC0.trans hcLower
  have hcLtTwoReal : (c : ℝ) < 2 := hcUpper.trans_lt (by linarith)
  have hcPos : 0 < c := by exact_mod_cast hcPosReal
  have hcLtTwo : c < 2 := by exact_mod_cast hcLtTwoReal
  omega

/-- A natural number in the exact Section 13 range `[C, 2C)`, for
`0 < C < 1`, can only be one.  (For `C ≤ 1 / 2` the range is empty.) -/
theorem eq1312_mem_fareyDenominators_eq_one_of_lt_one {C : ℝ}
    (hC0 : 0 < C) (hC1 : C < 1) {c : ℕ} (hc : c ∈ fareyDenominators C) :
    c = 1 := by
  rw [fareyDenominators, Finset.mem_Ico] at hc
  have hcOne : 1 ≤ c := (Nat.one_le_ceil_iff.2 hC0).trans hc.1
  have hceilTwo : ⌈2 * C⌉₊ ≤ 2 := by
    rw [Nat.ceil_le]
    norm_num
    linarith
  omega

/-- A reusable one-dimensional spacing count.  If `S` has at most `2A`
elements, then pairs in `S x S` whose real casts differ by less than `delta`
number at most `2A(2delta+1)`. -/
theorem eq1312_card_close_nat_pairs_le (S : Finset ℕ) {A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hcard : (S.card : ℝ) ≤ 2 * A) :
    ((((S ×ˢ S).filter fun p : ℕ × ℕ =>
        |(p.1 : ℝ) - (p.2 : ℝ)| < δ).card : ℕ) : ℝ) ≤
      2 * A * (2 * δ + 1) := by
  classical
  let P := (S ×ˢ S).filter fun p : ℕ × ℕ =>
    |(p.1 : ℝ) - (p.2 : ℝ)| < δ
  let J := Finset.Icc ⌈-δ⌉ ⌊δ⌋
  let Q := S ×ˢ J
  let f : ℕ × ℕ → ℕ × ℤ := fun p => (p.1, (p.2 : ℤ) - (p.1 : ℤ))
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    simp only [f, Prod.mk.injEq] at hab
    rcases hab with ⟨ha, hdiff⟩
    subst a'
    have hbInt : (b : ℤ) = (b' : ℤ) := sub_left_inj.mp hdiff
    have hb : b = b' := by exact_mod_cast hbInt
    exact Prod.ext rfl hb
  have hmap : Set.MapsTo f (P : Set (ℕ × ℕ)) (Q : Set (ℕ × ℤ)) := by
    intro p hp
    have hp' : p ∈ P := hp
    simp only [P, Finset.mem_filter, Finset.mem_product] at hp'
    change f p ∈ Q
    simp only [Q, Finset.mem_product]
    refine ⟨hp'.1.1, ?_⟩
    rw [Finset.mem_Icc]
    have habs : -δ < (p.2 : ℝ) - (p.1 : ℝ) ∧
        (p.2 : ℝ) - (p.1 : ℝ) < δ :=
      abs_lt.mp (by simpa only [abs_sub_comm] using hp'.2)
    constructor
    · rw [Int.ceil_le]
      simpa only [f, Int.cast_sub, Int.cast_natCast] using habs.1.le
    · rw [Int.le_floor]
      simpa only [f, Int.cast_sub, Int.cast_natCast] using habs.2.le
  have hcardNat : P.card ≤ Q.card :=
    Finset.card_le_card_of_injOn f hmap hf.injOn
  have hJcard : (J.card : ℝ) ≤ 2 * δ + 1 := by
    dsimp [J]
    convert GK36.card_Icc_ceil_floor_le (show -δ ≤ δ by linarith) using 1 <;>
      ring
  have hQcard : (Q.card : ℝ) = (S.card : ℝ) * (J.card : ℝ) := by
    simp [Q]
  have hprod : (Q.card : ℝ) ≤ 2 * A * (2 * δ + 1) := by
    rw [hQcard]
    exact mul_le_mul hcard hJcard (Nat.cast_nonneg _) (by positivity)
  change (P.card : ℝ) ≤ 2 * A * (2 * δ + 1)
  exact (by exact_mod_cast hcardNat : (P.card : ℝ) ≤ Q.card) |>.trans hprod

/-- The endpoint-safe numerator interval `A / 4 ≤ a < 2A` contains at most
`2A` natural numbers.  The strict upper endpoint is important when `2A` is an
integer; writing the range with `Nat.ceil` preserves that endpoint exactly. -/
theorem eq1312_fareyMajorantNumerators_card_le {A : ℝ} (hA : 0 ≤ A) :
    ((fareyMajorantNumerators A).card : ℝ) ≤ 2 * A := by
  classical
  by_cases hAz : A = 0
  · subst A
    norm_num [fareyMajorantNumerators]
  · have hA0 : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hsub : fareyMajorantNumerators A ⊆ Finset.Ico 1 ⌈2 * A⌉₊ := by
      intro a ha
      simp only [fareyMajorantNumerators, Finset.mem_Ico] at ha
      simp only [Finset.mem_Ico]
      constructor
      · exact (Nat.one_le_ceil_iff.2 (by positivity)).trans ha.1
      · exact ha.2
    have hcardNat := Finset.card_le_card hsub
    have hceilOne : 1 ≤ ⌈2 * A⌉₊ := Nat.one_le_ceil_iff.2 (by positivity)
    have hceilLt : (⌈2 * A⌉₊ : ℝ) < 2 * A + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    calc
      ((fareyMajorantNumerators A).card : ℝ) ≤
          ((Finset.Ico 1 ⌈2 * A⌉₊).card : ℝ) := by exact_mod_cast hcardNat
      _ = (⌈2 * A⌉₊ : ℝ) - 1 := by
        rw [Nat.card_Ico, Nat.cast_sub hceilOne]
        norm_num
      _ ≤ 2 * A := by linarith

/-- For `0 < C < 1`, the Farey-pair count reduces to a one-dimensional
spacing count because both denominators are one.  The reciprocal-spacing
condition can only reduce the count, so no hypothesis on `Delta1` is needed. -/
theorem eq1312_fareyPairCount_smallC_le {Δ₁ Δ₂ A C : ℝ}
    (hA : 0 ≤ A) (hC0 : 0 < C) (hC1 : C < 1) (hΔ₂ : 0 ≤ Δ₂) :
    (fareyPairCount Δ₁ Δ₂ A C : ℝ) ≤
      2 * A * (2 * (Δ₂ * A * C) + 1) := by
  classical
  let F := (((dyadic A ×ˢ dyadic C) ×ˢ (dyadic A ×ˢ dyadic C)).filter
    fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
      Nat.Coprime q.1.1 q.1.2 ∧ Nat.Coprime q.2.1 q.2.2 ∧
        nearestIntDist ((modInv q.1.1 q.1.2 : ℝ) / q.1.2 -
          (modInv q.2.1 q.2.2 : ℝ) / q.2.2) ≤ Δ₁ ∧
        |((q.1.1 * q.1.2 : ℕ) : ℝ) - ((q.2.1 * q.2.2 : ℕ) : ℝ)| <
          Δ₂ * A * C)
  let P := ((dyadic A ×ˢ dyadic A).filter fun p : ℕ × ℕ =>
    |(p.1 : ℝ) - (p.2 : ℝ)| < Δ₂ * A * C)
  let f : (ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ := fun q => (q.1.1, q.2.1)
  have hmap : Set.MapsTo f (F : Set ((ℕ × ℕ) × (ℕ × ℕ)))
      (P : Set (ℕ × ℕ)) := by
    intro q hq
    have hq' : q ∈ F := hq
    simp only [F, Finset.mem_filter, Finset.mem_product] at hq'
    change f q ∈ P
    simp only [P, f, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hq'.1.1.1, hq'.1.2.1⟩, ?_⟩
    have hc := eq1312_mem_dyadic_eq_one_of_lt_one hC0 hC1 hq'.1.1.2
    have hc' := eq1312_mem_dyadic_eq_one_of_lt_one hC0 hC1 hq'.1.2.2
    simpa [hc, hc'] using hq'.2.2.2.2
  have hinj : Set.InjOn f (F : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
    rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩ hq ⟨⟨a', c'⟩, ⟨b', d'⟩⟩ hq' hab
    have hqMem : ((a, c), (b, d)) ∈ F := hq
    have hq'Mem : ((a', c'), (b', d')) ∈ F := hq'
    simp only [F, Finset.mem_filter, Finset.mem_product] at hqMem hq'Mem
    have hc := eq1312_mem_dyadic_eq_one_of_lt_one hC0 hC1 hqMem.1.1.2
    have hd := eq1312_mem_dyadic_eq_one_of_lt_one hC0 hC1 hqMem.1.2.2
    have hc' := eq1312_mem_dyadic_eq_one_of_lt_one hC0 hC1 hq'Mem.1.1.2
    have hd' := eq1312_mem_dyadic_eq_one_of_lt_one hC0 hC1 hq'Mem.1.2.2
    change (a, b) = (a', b') at hab
    cases hab
    subst c
    subst d
    subst c'
    subst d'
    rfl
  have hcardNat : F.card ≤ P.card :=
    Finset.card_le_card_of_injOn f hmap hinj
  have hδ : 0 ≤ Δ₂ * A * C := by positivity
  have hP : (P.card : ℝ) ≤ 2 * A * (2 * (Δ₂ * A * C) + 1) := by
    dsimp [P]
    exact eq1312_card_close_nat_pairs_le (dyadic A) hA hδ (L9.card_dyadic_le hA)
  unfold fareyPairCount
  change (F.card : ℝ) ≤ 2 * A * (2 * (Δ₂ * A * C) + 1)
  exact (by exact_mod_cast hcardNat : (F.card : ℝ) ≤ P.card) |>.trans hP

/-- The elementary small-`C` estimate for the endpoint-safe Farey majorant.
Both exact-range denominators are one, while the half-open numerator interval
still has at most `2A` elements, so the same one-dimensional spacing argument
as in the dyadic case applies. -/
theorem eq1312_fareyMajorantPairCount_smallC_le {Δ₁ Δ₂ A C : ℝ}
    (hA : 0 ≤ A) (hC0 : 0 < C) (hC1 : C < 1) (hΔ₂ : 0 ≤ Δ₂) :
    (fareyMajorantPairCount Δ₁ Δ₂ A C : ℝ) ≤
      2 * A * (2 * (Δ₂ * A * C) + 1) := by
  classical
  let F := (((fareyMajorantNumerators A ×ˢ fareyDenominators C) ×ˢ
      (fareyMajorantNumerators A ×ˢ fareyDenominators C)).filter
    fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
      Nat.Coprime q.1.1 q.1.2 ∧ Nat.Coprime q.2.1 q.2.2 ∧
        nearestIntDist ((modInv q.1.1 q.1.2 : ℝ) / q.1.2 -
          (modInv q.2.1 q.2.2 : ℝ) / q.2.2) ≤ Δ₁ ∧
        |((q.1.1 * q.1.2 : ℕ) : ℝ) - ((q.2.1 * q.2.2 : ℕ) : ℝ)| <
          Δ₂ * A * C)
  let P := ((fareyMajorantNumerators A ×ˢ fareyMajorantNumerators A).filter
    fun p : ℕ × ℕ => |(p.1 : ℝ) - (p.2 : ℝ)| < Δ₂ * A * C)
  let f : (ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ := fun q => (q.1.1, q.2.1)
  have hmap : Set.MapsTo f (F : Set ((ℕ × ℕ) × (ℕ × ℕ)))
      (P : Set (ℕ × ℕ)) := by
    intro q hq
    have hq' : q ∈ F := hq
    simp only [F, Finset.mem_filter, Finset.mem_product] at hq'
    change f q ∈ P
    simp only [P, f, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hq'.1.1.1, hq'.1.2.1⟩, ?_⟩
    have hc := eq1312_mem_fareyDenominators_eq_one_of_lt_one hC0 hC1 hq'.1.1.2
    have hc' := eq1312_mem_fareyDenominators_eq_one_of_lt_one hC0 hC1 hq'.1.2.2
    simpa [hc, hc'] using hq'.2.2.2.2
  have hinj : Set.InjOn f (F : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
    rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩ hq ⟨⟨a', c'⟩, ⟨b', d'⟩⟩ hq' hab
    have hqMem : ((a, c), (b, d)) ∈ F := hq
    have hq'Mem : ((a', c'), (b', d')) ∈ F := hq'
    simp only [F, Finset.mem_filter, Finset.mem_product] at hqMem hq'Mem
    have hc := eq1312_mem_fareyDenominators_eq_one_of_lt_one hC0 hC1 hqMem.1.1.2
    have hd := eq1312_mem_fareyDenominators_eq_one_of_lt_one hC0 hC1 hqMem.1.2.2
    have hc' := eq1312_mem_fareyDenominators_eq_one_of_lt_one hC0 hC1 hq'Mem.1.1.2
    have hd' := eq1312_mem_fareyDenominators_eq_one_of_lt_one hC0 hC1 hq'Mem.1.2.2
    change (a, b) = (a', b') at hab
    cases hab
    subst c
    subst d
    subst c'
    subst d'
    rfl
  have hcardNat : F.card ≤ P.card :=
    Finset.card_le_card_of_injOn f hmap hinj
  have hδ : 0 ≤ Δ₂ * A * C := by positivity
  have hP : (P.card : ℝ) ≤ 2 * A * (2 * (Δ₂ * A * C) + 1) := by
    dsimp [P]
    exact eq1312_card_close_nat_pairs_le (fareyMajorantNumerators A) hA hδ
      (eq1312_fareyMajorantNumerators_card_le hA)
  unfold fareyMajorantPairCount
  change (F.card : ℝ) ≤ 2 * A * (2 * (Δ₂ * A * C) + 1)
  exact (by exact_mod_cast hcardNat : (F.card : ℝ) ≤ P.card) |>.trans hP

private theorem eq1312_M_sq_lt_x {x H M : ℝ} (hmain : InMainRange x H M) :
    M ^ 2 < x := by
  rcases hmain with ⟨hx, hxM, hMupper, _, _, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hroot : M < Real.sqrt x := by
    simpa [Real.sqrt_eq_rpow] using hMupper
  nlinarith [Real.sq_sqrt hx0.le]

/-- The fractional-power factor in `Delta2` has the exact elementary scale
`C/N`.  Taking fourth powers avoids choosing any square-root branch; both
sides are nonnegative. -/
private theorem eq1312_delta2_core {x C M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hM : 0 < M) :
    x ^ (-(1 : ℝ) / 4) * (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
        Kscale x C M ^ (-(1 : ℝ) / 2) =
      C / shiftLength x M := by
  have hA : 0 < Ascale x C M := by unfold Ascale; positivity
  have hN : 0 < shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    positivity
  have hK : 0 < Kscale x C M := by unfold Kscale; positivity
  let S := x ^ (-(1 : ℝ) / 4) * (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
    Kscale x C M ^ (-(1 : ℝ) / 2)
  let R := C / shiftLength x M
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hx4 : (x ^ (-(1 : ℝ) / 4)) ^ 4 = x⁻¹ := by
    calc
      (x ^ (-(1 : ℝ) / 4)) ^ 4 =
          x ^ ((-(1 : ℝ) / 4) * (4 : ℕ)) :=
        (Real.rpow_mul_natCast hx.le _ 4).symm
      _ = x ^ (-(1 : ℝ)) := by congr 1 <;> norm_num
      _ = x⁻¹ := Real.rpow_neg_one x
  have hAC4 : ((Ascale x C M * C) ^ ((3 : ℝ) / 4)) ^ 4 =
      (Ascale x C M * C) ^ 3 := by
    calc
      ((Ascale x C M * C) ^ ((3 : ℝ) / 4)) ^ 4 =
          (Ascale x C M * C) ^ (((3 : ℝ) / 4) * (4 : ℕ)) :=
        (Real.rpow_mul_natCast (mul_nonneg hA.le hC.le) _ 4).symm
      _ = (Ascale x C M * C) ^ (3 : ℝ) := by congr 1 <;> norm_num
      _ = (Ascale x C M * C) ^ 3 := Real.rpow_natCast _ 3
  have hK4 : (Kscale x C M ^ (-(1 : ℝ) / 2)) ^ 4 =
      (Kscale x C M ^ 2)⁻¹ := by
    calc
      (Kscale x C M ^ (-(1 : ℝ) / 2)) ^ 4 =
          Kscale x C M ^ ((-(1 : ℝ) / 2) * (4 : ℕ)) :=
        (Real.rpow_mul_natCast hK.le _ 4).symm
      _ = Kscale x C M ^ (-(2 : ℝ)) := by congr 1 <;> norm_num
      _ = (Kscale x C M ^ (2 : ℝ))⁻¹ := Real.rpow_neg hK.le 2
      _ = (Kscale x C M ^ 2)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast (Kscale x C M) 2)
  have hfourth : S ^ 4 = R ^ 4 := by
    dsimp [S, R]
    rw [show (x ^ (-(1 : ℝ) / 4) * (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
          Kscale x C M ^ (-(1 : ℝ) / 2)) ^ 4 =
        (x ^ (-(1 : ℝ) / 4)) ^ 4 *
          ((Ascale x C M * C) ^ ((3 : ℝ) / 4)) ^ 4 *
          (Kscale x C M ^ (-(1 : ℝ) / 2)) ^ 4 by ring,
      hx4, hAC4, hK4]
    unfold Ascale Kscale
    rw [shiftLength_eq_mul_rpow]
    field_simp [hx.ne', hC.ne', hM.ne']
  exact (pow_left_inj₀ hS0 hR0 (by norm_num : (4 : ℕ) ≠ 0)).mp hfourth

private noncomputable def eq1312Delta1 (μ x C H M : ℝ) : ℝ :=
  μ / (Kscale x C M * Lscale x C H M)

private noncomputable def eq1312Delta2 (μ x C H M : ℝ) : ℝ :=
  μ * x ^ (-(1 : ℝ) / 4) * (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
    Kscale x C M ^ (-(1 : ℝ) / 2) / Lscale x C H M

private noncomputable def eq1312Target (x C H M : ℝ) : ℝ :=
  x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7

private theorem eq1312_delta2_eq {μ x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hM : 0 < M) :
    eq1312Delta2 μ x C H M =
      μ * C / (shiftLength x M * Lscale x C H M) := by
  have hcore := eq1312_delta2_core hx hC hM
  unfold eq1312Delta2
  rw [show μ * x ^ (-(1 : ℝ) / 4) *
        (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
        Kscale x C M ^ (-(1 : ℝ) / 2) =
      μ * (x ^ (-(1 : ℝ) / 4) *
        (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
        Kscale x C M ^ (-(1 : ℝ) / 2)) by ring,
    hcore]
  ring

private theorem eq1312_rpow_cancel_seven_elevenths {x : ℝ} (hx : 0 < x) :
    x ^ (-(7 : ℝ) / 11) * x ^ ((7 : ℝ) / 11) = 1 := by
  rw [← Real.rpow_add hx]
  norm_num

private theorem eq1312_target_eq {x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) :
    eq1312Target x C H M = M ^ 2 / (C * H * x ^ ((7 : ℝ) / 11)) := by
  have hN : 0 < shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    positivity
  have hNpow : shiftLength x M ^ (-(5 : ℝ)) =
      M ^ (-(5 : ℝ)) * x ^ ((15 : ℝ) / 11) := by
    rw [shiftLength_eq_mul_rpow,
      Real.mul_rpow hM.le (Real.rpow_nonneg hx.le _)]
    have hxpow : (x ^ (-(3 : ℝ) / 11)) ^ (-(5 : ℝ)) =
        x ^ ((15 : ℝ) / 11) := by
      calc
        (x ^ (-(3 : ℝ) / 11)) ^ (-(5 : ℝ)) =
            x ^ ((-(3 : ℝ) / 11) * (-(5 : ℝ))) :=
          (Real.rpow_mul hx.le _ _).symm
        _ = x ^ ((15 : ℝ) / 11) := by congr 1 <;> norm_num
    rw [hxpow]
  have hMpow : M ^ (-(5 : ℝ)) * M ^ 7 = M ^ 2 := by
    calc
      M ^ (-(5 : ℝ)) * M ^ 7 = M ^ (-(5 : ℝ)) * M ^ (7 : ℝ) :=
        congrArg (fun z => M ^ (-(5 : ℝ)) * z)
          (Real.rpow_natCast M 7).symm
      _ = M ^ (-(5 : ℝ) + 7) :=
        (Real.rpow_add hM _ _).symm
      _ = M ^ (2 : ℝ) := by congr 1 <;> norm_num
      _ = M ^ 2 := Real.rpow_natCast _ 2
  have hxpow : x ^ (-(2 : ℝ)) * x ^ ((15 : ℝ) / 11) =
      x ^ (-(7 : ℝ) / 11) := by
    calc
      x ^ (-(2 : ℝ)) * x ^ ((15 : ℝ) / 11) =
          x ^ (-(2 : ℝ) + (15 : ℝ) / 11) :=
        (Real.rpow_add hx _ _).symm
      _ = x ^ (-(7 : ℝ) / 11) := by congr 1 <;> norm_num
  unfold eq1312Target
  rw [hNpow]
  calc
    x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ *
          (M ^ (-(5 : ℝ)) * x ^ ((15 : ℝ) / 11)) * M ^ 7 =
        (M ^ (-(5 : ℝ)) * M ^ 7) *
          (x ^ (-(2 : ℝ)) * x ^ ((15 : ℝ) / 11)) * C⁻¹ * H⁻¹ := by
      ring
    _ = M ^ 2 * x ^ (-(7 : ℝ) / 11) * C⁻¹ * H⁻¹ := by
      rw [hMpow, hxpow]
    _ = M ^ 2 / (C * H * x ^ ((7 : ℝ) / 11)) := by
      have hx7 : 0 < x ^ ((7 : ℝ) / 11) := Real.rpow_pos_of_pos hx _
      field_simp [hC.ne', hH.ne', hx7.ne']
      convert eq1312_rpow_cancel_seven_elevenths hx using 1 <;> ring

private theorem eq1312_L_mul_G {x C H M : ℝ}
    (hx : 0 < x) (hH : 0 < H) (hM : 0 < M) :
    Lscale x C H M * Gscale x H M = C := by
  have hN : 0 < shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    positivity
  unfold Lscale Gscale
  field_simp [hx.ne', hH.ne', hM.ne', hN.ne']

private theorem eq1312_KL_lt_C_sq {x C H M : ℝ}
    (hmain : InMainRange x H M) (hC : 0 < C) :
    Kscale x C M * Lscale x C H M < C ^ 2 := by
  rcases hmain with ⟨hx, hxM, _, hH, hHupper, _, _, hMlower⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hN0 : 0 < shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    positivity
  have hHupper' : H ≤ M * x ^ (-(7 : ℝ) / 22) := by
    convert hHupper using 1
    norm_num [theta0]
  have hMlower' : x ^ ((19 : ℝ) / 44) < M := by
    convert hMlower using 1
    norm_num [theta0]
  have hMtwo : x ^ ((19 : ℝ) / 22) < M ^ 2 := by
    have hsquare := mul_self_lt_mul_self
      (Real.rpow_nonneg hx0.le _) hMlower'
    calc
      x ^ ((19 : ℝ) / 22) =
          x ^ ((19 : ℝ) / 44) * x ^ ((19 : ℝ) / 44) := by
        rw [← Real.rpow_add hx0]
        congr 1 <;> ring
      _ < M * M := hsquare
      _ = M ^ 2 := by ring
  have hratio : H * x ^ ((13 : ℝ) / 11) < M ^ 3 := by
    calc
      H * x ^ ((13 : ℝ) / 11) ≤
          (M * x ^ (-(7 : ℝ) / 22)) * x ^ ((13 : ℝ) / 11) :=
        mul_le_mul_of_nonneg_right hHupper' (Real.rpow_nonneg hx0.le _)
      _ = M * (x ^ (-(7 : ℝ) / 22) * x ^ ((13 : ℝ) / 11)) := by ring
      _ = M * x ^ ((19 : ℝ) / 22) := by
        congr 1
        rw [← Real.rpow_add hx0]
        congr 1 <;> norm_num
      _ < M * M ^ 2 := mul_lt_mul_of_pos_left hMtwo hM0
      _ = M ^ 3 := by ring
  unfold Kscale Lscale
  rw [shiftLength_eq_mul_rpow]
  have hxneg : 0 < x ^ (-(3 : ℝ) / 11) := Real.rpow_pos_of_pos hx0 _
  have hscale :
      x ^ 2 * H * (M * x ^ (-(3 : ℝ) / 11)) ^ 3 < M ^ 6 := by
    have hpow : (M * x ^ (-(3 : ℝ) / 11)) ^ 3 =
        M ^ 3 * x ^ (-(9 : ℝ) / 11) := by
      rw [mul_pow]
      have hx3 : (x ^ (-(3 : ℝ) / 11)) ^ 3 =
          x ^ (-(9 : ℝ) / 11) := by
        calc
          (x ^ (-(3 : ℝ) / 11)) ^ 3 =
              x ^ ((-(3 : ℝ) / 11) * (3 : ℕ)) :=
            (Real.rpow_mul_natCast hx0.le _ 3).symm
          _ = x ^ (-(9 : ℝ) / 11) := by congr 1 <;> norm_num
      rw [hx3]
    rw [hpow]
    have hxcombine : x ^ 2 * x ^ (-(9 : ℝ) / 11) = x ^ ((13 : ℝ) / 11) := by
      calc
        x ^ 2 * x ^ (-(9 : ℝ) / 11) =
            x ^ (2 : ℝ) * x ^ (-(9 : ℝ) / 11) :=
          congrArg (fun z => z * x ^ (-(9 : ℝ) / 11))
            (Real.rpow_natCast x 2).symm
        _ =
            x ^ ((2 : ℝ) + -(9 : ℝ) / 11) :=
          (Real.rpow_add hx0 _ _).symm
        _ = x ^ ((13 : ℝ) / 11) := by congr 1 <;> norm_num
    calc
      x ^ 2 * H * (M ^ 3 * x ^ (-(9 : ℝ) / 11)) =
          (x ^ 2 * x ^ (-(9 : ℝ) / 11)) * H * M ^ 3 := by ring
      _ = x ^ ((13 : ℝ) / 11) * H * M ^ 3 := by rw [hxcombine]
      _ = (H * x ^ ((13 : ℝ) / 11)) * M ^ 3 := by ring
      _ < M ^ 3 * M ^ 3 := mul_lt_mul_of_pos_right hratio (pow_pos hM0 3)
      _ = M ^ 6 := by ring
  have hden : 0 < M ^ 6 := pow_pos hM0 6
  have hfrac :
      (x ^ 2 * H * (M * x ^ (-(3 : ℝ) / 11)) ^ 3) / M ^ 6 < 1 :=
    (div_lt_one hden).2 hscale
  calc
    (x * C * (M * x ^ (-(3 : ℝ) / 11)) ^ 2 / M ^ 3) *
          (x * C * H * (M * x ^ (-(3 : ℝ) / 11)) / M ^ 3) =
        C ^ 2 *
          ((x ^ 2 * H * (M * x ^ (-(3 : ℝ) / 11)) ^ 3) / M ^ 6) := by
      field_simp [hM0.ne']
    _ < C ^ 2 * 1 := mul_lt_mul_of_pos_left hfrac (sq_pos_of_pos hC)
    _ = C ^ 2 := mul_one _

private theorem eq1312_target_one_le {x C H M : ℝ}
    (hmain : InMainRange x H M) (hC : 0 < C) (hCH : C ≤ H) :
    1 ≤ eq1312Target x C H M := by
  rcases hmain with ⟨hx, hxM, _, hH, hHupper, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hHupper' : H ≤ M * x ^ (-(7 : ℝ) / 22) := by
    convert hHupper using 1
    norm_num [theta0]
  have hxneg : 0 < x ^ (-(7 : ℝ) / 22) := Real.rpow_pos_of_pos hx0 _
  have hxpos : 0 < x ^ ((7 : ℝ) / 11) := Real.rpow_pos_of_pos hx0 _
  have hCHsq : C * H ≤ H * H := mul_le_mul_of_nonneg_right hCH hH0.le
  have hHsq : H * H ≤
      (M * x ^ (-(7 : ℝ) / 22)) * (M * x ^ (-(7 : ℝ) / 22)) :=
    mul_le_mul hHupper' hHupper' hH0.le (mul_pos hM0 hxneg).le
  have hdenle : C * H * x ^ ((7 : ℝ) / 11) ≤ M ^ 2 := by
    calc
      C * H * x ^ ((7 : ℝ) / 11) ≤
          (H * H) * x ^ ((7 : ℝ) / 11) :=
        mul_le_mul_of_nonneg_right hCHsq hxpos.le
      _ ≤ ((M * x ^ (-(7 : ℝ) / 22)) *
            (M * x ^ (-(7 : ℝ) / 22))) * x ^ ((7 : ℝ) / 11) :=
        mul_le_mul_of_nonneg_right hHsq hxpos.le
      _ = M ^ 2 *
          (x ^ (-(7 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22) *
            x ^ ((7 : ℝ) / 11)) := by ring
      _ = M ^ 2 := by
        have hcancel : x ^ (-(7 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22) *
            x ^ ((7 : ℝ) / 11) = 1 := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
          norm_num
        rw [hcancel, mul_one]
  rw [eq1312_target_eq hx0 hC hH0 hM0]
  exact (le_div_iff₀ (mul_pos (mul_pos hC hH0) hxpos)).2 (by simpa using hdenle)

private theorem eq1312_delta1_C_sq_ge {μ x C H M : ℝ}
    (hμ : 0 < μ) (hmain : InMainRange x H M) (hC : 0 < C) :
    μ ≤ eq1312Delta1 μ x C H M * C ^ 2 := by
  have hmain' : InMainRange x H M := hmain
  rcases hmain with ⟨hx, hxM, _, hH, _, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hN0 : 0 < shiftLength x M := by rw [shiftLength_eq_mul_rpow]; positivity
  have hK0 : 0 < Kscale x C M := by unfold Kscale; positivity
  have hL0 : 0 < Lscale x C H M := by unfold Lscale; positivity
  have hKL0 : 0 < Kscale x C M * Lscale x C H M := mul_pos hK0 hL0
  have hΔ₁0 : 0 < eq1312Delta1 μ x C H M := by
    unfold eq1312Delta1
    positivity
  have hmul : eq1312Delta1 μ x C H M *
      (Kscale x C M * Lscale x C H M) = μ := by
    unfold eq1312Delta1
    field_simp [hKL0.ne']
  have hKLlt := eq1312_KL_lt_C_sq hmain' hC
  calc
    μ = eq1312Delta1 μ x C H M *
        (Kscale x C M * Lscale x C H M) := hmul.symm
    _ ≤ eq1312Delta1 μ x C H M * C ^ 2 :=
      mul_le_mul_of_nonneg_left hKLlt.le hΔ₁0.le

private theorem eq1312_shift_fifth {x M : ℝ} (hx : 0 < x) :
    x ^ 2 * shiftLength x M ^ 5 = M ^ 5 * x ^ ((7 : ℝ) / 11) := by
  rw [shiftLength_eq_mul_rpow, mul_pow]
  have hx5 : (x ^ (-(3 : ℝ) / 11)) ^ 5 = x ^ (-(15 : ℝ) / 11) := by
    calc
      (x ^ (-(3 : ℝ) / 11)) ^ 5 =
          x ^ ((-(3 : ℝ) / 11) * (5 : ℕ)) :=
        (Real.rpow_mul_natCast hx.le _ 5).symm
      _ = x ^ (-(15 : ℝ) / 11) := by congr 1 <;> norm_num
  rw [hx5]
  have hxcombine : x ^ 2 * x ^ (-(15 : ℝ) / 11) = x ^ ((7 : ℝ) / 11) := by
    calc
      x ^ 2 * x ^ (-(15 : ℝ) / 11) =
          x ^ (2 : ℝ) * x ^ (-(15 : ℝ) / 11) :=
        congrArg (fun z => z * x ^ (-(15 : ℝ) / 11))
          (Real.rpow_natCast x 2).symm
      _ =
          x ^ ((2 : ℝ) + -(15 : ℝ) / 11) :=
        (Real.rpow_add hx _ _).symm
      _ = x ^ ((7 : ℝ) / 11) := by congr 1 <;> norm_num
  rw [show x ^ 2 * (M ^ 5 * x ^ (-(15 : ℝ) / 11)) =
      M ^ 5 * (x ^ 2 * x ^ (-(15 : ℝ) / 11)) by ring, hxcombine]

private theorem eq1312_mixed_term_eq {μ x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) :
    eq1312Delta1 μ x C H M * eq1312Delta2 μ x C H M *
        Ascale x C M * C =
      μ ^ 2 * (C / H) * eq1312Target x C H M := by
  have hN : 0 < shiftLength x M := by rw [shiftLength_eq_mul_rpow]; positivity
  have hK : 0 < Kscale x C M := by unfold Kscale; positivity
  have hL : 0 < Lscale x C H M := by unfold Lscale; positivity
  rw [eq1312_delta2_eq hx hC hM, eq1312_target_eq hx hC hH hM]
  unfold eq1312Delta1 Ascale Kscale Lscale
  field_simp [hx.ne', hC.ne', hH.ne', hM.ne', hN.ne', hK.ne', hL.ne']
  have hshift := eq1312_shift_fifth (M := M) hx
  nlinarith

private theorem eq1312_square_term_eq {μ x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) :
    eq1312Delta1 μ x C H M ^ 2 * Ascale x C M * C =
      μ ^ 2 * (Gscale x H M / C) * eq1312Target x C H M := by
  have hN : 0 < shiftLength x M := by rw [shiftLength_eq_mul_rpow]; positivity
  have hK : 0 < Kscale x C M := by unfold Kscale; positivity
  have hL : 0 < Lscale x C H M := by unfold Lscale; positivity
  rw [eq1312_target_eq hx hC hH hM]
  unfold eq1312Delta1 Ascale Kscale Lscale Gscale
  field_simp [hx.ne', hC.ne', hH.ne', hM.ne', hN.ne', hK.ne', hL.ne']
  have hshift := eq1312_shift_fifth (M := M) hx
  nlinarith

private theorem eq1312_A_gt_C {x C H M : ℝ}
    (hmain : InMainRange x H M) (hC : 0 < C) :
    C < Ascale x C M := by
  have hmain' : InMainRange x H M := hmain
  rcases hmain with ⟨hx, hxM, _, _, _, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hMtwo := eq1312_M_sq_lt_x hmain'
  unfold Ascale
  apply (lt_div_iff₀ (sq_pos_of_pos hM0)).2
  nlinarith

private theorem eq1312_target_times_AC {x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) :
    eq1312Target x C H M * (Ascale x C M * C) =
      Ascale x C M * Gscale x H M * x ^ ((1 : ℝ) / 11) := by
  have hN : 0 < shiftLength x M := by rw [shiftLength_eq_mul_rpow]; positivity
  rw [eq1312_target_eq hx hC hH hM]
  unfold Ascale Gscale
  rw [shiftLength_eq_mul_rpow]
  have hxneg : 0 < x ^ (-(3 : ℝ) / 11) := Real.rpow_pos_of_pos hx _
  field_simp [hx.ne', hC.ne', hH.ne', hM.ne', hN.ne', hxneg.ne']
  have hxcombine : x ^ ((7 : ℝ) / 11) * x ^ ((1 : ℝ) / 11) =
      x * x ^ (-(3 : ℝ) / 11) := by
    calc
      x ^ ((7 : ℝ) / 11) * x ^ ((1 : ℝ) / 11) =
          x ^ ((8 : ℝ) / 11) := by
        rw [← Real.rpow_add hx]
        congr 1 <;> norm_num
      _ = x ^ ((1 : ℝ) + -(3 : ℝ) / 11) := by congr 1 <;> norm_num
      _ = x * x ^ (-(3 : ℝ) / 11) := by
        rw [Real.rpow_add hx, Real.rpow_one]
  nlinarith

private theorem eq1312_target_with_epsilon {x C H M ε : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) :
    eq1312Target x C H M * (Ascale x C M * C) ^ (1 + ε) =
      Ascale x C M * Gscale x H M * x ^ ((1 : ℝ) / 11) *
        (Ascale x C M * C) ^ ε := by
  have hA : 0 < Ascale x C M := by unfold Ascale; positivity
  rw [Real.rpow_add (mul_pos hA hC), Real.rpow_one]
  rw [show eq1312Target x C H M *
        (Ascale x C M * C * (Ascale x C M * C) ^ ε) =
      (eq1312Target x C H M * (Ascale x C M * C)) *
        (Ascale x C M * C) ^ ε by ring,
    eq1312_target_times_AC hx hC hH hM]

private theorem eq1312_small_delta_le {μ x C H M : ℝ}
    (hμ : 0 < μ) (hmain : InMainRange x H M)
    (hC : 0 < C) (hC1 : C < 1) :
    eq1312Delta2 μ x C H M * Ascale x C M * C ≤
      μ * Gscale x H M * x ^ ((1 : ℝ) / 11) := by
  rcases hmain with ⟨hx, hxM, _, hH, _, _, _, hMlower⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hN0 : 0 < shiftLength x M := by rw [shiftLength_eq_mul_rpow]; positivity
  have hL0 : 0 < Lscale x C H M := by unfold Lscale; positivity
  have hG0 : 0 < Gscale x H M := by unfold Gscale; positivity
  have hA0 : 0 < Ascale x C M := by unfold Ascale; positivity
  have hMlower' : x ^ ((19 : ℝ) / 44) < M := by
    convert hMlower using 1
    norm_num [theta0]
  have hx52_le_x57 : x ^ ((13 : ℝ) / 11) ≤ x ^ ((57 : ℝ) / 44) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hx57_lt_M3 : x ^ ((57 : ℝ) / 44) < M ^ 3 := by
    have h1 := mul_self_lt_mul_self
      (Real.rpow_nonneg hx0.le _) hMlower'
    have h2 :
        (x ^ ((19 : ℝ) / 44) * x ^ ((19 : ℝ) / 44)) *
            x ^ ((19 : ℝ) / 44) <
          (M * M) * M := by
      calc
        (x ^ ((19 : ℝ) / 44) * x ^ ((19 : ℝ) / 44)) *
              x ^ ((19 : ℝ) / 44) <
            (M * M) * x ^ ((19 : ℝ) / 44) :=
          mul_lt_mul_of_pos_right h1 (Real.rpow_pos_of_pos hx0 _)
        _ < (M * M) * M :=
          mul_lt_mul_of_pos_left hMlower' (mul_pos hM0 hM0)
    calc
      x ^ ((57 : ℝ) / 44) =
          (x ^ ((19 : ℝ) / 44) * x ^ ((19 : ℝ) / 44)) *
            x ^ ((19 : ℝ) / 44) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
        congr 1 <;> ring
      _ < (M * M) * M := h2
      _ = M ^ 3 := by ring
  have hCtwo : C ^ 2 < 1 := by nlinarith [sq_pos_of_pos hC]
  have hscale : C ^ 2 * x ^ ((13 : ℝ) / 11) ≤ M ^ 3 := by
    calc
      C ^ 2 * x ^ ((13 : ℝ) / 11) ≤ 1 * x ^ ((13 : ℝ) / 11) :=
        mul_le_mul_of_nonneg_right hCtwo.le (Real.rpow_nonneg hx0.le _)
      _ ≤ x ^ ((57 : ℝ) / 44) := by simpa using hx52_le_x57
      _ ≤ M ^ 3 := hx57_lt_M3.le
  have hLG := eq1312_L_mul_G (C := C) hx0 hH0 hM0
  have hΔ₂ : eq1312Delta2 μ x C H M = μ * Gscale x H M /
      shiftLength x M := by
    rw [eq1312_delta2_eq hx0 hC hM0]
    calc
      μ * C / (shiftLength x M * Lscale x C H M) =
          μ * (Lscale x C H M * Gscale x H M) /
            (shiftLength x M * Lscale x C H M) := by rw [hLG]
      _ = μ * Gscale x H M / shiftLength x M := by
        field_simp [hN0.ne', hL0.ne', hG0.ne']
  rw [hΔ₂]
  have hratio : Ascale x C M * C / shiftLength x M ≤ x ^ ((1 : ℝ) / 11) := by
    apply (div_le_iff₀ hN0).2
    unfold Ascale
    rw [shiftLength_eq_mul_rpow]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hM0)).2
    have hxneg2 : 0 ≤ x ^ (-(2 : ℝ) / 11) := Real.rpow_nonneg hx0.le _
    have hscaled := mul_le_mul_of_nonneg_right hscale hxneg2
    have hx132 :
        x ^ ((13 : ℝ) / 11) * x ^ (-(2 : ℝ) / 11) = x := by
      rw [← Real.rpow_add hx0]
      norm_num [Real.rpow_one]
    have hx1m3 :
        x ^ ((1 : ℝ) / 11) * x ^ (-(3 : ℝ) / 11) =
          x ^ (-(2 : ℝ) / 11) := by
      rw [← Real.rpow_add hx0]
      congr 1 <;> norm_num
    calc
      x * C * C = C ^ 2 *
          (x ^ ((13 : ℝ) / 11) * x ^ (-(2 : ℝ) / 11)) := by
        rw [hx132]
        ring
      _ = (C ^ 2 * x ^ ((13 : ℝ) / 11)) *
          x ^ (-(2 : ℝ) / 11) := by ring
      _ ≤ M ^ 3 * x ^ (-(2 : ℝ) / 11) := hscaled
      _ = (x ^ ((1 : ℝ) / 11) * x ^ (-(3 : ℝ) / 11)) * M ^ 3 := by
        rw [hx1m3]
        ring
      _ = x ^ ((1 : ℝ) / 11) *
          (M * x ^ (-(3 : ℝ) / 11)) * M ^ 2 := by ring
  calc
    μ * Gscale x H M / shiftLength x M * Ascale x C M * C =
        μ * Gscale x H M *
          (Ascale x C M * C / shiftLength x M) := by ring
    _ ≤ μ * Gscale x H M * x ^ ((1 : ℝ) / 11) :=
      mul_le_mul_of_nonneg_left hratio (mul_pos hμ hG0).le

/-- Shared scale algebra for both the dyadic and Farey-majorant pair counts.
Only two facts about `pairCount` enter: the Bombieri--Iwaniec-shaped estimate
for `1 ≤ C`, and the elementary denominator-one estimate for `0 < C < 1`.
Keeping the count abstract here prevents the two Section 13 proofs from
silently drifting apart. -/
private theorem eq1312_pairCount_of_spacing
    (pairCount : ℝ → ℝ → ℝ → ℝ → ℕ)
    (hBI :
      ∀ c₀ c₁ ε : ℝ, 0 < c₀ → 0 < c₁ → 0 < ε →
        ∃ C₀ : ℝ, ∀ Δ₁ Δ₂ A C : ℝ, 1 ≤ A → 1 ≤ C → 0 < Δ₁ → 0 < Δ₂ →
          C ≤ c₀ * A → c₁ ≤ Δ₁ * C ^ 2 →
          (pairCount Δ₁ Δ₂ A C : ℝ) ≤
            C₀ * (1 + Δ₁ * Δ₂ * A * C + Δ₁ ^ 2 * A * C) *
              (A * C) ^ (1 + ε))
    (hsmallCount :
      ∀ {Δ₁ Δ₂ A C : ℝ}, 0 ≤ A → 0 < C → C < 1 → 0 ≤ Δ₂ →
        (pairCount Δ₁ Δ₂ A C : ℝ) ≤
          2 * A * (2 * (Δ₂ * A * C) + 1)) :
    ∀ μ₁ μ ε : ℝ, 0 < μ₁ → 0 < μ → 0 < ε →
      ∃ C₀ : ℝ, ∀ x C H M : ℝ,
        InMainRange x H M → μ₁ * Gscale x H M < C → C ≤ H →
        (pairCount (μ / (Kscale x C M * Lscale x C H M))
            (μ * x ^ (-(1 : ℝ) / 4) * (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
              Kscale x C M ^ (-(1 : ℝ) / 2) / Lscale x C H M)
            (Ascale x C M) C : ℝ) ≤
          C₀ * (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) *
            M ^ 7 * (Ascale x C M * C) ^ (1 + ε)) := by
  intro μ₁ μ ε hμ₁ hμ hε
  obtain ⟨C_BI, hBIbound⟩ := hBI 1 μ ε zero_lt_one hμ hε
  let D : ℝ := 1 + μ ^ 2 + μ ^ 2 / μ₁
  let q : ℝ := (μ₁ ^ 2) ^ ε
  let Csmall : ℝ := 2 * (2 * μ + 1) / q
  let Cbig : ℝ := |C_BI| * D
  refine ⟨Cbig + Csmall, ?_⟩
  intro x C H M hmain hshort hCH
  rcases hmain with ⟨hx, hxM, hMupper, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hmain : InMainRange x H M :=
    ⟨hx, hxM, hMupper, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hN0 : 0 < shiftLength x M := by rw [shiftLength_eq_mul_rpow]; positivity
  have hGbounds := iwaniecMozzochi_eq66_holds x H M hmain
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hGbounds.1
  have hC0 : 0 < C := (mul_pos hμ₁ hG0).trans hshort
  have hA0 : 0 < Ascale x C M := by unfold Ascale; positivity
  have hK0 : 0 < Kscale x C M := by unfold Kscale; positivity
  have hL0 : 0 < Lscale x C H M := by unfold Lscale; positivity
  have hΔ₁0 : 0 < eq1312Delta1 μ x C H M := by
    unfold eq1312Delta1
    positivity
  have hΔ₂0 : 0 < eq1312Delta2 μ x C H M := by
    rw [eq1312_delta2_eq hx0 hC0 hM0]
    positivity
  have hT1 : 1 ≤ eq1312Target x C H M :=
    eq1312_target_one_le hmain hC0 hCH
  have hT0 : 0 ≤ eq1312Target x C H M := zero_le_one.trans hT1
  have hAC0 : 0 < Ascale x C M * C := mul_pos hA0 hC0
  have hpow0 : 0 ≤ (Ascale x C M * C) ^ (1 + ε) :=
    Real.rpow_nonneg hAC0.le _
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hD0 : 0 ≤ D := by
    dsimp [D]
    have hquot : 0 ≤ μ ^ 2 / μ₁ := div_nonneg (sq_nonneg μ) hμ₁.le
    positivity
  have hCsmall0 : 0 ≤ Csmall := by
    dsimp [Csmall]
    positivity
  have hCbig0 : 0 ≤ Cbig := by dsimp [Cbig]; positivity
  change
    (pairCount (eq1312Delta1 μ x C H M)
        (eq1312Delta2 μ x C H M) (Ascale x C M) C : ℝ) ≤
      (Cbig + Csmall) *
        (eq1312Target x C H M * (Ascale x C M * C) ^ (1 + ε))
  by_cases hCone : 1 ≤ C
  · have hAone : 1 ≤ Ascale x C M := by
      exact hCone.trans (eq1312_A_gt_C hmain hC0).le
    have hCA : C ≤ (1 : ℝ) * Ascale x C M := by
      simpa using (eq1312_A_gt_C hmain hC0).le
    have hspacing : μ ≤ eq1312Delta1 μ x C H M * C ^ 2 :=
      eq1312_delta1_C_sq_ge hμ hmain hC0
    have hcount := hBIbound (eq1312Delta1 μ x C H M)
      (eq1312Delta2 μ x C H M) (Ascale x C M) C
      hAone hCone hΔ₁0 hΔ₂0 hCA hspacing
    let B : ℝ := 1 +
      eq1312Delta1 μ x C H M * eq1312Delta2 μ x C H M *
        Ascale x C M * C +
      eq1312Delta1 μ x C H M ^ 2 * Ascale x C M * C
    have hB0 : 0 ≤ B := by
      dsimp [B]
      positivity
    have hCHratio : C / H ≤ 1 := (div_le_one hH0).2 hCH
    have hmixed :
        eq1312Delta1 μ x C H M * eq1312Delta2 μ x C H M *
            Ascale x C M * C ≤ μ ^ 2 * eq1312Target x C H M := by
      rw [eq1312_mixed_term_eq hx0 hC0 hH0 hM0]
      calc
        μ ^ 2 * (C / H) * eq1312Target x C H M ≤
            μ ^ 2 * 1 * eq1312Target x C H M := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hCHratio (sq_nonneg μ)) hT0
        _ = μ ^ 2 * eq1312Target x C H M := by ring
    have hGC : Gscale x H M / C ≤ 1 / μ₁ := by
      apply (div_le_iff₀ hC0).2
      calc
        Gscale x H M ≤ C / μ₁ :=
          (le_div_iff₀ hμ₁).2 (by simpa [mul_comm] using hshort.le)
        _ = (1 / μ₁) * C := by ring
    have hsquare :
        eq1312Delta1 μ x C H M ^ 2 * Ascale x C M * C ≤
          (μ ^ 2 / μ₁) * eq1312Target x C H M := by
      rw [eq1312_square_term_eq hx0 hC0 hH0 hM0]
      calc
        μ ^ 2 * (Gscale x H M / C) * eq1312Target x C H M ≤
            μ ^ 2 * (1 / μ₁) * eq1312Target x C H M := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hGC (sq_nonneg μ)) hT0
        _ = (μ ^ 2 / μ₁) * eq1312Target x C H M := by ring
    have hB : B ≤ D * eq1312Target x C H M := by
      dsimp [B, D]
      calc
        1 +
            eq1312Delta1 μ x C H M * eq1312Delta2 μ x C H M *
              Ascale x C M * C +
            eq1312Delta1 μ x C H M ^ 2 * Ascale x C M * C ≤
            eq1312Target x C H M +
              μ ^ 2 * eq1312Target x C H M +
              (μ ^ 2 / μ₁) * eq1312Target x C H M :=
          add_le_add (add_le_add hT1 hmixed) hsquare
        _ = (1 + μ ^ 2 + μ ^ 2 / μ₁) * eq1312Target x C H M := by ring
    have hCBI : C_BI * B ≤ |C_BI| * B :=
      mul_le_mul_of_nonneg_right (le_abs_self C_BI) hB0
    have hbig :
        (pairCount (eq1312Delta1 μ x C H M)
            (eq1312Delta2 μ x C H M) (Ascale x C M) C : ℝ) ≤
          Cbig * (eq1312Target x C H M *
            (Ascale x C M * C) ^ (1 + ε)) := by
      calc
        (pairCount (eq1312Delta1 μ x C H M)
              (eq1312Delta2 μ x C H M) (Ascale x C M) C : ℝ) ≤
            C_BI * B * (Ascale x C M * C) ^ (1 + ε) := by
          simpa [B] using hcount
        _ ≤ |C_BI| * B * (Ascale x C M * C) ^ (1 + ε) :=
          mul_le_mul_of_nonneg_right hCBI hpow0
        _ ≤ |C_BI| * (D * eq1312Target x C H M) *
              (Ascale x C M * C) ^ (1 + ε) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hB (abs_nonneg C_BI)) hpow0
        _ = Cbig * (eq1312Target x C H M *
              (Ascale x C M * C) ^ (1 + ε)) := by
          dsimp [Cbig]
          ring
    exact hbig.trans (by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hT0 hpow0)
      linarith)
  · have hClt : C < 1 := lt_of_not_ge hCone
    have hraw := hsmallCount
      (Δ₁ := eq1312Delta1 μ x C H M)
      (Δ₂ := eq1312Delta2 μ x C H M)
      hA0.le hC0 hClt hΔ₂0.le
    have hδ := eq1312_small_delta_le hμ hmain hC0 hClt
    let U : ℝ := Ascale x C M * Gscale x H M * x ^ ((1 : ℝ) / 11)
    have hxpow1 : 1 ≤ x ^ ((1 : ℝ) / 11) :=
      Real.one_le_rpow hx (by norm_num)
    have hGx1 : 1 ≤ Gscale x H M * x ^ ((1 : ℝ) / 11) :=
      one_le_mul_of_one_le_of_one_le hGbounds.1 hxpow1
    have hU0 : 0 ≤ U := by dsimp [U]; positivity
    have hclose :
        (pairCount (eq1312Delta1 μ x C H M)
            (eq1312Delta2 μ x C H M) (Ascale x C M) C : ℝ) ≤
          2 * (2 * μ + 1) * U := by
      calc
        (pairCount (eq1312Delta1 μ x C H M)
              (eq1312Delta2 μ x C H M) (Ascale x C M) C : ℝ) ≤
            2 * Ascale x C M *
              (2 * (eq1312Delta2 μ x C H M * Ascale x C M * C) + 1) :=
          hraw
        _ ≤ 2 * Ascale x C M *
              (2 * (μ * Gscale x H M * x ^ ((1 : ℝ) / 11)) + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ 2 * Ascale x C M *
              ((2 * μ + 1) * (Gscale x H M * x ^ ((1 : ℝ) / 11))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [mul_nonneg (show 0 ≤ 2 * μ by positivity) (sub_nonneg.mpr hGx1)]
        _ = 2 * (2 * μ + 1) * U := by dsimp [U]; ring
    have hmuC : μ₁ < C := by
      calc
        μ₁ = μ₁ * 1 := by ring
        _ ≤ μ₁ * Gscale x H M :=
          mul_le_mul_of_nonneg_left hGbounds.1 hμ₁.le
        _ < C := hshort
    have hACmu : μ₁ ^ 2 < Ascale x C M * C := by
      have hAC := eq1312_A_gt_C hmain hC0
      have hsq : μ₁ * μ₁ < C * C :=
        mul_self_lt_mul_self hμ₁.le hmuC
      calc
        μ₁ ^ 2 = μ₁ * μ₁ := by ring
        _ < C * C := hsq
        _ < Ascale x C M * C := by
          exact mul_lt_mul_of_pos_right hAC hC0
    have hqle : q ≤ (Ascale x C M * C) ^ ε := by
      dsimp [q]
      exact Real.rpow_le_rpow (sq_nonneg μ₁) hACmu.le hε.le
    have htarget := eq1312_target_with_epsilon
      (ε := ε) hx0 hC0 hH0 hM0
    have hsmall :
        (pairCount (eq1312Delta1 μ x C H M)
            (eq1312Delta2 μ x C H M) (Ascale x C M) C : ℝ) ≤
          Csmall * (eq1312Target x C H M *
            (Ascale x C M * C) ^ (1 + ε)) := by
      calc
        (pairCount (eq1312Delta1 μ x C H M)
              (eq1312Delta2 μ x C H M) (Ascale x C M) C : ℝ) ≤
            2 * (2 * μ + 1) * U := hclose
        _ = Csmall * (U * q) := by
          dsimp [Csmall]
          field_simp [hq0.ne']
        _ ≤ Csmall * (U * (Ascale x C M * C) ^ ε) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hqle hU0) hCsmall0
        _ = Csmall * (eq1312Target x C H M *
              (Ascale x C M * C) ^ (1 + ε)) := by
          simpa only [U] using congrArg (fun z => Csmall * z) htarget.symm
    exact hsmall.trans (by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hT0 hpow0)
      linarith)

/-- On every Section 12 block, the first spacing threshold is at most the
nominal threshold with `mu` doubled. -/
private theorem eq1312_block_delta1_le
    {μ K L Kb Lb : ℝ}
    (hμ : 0 ≤ μ)
    (hK : 0 < K) (hL : 0 < L)
    (hKb : 0 < Kb) (hLb : 0 < Lb)
    (hKKb : K ≤ Kb) (hLLb : L / 2 ≤ Lb) :
    μ / (Kb * Lb) ≤ (2 * μ) / (K * L) := by
  have hLtwo : L ≤ 2 * Lb := by
    linarith
  have hprod : K * L ≤ 2 * (Kb * Lb) := by
    calc
      K * L ≤ Kb * (2 * Lb) :=
        mul_le_mul hKKb hLtwo hL.le hKb.le
      _ = 2 * (Kb * Lb) := by ring
  apply (div_le_div_iff₀ (mul_pos hKb hLb) (mul_pos hK hL)).2
  calc
    μ * (K * L) ≤ μ * (2 * (Kb * Lb)) :=
      mul_le_mul_of_nonneg_left hprod hμ
    _ = (2 * μ) * (Kb * Lb) := by ring

/-- On every Section 12 block, the second spacing threshold is at most the
nominal threshold with `mu` doubled. -/
private theorem eq1312_block_delta2_le
    {μ X Y K L Kb Lb : ℝ}
    (hμ : 0 ≤ μ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hK : 0 < K) (hL : 0 < L) (hLb : 0 < Lb)
    (hKKb : K ≤ Kb) (hLLb : L / 2 ≤ Lb) :
    μ * X * Y * Kb ^ (-(1 : ℝ) / 2) / Lb ≤
      (2 * μ) * X * Y * K ^ (-(1 : ℝ) / 2) / L := by
  have hLtwo : L ≤ 2 * Lb := by
    linarith
  have hpow :
      Kb ^ (-(1 : ℝ) / 2) ≤ K ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hK hKKb
      (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
  have hprefix : 0 ≤ μ * X * Y :=
    mul_nonneg (mul_nonneg hμ hX) hY
  have hKpow : 0 ≤ K ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg hK.le _
  apply (div_le_div_iff₀ hLb hL).2
  calc
    (μ * X * Y * Kb ^ (-(1 : ℝ) / 2)) * L ≤
        (μ * X * Y * K ^ (-(1 : ℝ) / 2)) * L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hprefix) hL.le
    _ ≤ (μ * X * Y * K ^ (-(1 : ℝ) / 2)) * (2 * Lb) :=
      mul_le_mul_of_nonneg_left hLtwo
        (mul_nonneg hprefix hKpow)
    _ = ((2 * μ) * X * Y * K ^ (-(1 : ℝ) / 2)) * Lb := by
      ring

/-- **The dyadic pair-count estimate underlying Iwaniec--Mozzochi (13.12),
conditional form.**  Bombieri--Iwaniec Theorem 4.1 supplies the paper range
`1 ≤ C`; the remaining formal range `0 < C < 1` is discharged by the
dyadic denominator-one spacing count. -/
theorem iwaniecMozzochi_eq1312_dyadicPairCount_of_bombieriIwaniec_theorem41
    (hBI : bombieriIwaniec_theorem41) :
    iwaniecMozzochi_eq1312_dyadicPairCount := by
  unfold bombieriIwaniec_theorem41 at hBI
  unfold iwaniecMozzochi_eq1312_dyadicPairCount
  exact eq1312_pairCount_of_spacing fareyPairCount hBI
    eq1312_fareyPairCount_smallC_le

/-- **(13.12), endpoint-safe nominal-block conditional form.**  The
Farey-majorant Bombieri--Iwaniec premise supplies all same- and cross-range
pairs for `1 ≤ C`; `eq1312_fareyMajorantPairCount_smallC_le` supplies the
remaining `0 < C < 1` range.  The finite-block theorem below transfers this
nominal estimate by threshold monotonicity. -/
theorem
    iwaniecMozzochi_eq1312_nominalBlock_of_bombieriIwaniec_theorem41_fareyMajorant
    (hBI : bombieriIwaniec_theorem41_fareyMajorant) :
    iwaniecMozzochi_eq1312_nominalBlock := by
  unfold bombieriIwaniec_theorem41_fareyMajorant at hBI
  unfold iwaniecMozzochi_eq1312_nominalBlock
  exact eq1312_pairCount_of_spacing fareyMajorantPairCount hBI
    eq1312_fareyMajorantPairCount_smallC_le

/-- **(13.12), uniformly over the finite Section 12 block cover.**  Every
block has `Kbase ≤ Kb` and `Lbase / 2 ≤ Lb`.  Consequently both block spacing
thresholds are bounded by the nominal thresholds with `mu` replaced by
`2 * mu`.  Monotonicity of the exact Farey-majorant count therefore transfers
the nominal Bombieri--Iwaniec estimate with one constant chosen before the
two finite block indices. -/
theorem
    iwaniecMozzochi_eq1312_of_bombieriIwaniec_theorem41_fareyMajorant
    (hBI : bombieriIwaniec_theorem41_fareyMajorant) :
    iwaniecMozzochi_eq1312 := by
  have hnominal :=
    iwaniecMozzochi_eq1312_nominalBlock_of_bombieriIwaniec_theorem41_fareyMajorant
      hBI
  unfold iwaniecMozzochi_eq1312_nominalBlock at hnominal
  unfold iwaniecMozzochi_eq1312
  intro μ₁ μ ε hμ₁ hμ hε
  obtain ⟨C₀, hC₀⟩ :=
    hnominal μ₁ (2 * μ) ε hμ₁ (mul_pos (by norm_num) hμ) hε
  refine ⟨C₀, ?_⟩
  intro x C H M jK jL hmain hshort hCH

  have hmain' : InMainRange x H M := hmain
  rcases hmain with ⟨hx, hxM, _, hH, _, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M :=
    (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hN0 : 0 < shiftLength x M := by
    unfold shiftLength
    positivity
  have hGbounds := iwaniecMozzochi_eq66_holds x H M hmain'
  have hG0 : 0 < Gscale x H M :=
    zero_lt_one.trans_le hGbounds.1
  have hC0 : 0 < C :=
    (mul_pos hμ₁ hG0).trans hshort
  have hA0 : 0 < Ascale x C M := by
    unfold Ascale
    positivity

  let Kbase : ℝ := Kscale x C M
  let Lbase : ℝ := Lscale x C H M
  let Kb : ℝ := section12KBlockScale Kbase jK
  let Lb : ℝ := section12LBlockScale Lbase jL
  have hKbase0 : 0 < Kbase := by
    dsimp [Kbase]
    unfold Kscale
    positivity
  have hLbase0 : 0 < Lbase := by
    dsimp [Lbase]
    unfold Lscale
    positivity
  have hKbLower : Kbase ≤ Kb := by
    simpa only [Kb] using
      section12KBlockScale_lower hKbase0.le jK
  have hLbLower : Lbase / 2 ≤ Lb := by
    simpa only [Lb] using
      section12LBlockScale_lower hLbase0.le jL
  have hKb0 : 0 < Kb :=
    hKbase0.trans_le hKbLower
  have hLb0 : 0 < Lb :=
    (div_pos hLbase0 (by norm_num)).trans_le hLbLower

  have hΔ₁ :
      μ / (Kb * Lb) ≤ (2 * μ) / (Kbase * Lbase) :=
    eq1312_block_delta1_le
      (μ := μ) (K := Kbase) (L := Lbase)
      (Kb := Kb) (Lb := Lb)
      hμ.le hKbase0 hLbase0 hKb0 hLb0 hKbLower hLbLower
  have hxQuarter0 : 0 ≤ x ^ (-(1 : ℝ) / 4) :=
    Real.rpow_nonneg hx0.le _
  have hACThreeQuarter0 :
      0 ≤ (Ascale x C M * C) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (mul_nonneg hA0.le hC0.le) _
  have hΔ₂ :
      μ * x ^ (-(1 : ℝ) / 4) *
          (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
          Kb ^ (-(1 : ℝ) / 2) / Lb ≤
        (2 * μ) * x ^ (-(1 : ℝ) / 4) *
          (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
          Kbase ^ (-(1 : ℝ) / 2) / Lbase :=
    eq1312_block_delta2_le
      (μ := μ)
      (X := x ^ (-(1 : ℝ) / 4))
      (Y := (Ascale x C M * C) ^ ((3 : ℝ) / 4))
      (K := Kbase) (L := Lbase)
      (Kb := Kb) (Lb := Lb)
      hμ.le hxQuarter0 hACThreeQuarter0
      hKbase0 hLbase0 hLb0 hKbLower hLbLower

  have hcountNat :
      fareyMajorantPairCount
          (μ / (Kb * Lb))
          (μ * x ^ (-(1 : ℝ) / 4) *
            (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
            Kb ^ (-(1 : ℝ) / 2) / Lb)
          (Ascale x C M) C ≤
        fareyMajorantPairCount
          ((2 * μ) / (Kbase * Lbase))
          ((2 * μ) * x ^ (-(1 : ℝ) / 4) *
            (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
            Kbase ^ (-(1 : ℝ) / 2) / Lbase)
          (Ascale x C M) C :=
    fareyMajorantPairCount_mono hA0.le hC0.le hΔ₁ hΔ₂
  have hcountReal :
      (fareyMajorantPairCount
          (μ / (Kb * Lb))
          (μ * x ^ (-(1 : ℝ) / 4) *
            (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
            Kb ^ (-(1 : ℝ) / 2) / Lb)
          (Ascale x C M) C : ℝ) ≤
        (fareyMajorantPairCount
          ((2 * μ) / (Kbase * Lbase))
          ((2 * μ) * x ^ (-(1 : ℝ) / 4) *
            (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
            Kbase ^ (-(1 : ℝ) / 2) / Lbase)
          (Ascale x C M) C : ℝ) := by
    exact_mod_cast hcountNat
  have hnom := hC₀ x C H M hmain' hshort hCH
  have hresult := hcountReal.trans hnom
  simpa only [Kbase, Lbase, Kb, Lb] using hresult

end LeanProofs.IntegerPoints
