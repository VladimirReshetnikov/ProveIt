import New.Derivatives.Divisibility.Count
import New.Derivatives.Sharpness.NearPairs

/-!
# A lower bound for the divisibility bound by the gain

Fix a prime `p`. The divisibility bound of stage `j` at `p` measures the `p`-divisibility of a lift;
it depends on a set `S` (also written `ev`) of places whose long rows are removed.

This file defines it and bounds it from below by the gain at `p` when `p < x₁` is non-split. Apart
from an error term, only collisions lose; a collision is a pair `(τ, e)` with `e ∈ I_p` (`e` odd, or
`p = d`) such that `τ` and `(-p ^ e) τ` are `a`-places outside `ev`. In `lowColumns` and `lowBoxes`
a column is a column of a diagram; they count the columns of height below `n_{j+1}` and different
from `1`, and the boxes in them.

## Main definitions and results

* `New.Data.divisibilityBound`: the divisibility bound at `p` of stage `j`, for a set `S` of places.
* `New.Data.le_divisibilityBound`: the lower bound for the divisibility bound by the gain at `p`.

Notions from other files:
* `New.Data.aPlaces`: The `a`-places: the infinite places of `E` whose class in `(ℤ/q₁)ˣ` is `1`
  modulo `q₀`.
* `New.Data.IsExceptional`, `New.Data.ceilLogLifts`: A condition on `p` alone: `(p/d) = -1`,
  `p ≢ ±1` modulo `m`, and the order `o₀` of `-p` modulo `q₀` is odd and at most `𝔯`, the least
  natural number with `m ≤ p^𝔯`.
* `New.Data.placeOfInt`: The infinite place of E named by the class of the integer ν modulo q₁ if ν
  is prime to q₁, and the identity place otherwise.
-/

noncomputable section

namespace New.Data

section DivisibilityBound

open Finset Real Nat

variable {P : Parameters} {D : Data P}

/-- The number of columns at τ of height below n_{j+1} and different from 1: the sum of
`columnCount τ h` over h < n_{j+1}, h ≠ 1. -/
def lowColumns (j : ℕ) (τ : D.Φ) : ℕ := ∑ h ∈ range (D.n (j + 1)),
  if h = 1 then 0 else D.columnCount τ h

/-- The number of boxes in the columns counted by `New.Data.lowColumns` j τ: the sum of
h·`columnCount τ h` over h < n_{j+1}, h ≠ 1. -/
def lowBoxes (j : ℕ) (τ : D.Φ) : ℕ := ∑ h ∈ range (D.n (j + 1)),
  h * if h = 1 then 0 else D.columnCount τ h

/-- The divisibility bound at `p` of stage `j`, for a set `ev` of places. Remove the columns of
height one at the places of `ev` from the diagrams `D.columnCount`, read at heights below
`n = D.n (j + 1)`. The bound is the predicted divisibility of what remains, plus the full gain
`γ_p = gammaPrime P.d p` for each removed box, less `f n ^ 3 (1 + log_p (max B 1))`. Here `B` is the
number of boxes before the removal. -/
noncomputable def divisibilityBound (p j : ℕ) (ev : Finset D.Φ) : ℝ :=
  predictedDivisibility P.d p (P.partner D.towerExp p) (eraseHeightOne D.columnCount ev)
    (D.n (j + 1)) +
    gammaPrime P.d p * (boxes D.columnCount (D.n (j + 1)) - boxes (eraseHeightOne D.columnCount ev)
      (D.n (j + 1))) -
    D.f * D.n (j + 1) ^ 3 * (1 + logb p (max (boxes D.columnCount (D.n (j + 1))) 1 : ℕ))

/-- The length of the long row at `τ` (the `a` columns of height one at an `a`-place) after removing
the long rows at the places of `ev`. -/
noncomputable def longRow (ev : Finset D.Φ) (τ : D.Φ) : ℝ := if τ ∈ D.aPlaces \ ev then D.a else 0

/-- The term of the place `τ` and the exponent `e` in the predicted divisibility of stage `j`, after
removing the long rows at the places of `ev` and without the factor `v(π_p)`. It is zero unless
`e ∈ I_p = positivePartnerExponents P.d p`, and `P.partner D.towerExp p e τ` is the place
`(-p ^ e) τ`. -/
noncomputable def partnerTerm (p j : ℕ) (ev : Finset D.Φ) (τ : D.Φ) (e : ℕ) : ℝ :=
  if e ∈ positivePartnerExponents P.d p then
    (longRow ev τ / p ^ e - longRow ev (P.partner D.towerExp p e τ) -
        D.lowColumns j (P.partner D.towerExp p e τ))⁺ +
      (D.lowBoxes j τ / p ^ e - D.lowBoxes j (P.partner D.towerExp p e τ) : ℝ)⁺ - D.lowColumns j τ /
        p ^ e
  else 0

variable {p : ℕ} [q : Fact p.Prime]

/-- The terms `partnerTerm p j S τ e = (L τ / p ^ e - L τ' - c τ')₊ + (l τ / p ^ e - l τ')₊ - c
τ / p ^ e`, where `τ' = (-p ^ e) τ`, `L = longRow S`, `c = lowColumns j` and `l = lowBoxes j` (zero
unless `e ∈ positivePartnerExponents P.d p`), are summable over `e`. -/
lemma summable_partnerTerm (j : ℕ) (S : Finset D.Φ) (τ : D.Φ) :
    Summable (partnerTerm p j S τ) := by
  -- Each term is bounded in absolute value by a constant times `1 / p ^ e`.
  refine (hasSum_div_pow_positivePartnerExponents P.d p
    (longRow S τ + D.lowBoxes j τ + D.lowColumns j τ)).summable.of_norm_bounded fun e ↦ ?_
  have h_abs {a a' b b' c : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hb : 0 ≤ b) (hb' : 0 ≤ b')
      (hc : 0 ≤ c) : |(a - a')⁺ + (b - b')⁺ - c| ≤ a + b + c := by grind [posPart_def]
  rw [partnerTerm, sub_sub, add_div, add_div, norm_eq_abs]
  split_ifs
  · unfold longRow
    apply h_abs <;> positivity
  · simp

/-- After removing the long rows at the places of `S`, the number of columns of height one at `τ`
below `n_{j+1}` is `longRow S τ`. -/
lemma heightOneColumns_eraseHeightOne (j : ℕ) (S : Finset D.Φ) (τ : D.Φ) :
    (heightOneColumns (eraseHeightOne D.columnCount S) (D.n (j + 1)) τ : ℝ) = longRow S τ := by
  have h_one : 1 < D.n (j + 1) := by grind [n]
  by_cases τ ∈ S <;> simp [heightOneColumns, eraseHeightOne, longRow, columnCount, *]

/-- Erasing the columns of height one at the places of `S` from `D.columnCount` keeps the number of
low columns: `lowColumnCount` at height bound `D.n (j + 1)` equals `D.lowColumns j τ`. -/
lemma lowColumnCount_eraseHeightOne (j : ℕ) (S : Finset D.Φ) (τ : D.Φ) :
    lowColumnCount (eraseHeightOne D.columnCount S) (D.n (j + 1)) τ = D.lowColumns j τ :=
  sum_congr rfl fun h _ ↦ by simp +contextual [eraseHeightOne]

/-- Erasing the columns of height one at the places of `S` from `D.columnCount` keeps the number of
boxes in the low columns: `lowBoxCount` at height bound `D.n (j + 1)` equals `D.lowBoxes j τ`. -/
lemma lowBoxCount_eraseHeightOne (j : ℕ) (S : Finset D.Φ) (τ : D.Φ) :
    lowBoxCount (eraseHeightOne D.columnCount S) (D.n (j + 1)) τ = D.lowBoxes j τ :=
  sum_congr rfl fun h _ ↦ by simp +contextual [eraseHeightOne]

variable (D) in
/-- The loss `D.loss p` is at least `f * logB ^ 2 * (a / p)`: for `p ≡ ±1` modulo `m` it carries
the additional factor `m ≥ 1`. -/
lemma le_loss (p : ℕ) : D.f * D.logB ^ 2 * (D.a / p) ≤ D.loss p := by
  unfold loss
  bound [D.ten_thousand_le_m]

variable (D) in
/-- For odd `e` and an `a`-place `τ`, the place `D.placeOfInt (-p ^ e) * τ` is an `a`-place if and
only if `D.o₀ p` divides `e`. -/
lemma placeOfInt_mul_mem_aPlaces_iff {p e : ℕ} (he : Odd e) (τ : D.Φ) (hτ : τ ∈ D.aPlaces) :
    D.placeOfInt (-p ^ e) * τ ∈ D.aPlaces ↔ D.o₀ p ∣ e := by
  simp_all [← he.neg_pow, ← Parameters.placeOfInt_pow, o₀, aPlaces, orderOf_dvd_iff_pow_eq_one]

/-- If `(τ, e)` is a collision at `p` outside `S`, that is, `τ` and `placeOfInt (-p ^ e) * τ` are
`a`-places outside `S` and `e ∈ I_p` (it is odd, or `p = d`), then `p ≠ d`, and `e` is odd and
divisible by the order `o₀ p` of `-p` modulo `q₀`. -/
lemma IsCollision.ne_and_odd_and_dvd {p : ℕ} {S : Finset D.Φ} {τ : D.Φ} {e : ℕ}
    (h : D.IsCollision p S τ e) : p ≠ P.d ∧ Odd e ∧ D.o₀ p ∣ e := by
  grind [IsCollision, mem_positivePartnerExponents, mem_partnerExponents, aPlaces,
    ne_d_of_placeClass_eq, placeOfInt_mul_mem_aPlaces_iff]

/-- Let `p` be a prime and `S` a set of infinite places of `E` (`D.Φ` is the type of these places,
`f` their number). If every collision has `e ≥ o`, then `collisionSum p S`, the sum of `a / p ^ e`
over the collisions, is at most `2 f a / p ^ o`; here `a = D.a` is the length of a long row. -/
lemma collisionSum_le {S : Finset D.Φ} {o : ℕ}
    (h_le : ∀ {τ : D.Φ} {e : ℕ}, D.IsCollision p S τ e → o ≤ e) :
    D.collisionSum p S ≤ 2 * D.f * D.a / p ^ o := by
  classical
  -- At each of the `f` places the series starts at `e = o`, and as `p ≥ 2` its terms are at most
  -- those of the geometric series with first term `a / p ^ o` and ratio `1 / 2`.
  have h_place (τ : D.Φ) :
      ∑' e : ℕ, ite (D.IsCollision p S τ e) (D.a / p ^ e : ℝ) 0 ≤ D.a / p ^ o * 2 := by
    set t : ℕ → ℝ := fun e ↦ ite (D.IsCollision p S τ e) (D.a / p ^ e : ℝ) 0
    have h_support : Function.support t ⊆ Set.range (o + ·) :=
      fun e he ↦ le.dest (by grind)
    have h_bound (e : ℕ) : ‖t (o + e)‖ ≤ D.a / p ^ o * 2 / 2 / 2 ^ e :=
      calc ‖t (o + e)‖ ≤ (D.a / p ^ o / p ^ e : ℝ) := by
            unfold t
            split <;> simp [pow_add, ← div_div]; positivity
        _ ≤ D.a / p ^ o / 2 ^ e := by gcongr; exact mod_cast q.1.two_le
        _ = _ := by ring
    grw [← (add_right_injective o).tsum_eq h_support, le_norm_self (tsum _)]
    exact tsum_of_norm_bounded (hasSum_geometric_two' _) h_bound
  grw [collisionSum, h_place]
  simp [field]

/-- Let the prime `p` be below the cut-off `x₁`, non-split in `K = ℚ(√-d)` and not exceptional. Then
`m * collisionSum p ∅ ≤ loss p`, where `loss p` is `m f a (log b)² / p` if `p ≡ ±1` modulo `m` and
`f a (log b)² / p` otherwise. Here `m` is the number of lifts, `f` the number of infinite places of
`E`, and `a = x b` is the product of the scales `x` and `b` of the data. -/
lemma mul_collisionSum_le_loss (hp : D.IsSmallNonsplit p)
    (h_not_exceptional : ¬D.IsExceptional p) :
    D.m * D.collisionSum p ∅ ≤ D.loss p := by
  grw [loss, ← (D.le_of_hasLogBound : 2 ≤ D.logB ^ 2)]
  split
  · -- If `p ≡ ±1` modulo `m`, the loss has the factor `m`, and it is enough that exponents are
    -- positive.
    grw [collisionSum_le (o := 1) (by grind [IsCollision, mem_positivePartnerExponents])]
    grind
  · -- Otherwise a collision has `e` an odd multiple of `o₀`. So either there is none, or `o₀` is
    -- odd and exceeds `ceilLogLifts p`, as `p` is not exceptional; and `m ≤ p ^ ceilLogLifts p`.
    have h_far {τ : D.Φ} {e : ℕ} (hc : D.IsCollision p ∅ τ e) : D.ceilLogLifts p + 1 ≤ e := by
      obtain ⟨h_ne, h_odd, h_dvd⟩ := hc.ne_and_odd_and_dvd
      grind [IsExceptional, chiK_cases, Odd.of_dvd_nat, Nat.le_of_dvd h_odd.pos h_dvd]
    grw [collisionSum_le h_far, le_pow_clog q.1.one_lt D.m, ← ceilLogLifts]
    have hp_ne : p ≠ 0 := q.1.ne_zero
    simp [pow_succ, field]

/-- The least height `k` of a low column is below `n_{j+1}`. -/
lemma k_mem_range_n_succ (j : ℕ) : D.k ∈ range (D.n (j + 1)) := by simp [n]

variable {j : ℕ}

/-- The number `lowBoxes j σ` of boxes in the low columns at `σ` is at least `k w`, where
`w = D.weight σ` and `k` is the least height of a low column: the columns of height `k` alone have
that many boxes. -/
lemma mul_weight_le_lowBoxes (j : ℕ) (σ : D.Φ) : D.k * (D.weight σ : ℝ) ≤ D.lowBoxes j σ := by
  have h_single : D.k * (if D.k = 1 then 0 else D.columnCount σ D.k) ≤ D.lowBoxes j σ :=
    single_le_sum (f := fun h : ℕ ↦ h * if h = 1 then 0 else D.columnCount σ h) (by simp)
      (k_mem_range_n_succ j)
  grw [← h_single, weight_le_liftWeight_sub _ 1]
  rify
  gcongr
  norm_cast
  grind [columnCount]

/-- Let `j < m`, with `m = D.m` the number of lifts, and `σ : D.Φ` an infinite place of `E`. The
number `D.lowColumns j σ` of columns at `σ` of height below `n_{j+1}` and other than `1` is at most
`D.weight σ + x ^ 60`, where `x` is the scale `D.x`: there are about `D.weight σ` of height `k` and
at most `D.gap` of every other height. -/
lemma lowColumns_le (hj : j < D.m) (σ : D.Φ) :
    D.lowColumns j σ ≤ (D.weight σ : ℝ) + D.x ^ 60 := by
  -- The size of the rank, as an instance for `D.le_of_hasLogBound`, which compares orders of
  -- magnitude.
  have := D.hasLogUpper_of_le (D.n_mono hj)
  calc (D.lowColumns j σ : ℝ) ≤ D.liftWeight 1 σ + D.n (j + 1) * D.gap := by
        grw [lowColumns, columnCount_le]
        simp [k_mem_range_n_succ j, sum_add_distrib]
    _ ≤ D.weight σ + D.x ^ 60 := by
        grw [D.liftWeight_le_weight_add D.nat_le_of_hasLogBound, add_assoc]
        exact add_le_add le_rfl D.le_of_hasLogBound

/-- For `j < D.m`, the number `D.lowBoxes j σ` of boxes in the columns at `σ` of height below
`n_{j+1}` and different from `1` is at most `D.k * D.weight σ + D.x ^ 60`. -/
lemma lowBoxes_le (hj : j < D.m) (σ : D.Φ) :
    D.lowBoxes j σ ≤ D.k * (D.weight σ : ℝ) + D.x ^ 60 := by
  have := D.hasLogUpper_of_le (D.n_mono hj)
  calc (D.lowBoxes j σ : ℝ) ≤
        D.k * D.liftWeight 1 σ + (D.n (j + 1) * (D.n (j + 1) - 1) / 2 : ℕ) * D.gap := by
        grw [lowBoxes, columnCount_le]
        simp [k_mem_range_n_succ j, mul_add, sum_add_distrib, ← sum_mul, sum_range_id]
    _ ≤ D.k * D.weight σ + D.x ^ 60 := by
        grw [D.liftWeight_le_weight_add D.nat_le_of_hasLogBound, Nat.div_le_self, sub_le, mul_add,
          add_assoc]
        exact add_le_add le_rfl D.le_of_hasLogBound

/-- For `j < m` and an infinite place `σ` of weight `w = D.weight σ` (that is `a / x` at a `b`-place
and `a / x₁` at any other): the number of boxes in the low columns lies between `k w` and
`k w + x ^ 60`, and the number of low columns is at most `w + x ^ 60`. -/
lemma lowColumns_lowBoxes_bounds (hj : j < D.m) (σ : D.Φ) :
    D.k * (D.weight σ : ℝ) ≤ D.lowBoxes j σ ∧
    D.lowColumns j σ ≤ (D.weight σ : ℝ) + D.x ^ 60 ∧
    D.lowBoxes j σ ≤ D.k * (D.weight σ : ℝ) + D.x ^ 60 :=
  ⟨mul_weight_le_lowBoxes j σ, lowColumns_le hj σ, lowBoxes_le hj σ⟩

/-- For `j < D.m`, the number `boxes D.columnCount (D.n (j + 1))` of boxes in the columns of height
below `D.n (j + 1)` equals `D.a` times the number of a-places `D.aPlaces`, plus the sum over `σ` of
`D.lowBoxes j σ`, the boxes in columns at `σ` of height below `D.n (j + 1)` other than `1`. -/
lemma boxes_eq_aPlaces_add_low (_hj : j < D.m) :
    (boxes D.columnCount (D.n (j + 1)) : ℝ) = #D.aPlaces * D.a + ∑ σ : D.Φ,
      (D.lowBoxes j σ : ℝ) := by
  have h_one : 1 < D.n (j + 1) := by grind [n]
  have h_split (σ : D.Φ) (h : ℕ) : h * D.columnCount σ h =
      (if h = 1 then if σ ∈ D.aPlaces then D.a else 0 else 0) + h * if h = 1 then 0 else
        D.columnCount σ h := by
    split_ifs <;> simp_all [columnCount]
  simp_rw [boxes, h_split, sum_add_distrib]
  simp [lowBoxes, h_one]

/-- For `j < m` the boxes removed with the columns of height one at the places of `S` are the `a`
boxes at each a-place in `S`. -/
lemma boxes_sub_boxes_eraseHeightOne (hj : j < D.m) (S : Finset D.Φ) :
    (boxes D.columnCount (D.n (j + 1)) - boxes (eraseHeightOne D.columnCount S) (D.n (j + 1)) : ℝ)
      =
      #(D.aPlaces ∩ S) * D.a := by
  have h_card : (#D.aPlaces : ℝ) = #(D.aPlaces \ S) + #(D.aPlaces ∩ S) :=
    mod_cast (card_sdiff_add_card_inter D.aPlaces S).symm
  simp [-Nat.cast_sum, boxes_eq_aPlaces_add_low hj, boxes_eq_sum, heightOneColumns_eraseHeightOne,
    lowBoxCount_eraseHeightOne, sum_add_distrib, longRow, h_card, add_mul, sum_ite_mem, -mem_sdiff]

/-- Let `p` be a prime and `j < m`, the number of lifts. The diagram at an infinite place `τ` of `E`
has `D.columnCount τ h` columns of height `h`. Let `B` be the number of boxes of these diagrams, at
all places, in the columns of height below the rank `n_{j+1} = D.n (j + 1)`. Then
`1 + log_p (max B 1)` is at most `(log b) ^ 2`, where `b` is the largest scale of the data and
`log b = D.logB`. -/
lemma one_add_logb_boxes_le (hj : j < D.m) :
    1 + logb p (max (boxes D.columnCount (D.n (j + 1))) 1 : ℕ) ≤ D.logB ^ 2 := by
  have h_low (σ : D.Φ) : (D.lowBoxes j σ : ℝ) ≤ D.M :=
    (lowBoxes_le hj σ).trans D.le_of_hasLogBound
  have h_boxes : ((max (boxes D.columnCount (D.n (j + 1))) 1 : ℕ) : ℝ) ≤ D.f * D.a + D.f * D.M +
    1 := by
    grw [max_le_add_of_nonneg (Nat.zero_le _) zero_le_one, cast_add_one,
      boxes_eq_aPlaces_add_low hj,
      h_low, card_le_univ]
    simp [f, Core.numInfPlaces]
  have h_log : 1 / 2 ≤ Real.log p := by
    grw [← q.out.two_le]
    linarith [Real.log_two_gt_d9]
  calc _ ≤ 1 + Real.log (D.f * D.a + D.f * D.M + 1) / (1 / 2) := by
        grw [logb, ← h_log, h_boxes]
    _ ≤ D.logB ^ 2 := D.le_of_hasLogBound

/-- Let `j < m`, let the prime `p` be below the cut-off `x₁` and non-split in `K = ℚ(√-d)`, let
`e ∈ positivePartnerExponents P.d p`, let `S` be a set of infinite places of `E`, and let
`τ' = D.placeOfInt (-p ^ e) * τ` be the product of `τ` with the place of the class of `-p ^ e`
modulo `q₁`. With `a = x b` the product of the scales `x` and `b`, the weight `w = D.weight` is
`a / x` at the b-places and `a / x₁` elsewhere. Let `L = longRow S` be `a` at the a-places outside
`S` and `0` elsewhere, and let `c = lowColumns j` count the columns of height below `n_{j+1}` other
than `1`. For an a-place `τ` the number `(a / p ^ e - w τ')₊` is at most
`(L τ / p ^ e - L τ' - c τ')₊ + x ^ 60`, plus `a / p ^ e` if `τ ∈ S` or if `(τ, e)` is a collision.
For `τ ∈ S` and `e = 1` the bound still holds with `a / x₁` added on the left. -/
lemma posPart_sub_weight_le_posPart_longRow (hj : j < D.m) (hp : D.IsSmallNonsplit p)
    (S : Finset D.Φ) (τ : D.Φ) {e : ℕ} (he : e ∈ positivePartnerExponents P.d p)
    [Decidable (D.IsCollision p S τ e)] :
    (if τ ∈ D.aPlaces then (D.a / p ^ e - D.weight (D.placeOfInt (-p ^ e) * τ) : ℝ)⁺ else 0) +
        (if e = 1 ∧ τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) ≤
      (longRow S τ / p ^ e - longRow S (D.placeOfInt (-p ^ e) * τ) -
          D.lowColumns j (D.placeOfInt (-p ^ e) * τ))⁺ +
        (if τ ∈ D.aPlaces ∩ S then (D.a / p ^ e : ℝ) else 0) +
        (if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0) + D.x ^ 60 := by
  set τ' : D.Φ := D.placeOfInt (-p ^ e) * τ with hτ'
  have hp_pos : (0 : ℝ) < p := mod_cast q.out.pos
  have h_quot : (0 : ℝ) ≤ D.a / p ^ e := by positivity
  have h_err : 0 ≤ D.x ^ 60 := by positivity
  have h_weight : (D.a / D.x₁ : ℝ) ≤ D.weight τ' := (D.weight_mem_Icc τ').1
  by_cases h_aPlace : τ ∈ D.aPlaces
  swap
  · simp only [h_aPlace, mem_inter, false_and, and_false, ite_false, add_zero]
    positivity
  have h_nonneg : (0 : ℝ) ≤ D.weight τ' := Nat.cast_nonneg _
  simp only [IsCollision, ← hτ', mem_inter, mem_sdiff, h_aPlace, he, posPart_def, longRow]
  by_cases h_removed : τ ∈ S
  · -- A removed row: only the surplus at `e = 1` is to be absorbed.
    have h_surplus (h_one : e = 1) : (D.a / D.x₁ : ℝ) ≤ D.a / p ^ e := by
      simpa [h_one] using div_le_div_of_nonneg_left (Nat.cast_nonneg D.a) hp_pos hp.1.le
    grind
  · -- A row that stays: `τ'` is an a-place outside `S` (a collision), or its long row is empty.
    grind [lowColumns_le hj τ']

/-- For `j < m` and `z > 0`, the second term of the gain, `k (w(τ) / z - w(τ'))₊` with `w` the
weight and `k` the least height of a column other than `1`, exceeds the same expression in the boxes
of the low columns by at most `x ^ 60`. -/
lemma mul_posPart_weight_le (hj : j < D.m) (τ τ' : D.Φ) {z : ℝ} (hz : 0 < z) :
    D.k * (D.weight τ / z - D.weight τ')⁺ ≤ (D.lowBoxes j τ / z - D.lowBoxes j τ')⁺ + D.x ^ 60 := by
  have h_lower : D.k * (D.weight τ / z) ≤ D.lowBoxes j τ / z := by
    grw [← mul_div_assoc, mul_weight_le_lowBoxes j τ]
  rw [posPart_def, posPart_def, mul_max_of_nonneg _ _ (Nat.cast_nonneg _), mul_zero, mul_sub]
  grind [lowBoxes_le hj τ', show 0 ≤ D.x ^ 60 by positivity]

/-- Let `j < m`, the number of lifts, let `S` be a set of places, and let
`-τ = P.partner D.towerExp P.d 0 τ` be the product of `τ` with the place named by `-1`. Let
`L = longRow S` be `a = D.a` at the a-places outside `S` and `0` elsewhere, let `c = lowColumns j`
count the columns of height below `n_{j+1}` other than `1`, and let `l = lowBoxes j` count the boxes
in these columns. Then `min (L τ) (L (-τ) + c (-τ)) + c τ + min (l τ) (l (-τ))` is at most
`3 a / (d m)`, because `τ` and `-τ` are neither both a-places nor both b-places (class `-1`). -/
lemma min_longRow_add_lowColumns_add_min_lowBoxes_le (hj : j < D.m) (S : Finset D.Φ) (τ : D.Φ) :
    min (longRow S τ) (longRow S (P.partner D.towerExp P.d 0 τ) +
          D.lowColumns j (P.partner D.towerExp P.d 0 τ)) + D.lowColumns j τ +
        min (D.lowBoxes j τ : ℝ) (D.lowBoxes j (P.partner D.towerExp P.d 0 τ)) ≤
      3 * (D.a / P.d / D.m) := by
  set τ' : D.Φ := P.partner D.towerExp P.d 0 τ
  have h_class : P.placeClass ⟨towerDeg D.towerExp, rfl⟩ τ' ≠ P.placeClass
    ⟨towerDeg D.towerExp, rfl⟩ τ :=
    fun h_eq ↦ D.ne_d_of_placeClass_eq h_eq rfl
  set u : ℝ := D.a / P.d / D.m
  have h_columns (σ : D.Φ) : (D.lowColumns j σ : ℝ) ≤ u :=
    (lowColumns_le hj σ).trans D.le_of_hasLogBound
  have h_boxes (σ : D.Φ) (hσ : σ ∉ D.bPlaces) : (D.lowBoxes j σ : ℝ) ≤ u :=
    (lowBoxes_le hj σ).trans (by simpa [cast_weight, hσ] using D.le_of_hasLogBound)
  have h_rows : min (longRow S τ) (longRow S τ' + D.lowColumns j τ') ≤ u := by
    obtain h_not | h_not : τ ∉ D.aPlaces ∨ τ' ∉ D.aPlaces := by grind [aPlaces]
    · exact min_le_of_left_le (by simpa [longRow, h_not] using by positivity)
    · exact min_le_of_right_le (by simpa [longRow, h_not] using h_columns τ')
  have h_min : min (D.lowBoxes j τ : ℝ) (D.lowBoxes j τ') ≤ u := by
    obtain h_not | h_not : τ ∉ D.bPlaces ∨ τ' ∉ D.bPlaces := by grind [placeClass_of_mem_bPlaces]
    · exact min_le_of_left_le (h_boxes τ h_not)
    · exact min_le_of_right_le (h_boxes τ' h_not)
  linarith [h_columns τ]

/-- Let `p` be a prime, `j < m` (the number of lifts) and `S` a set of infinite places of `E`.
Remove from the diagrams `D.columnCount` the columns of height one at the places of `S`, and read
them at heights below `n_{j+1}`. Their `predictedDivisibility` at `p`, for the partner map
`P.partner D.towerExp p e τ = (-p ^ e) τ`, is by definition `v(π_p) = piPrimeValuation P.d p` times
the sum over all `e` and `τ` of `partnerTerm p j S τ e`, the term that compares the diagram at `τ`
with that at its partner, less a correction if `p = d`. The correction is at most `2 a / (p m)` for
each of the `f` places, where `a = D.a` is the length of a long row. -/
lemma sub_le_predictedDivisibility (hj : j < D.m) (S : Finset D.Φ) :
    piPrimeValuation P.d p * ∑ τ : D.Φ, ∑' e : ℕ, partnerTerm p j S τ e -
        D.f * (2 * (D.a / p / D.m)) ≤
      predictedDivisibility P.d p (P.partner D.towerExp p) (eraseHeightOne D.columnCount S)
        (D.n (j + 1)) := by
  simp only [predictedDivisibility, heightOneColumns_eraseHeightOne,
    lowColumnCount_eraseHeightOne, lowBoxCount_eraseHeightOne]
  rw [← Summable.tsum_finsetSum fun τ _ ↦ summable_partnerTerm j S τ]
  refine sub_le_sub (by simp only [partnerTerm, sum_ite_irrel, sum_const_zero, le_refl]) ?_
  split_ifs with h_ramified
  · subst h_ramified
    grw [sum_le_card_nsmul univ _ _ fun τ _ ↦
      min_longRow_add_lowColumns_add_min_lowBoxes_le hj S τ, nsmul_eq_mul]
    change (1 / 2 * (D.f * (3 * (D.a / P.d / D.m))) : ℝ) ≤ D.f * (2 * (D.a / P.d / D.m))
    linarith [show (0 : ℝ) ≤ D.f * (D.a / P.d / D.m) by positivity]
  · positivity

/-- For `j < D.m` and a place `τ`, the number `γ_p = gammaPrime P.d p` times the number
`D.lowColumns j τ` of columns at `τ` of height below `n_{j+1}` and different from `1` is at most
`D.a / p / D.m`. -/
lemma gammaPrime_mul_lowColumns_le (hj : j < D.m) (τ : D.Φ) :
    gammaPrime P.d p * D.lowColumns j τ ≤ D.a / p / D.m := by
  have h_inv : (1 / (p - 1) : ℝ) ≤ 2 / p := by
    rw [div_le_div_iff₀] <;> linarith [show (2 : ℝ) ≤ p from mod_cast q.out.two_le]
  calc _ ≤ 2 / p * (D.weight τ + D.x ^ 60) := by
        grw [gammaPrime_le_one_div, h_inv, lowColumns_le hj τ]
    _ ≤ D.a / p / D.m := by
        rw [div_mul_eq_mul_div, div_right_comm]
        exact div_le_div_of_nonneg_right D.le_of_hasLogBound p.cast_nonneg

open scoped Classical in
/-- The bound for the gain `D.gain p` at one infinite place `τ` of `E`. Let `j < m`, let the prime
`p` be below the cut-off `x₁` and non-split in `K = ℚ(√-d)`, and let `S` be a set of places whose
long rows are removed. Let `I_p = positivePartnerExponents P.d p`, `v = piPrimeValuation P.d p` and
`γ_p = gammaPrime P.d p = v ∑_{e ∈ I_p} 1 / p ^ e`. The weight `w = D.weight` is `a / x` at the
b-places and `a / x₁` elsewhere, `a = x b` being the product of two scales of the data, and
`s_p = localPrimeSum p` is the series `s_p(y, τ) = v ∑_{e ∈ I_p} (y / p ^ e - w((-p ^ e) τ))₊`. The
left side is the share of `τ` in `gain p / m`, namely `s_p(a, τ)` (for an a-place only, that is, of
class `1` modulo `q₀`) plus `k s_p(w(τ), τ)` with `k` the rank of the source, increased by
`v a / x₁` if `τ` is an a-place in `S`. It is at most `v` times the sum of three terms, plus `γ_p`
times the number `lowColumns j τ` of columns of height below `n_{j+1}` other than `1`, plus `γ_p a`
if `τ` is an a-place in `S`. The three terms are the series of `partnerTerm p j S τ e`, the series
of `a / p ^ e` over the `e ∈ I_p` such that `τ` and `(-p ^ e) τ` are a-places outside `S`
(collisions), and `2 x ^ 60` for each of the `clog p ⌈x₁⌉₊` exponents `e` with `p ^ e < x₁`. -/
lemma localPrimeSum_add_le_mul_tsum_partnerTerm_add (hj : j < D.m) (hp : D.IsSmallNonsplit p)
    (S : Finset D.Φ) (τ : D.Φ) :
    (if τ ∈ D.aPlaces then D.localPrimeSum p D.a τ else 0) +
        D.k * D.localPrimeSum p (D.weight τ) τ +
        piPrimeValuation P.d p * (if τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) ≤
      piPrimeValuation P.d p * ((∑' e : ℕ, partnerTerm p j S τ e) +
          (∑' e : ℕ, if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0) +
          clog p ⌈D.x₁⌉₊ * (2 * D.x ^ 60)) +
        gammaPrime P.d p * (D.lowColumns j τ + if τ ∈ D.aPlaces ∩ S then (D.a : ℝ) else 0) := by
  -- Divide by `v`. Each of the seven terms is then the sum of a series in `e`; compare the series
  -- term by term.
  have hv_pos : 0 < piPrimeValuation P.d p := piPrimeValuation_pos P.d p
  suffices h_div :
      (if τ ∈ D.aPlaces then 1 else 0) * (D.localPrimeSum p D.a τ / piPrimeValuation P.d p) +
          D.k * (D.localPrimeSum p (D.weight τ) τ / piPrimeValuation P.d p) +
          (if τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) ≤
        ∑' e : ℕ, partnerTerm p j S τ e +
          (D.lowColumns j τ + if τ ∈ D.aPlaces ∩ S then (D.a : ℝ) else 0) * gammaPrime P.d p /
            piPrimeValuation P.d p +
          (∑' e : ℕ, if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0) +
          clog p ⌈D.x₁⌉₊ * (2 * D.x ^ 60) by
    rw [← boole_mul (τ ∈ D.aPlaces)]
    refine le_of_eq_of_le ?_ ((mul_le_mul_of_nonneg_left h_div hv_pos.le).trans_eq ?_)
    · field
    · field
  have h_gain (y : ℝ) : HasSum (fun e : ℕ ↦ if e ∈ positivePartnerExponents P.d p then
        (y / p ^ e - D.weight (D.placeOfInt (-p ^ e) * τ))⁺ else 0)
      (D.localPrimeSum p y τ / piPrimeValuation P.d p) := by
    rw [localPrimeSum, mul_div_cancel_left₀ _ hv_pos.ne']
    exact (D.summable_posPart_sub_weight p y τ).hasSum
  have h_surplus : HasSum
      (fun e : ℕ ↦ if e = 1 then (if τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) else 0)
      (if τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) :=
    hasSum_ite_eq 1 _
  have h_full : HasSum (fun e : ℕ ↦ if e ∈ positivePartnerExponents P.d p then
        ((D.lowColumns j τ + if τ ∈ D.aPlaces ∩ S then (D.a : ℝ) else 0) / p ^ e : ℝ) else 0)
      ((D.lowColumns j τ + if τ ∈ D.aPlaces ∩ S then (D.a : ℝ) else 0) * gammaPrime P.d p /
        piPrimeValuation P.d p) :=
    hasSum_div_pow_positivePartnerExponents P.d p _
  have h_coll : Summable fun e : ℕ ↦ if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0 := by
    refine (hasSum_div_pow_positivePartnerExponents P.d p D.a).summable.of_nonneg_of_le
      (fun e ↦ by positivity) fun e ↦ ?_
    by_cases h_collision : D.IsCollision p S τ e
    · rw [ite_eq_left h_collision, ite_eq_left h_collision.1]
    · rw [ite_eq_right h_collision]
      positivity
  have h_err : HasSum (fun e : ℕ ↦ if e ∈ range (clog p ⌈D.x₁⌉₊) then 2 * D.x ^ 60 else 0)
      (clog p ⌈D.x₁⌉₊ * (2 * D.x ^ 60)) := by
    convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (s := range (clog p ⌈D.x₁⌉₊)) (fun e he ↦ ite_eq_right he) using 1
    simp [sum_ite_of_true]
  refine hasSum_le (fun e ↦ ?_)
    ((((h_gain D.a).mul_left _).add ((h_gain (D.weight τ)).mul_left _)).add h_surplus)
    ((((summable_partnerTerm j S τ).hasSum.add h_full).add h_coll.hasSum).add h_err)
  by_cases he : e ∈ positivePartnerExponents P.d p
  swap
  · have h_ne : e ≠ 1 := fun h_one ↦
      he (by simpa [h_one] using one_mem_positivePartnerExponents hp.2)
    simpa [partnerTerm, IsCollision, he, h_ne] using by positivity
  simp only [partnerTerm, he, ite_true, add_div, ite_div, zero_div, ite_mul, one_mul, zero_mul,
    ← ite_and, Parameters.partner]
  by_cases h_small : e ∈ range (clog p ⌈D.x₁⌉₊)
  · rw [ite_eq_left h_small]
    linarith [posPart_sub_weight_le_posPart_longRow hj hp S τ he, mul_posPart_weight_le hj τ
      (D.placeOfInt (-p ^ e) * τ) (pow_pos (Nat.cast_pos.2 q.out.pos) e)]
  · -- Here `p ^ e ≥ x₁`, so the terms of the gain vanish, as every weight is at least `a / x₁`.
    have h_pow : D.x₁ ≤ p ^ e := (Nat.le_ceil D.x₁).trans <| mod_cast
      (le_pow_clog q.out.one_lt _).trans (Nat.pow_le_pow_right q.out.pos (by simpa using h_small))
    have h_zero {y : ℝ} (hy : y ≤ D.a) (σ : D.Φ) : (y / p ^ e - D.weight σ)⁺ = 0 :=
      posPart_eq_zero.2 <| sub_nonpos.2 <|
        (div_le_div₀ (Nat.cast_nonneg _) hy (HasLogBound.pos D) h_pow).trans (D.weight_mem_Icc σ).1
    have h_ne : e ≠ 1 := fun h_one ↦ hp.1.not_ge (by simpa [h_one] using h_pow)
    simp only [h_zero le_rfl, h_zero (D.le_of_hasLogBound : (D.weight τ : ℝ) ≤ D.a), h_ne, h_small,
      false_and, ite_false, ite_self, mul_zero, add_zero, ← add_assoc, sub_add_cancel]
    positivity

/-- **Only collisions lose.** Let the prime `p` be below the cut-off `x₁` and non-split in
`K = ℚ(√-d)`, let `j < m`, the number of lifts, and let `S` be any set of infinite places of `E`.
The bound `divisibilityBound p j S` is the predicted divisibility at `p` of the diagrams
`D.columnCount`, read below height `n_{j+1}` and with the columns of height one at `S` removed, plus
`γ_p` for each removed box, less a logarithmic term. It is at least
`gain p / m = ∑_τ s_p(a, τ) + k ∑_σ s_p(w(σ), σ)` (with `τ` an a-place, that is, of class `1` modulo
`q₀`, `σ` any place, `s_p = localPrimeSum p` and `w = D.weight`), less `collisionSum p S`, the sum
of `a / p ^ e` over the pairs `(τ, e)` with `e ∈ I_p` and both `τ` and `(-p ^ e) τ` a-places outside
`S`, plus `v(π_p) a / x₁` for each a-place in `S`, less `f a (log b)² / (m p)`. Here
`v(π_p) = piPrimeValuation P.d p`, `a = x b` is the length of a long row, `log b = D.logB`, and `f`
is the number of infinite places of `E`. -/
lemma le_divisibilityBound (hj : j < D.m) (hp : D.IsSmallNonsplit p) (S : Finset D.Φ) :
    D.gain p / D.m - D.collisionSum p S +
        piPrimeValuation P.d p * #(D.aPlaces ∩ S) * (D.a / D.x₁) -
        D.f * D.logB ^ 2 * (D.a / p) / D.m ≤
      D.divisibilityBound p j S := by
  classical
  -- Put `u = a / (p m)`. Apart from collisions the losses at one place add up to at most `5 u`.
  -- The sizes of the rank and of `p`, as instances for `D.le_of_hasLogBound`.
  have := D.hasLogUpper_of_le (D.n_mono hj)
  have hp_size : D.HasLogUpper p D.logX₁ := D.hasLogUpper_of_le_of_nonneg hp.1.le p.cast_nonneg
  set u : ℝ := D.a / p / D.m with hu
  set γ : ℝ := gammaPrime P.d p
  set v : ℝ := piPrimeValuation P.d p
  have hv_pos : 0 < v := piPrimeValuation_pos P.d p
  have hv_le : v ≤ 1 := piPrimeValuation_le_one P.d p
  have h_err : v * (clog p ⌈D.x₁⌉₊ * (2 * D.x ^ 60)) ≤ u := by
    grw [hv_le, one_mul, clog_le_of_le_pow (Nat.lt_pow_self q.out.one_lt).le,
      Nat.ceil_lt_add_one (HasLogBound.pos D).le]
    exact D.le_of_hasLogBound
  have h_place (τ : D.Φ) :
      (if τ ∈ D.aPlaces then D.localPrimeSum p D.a τ else 0) +
          D.k * D.localPrimeSum p (D.weight τ) τ +
          v * (if τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) ≤
        v * ∑' e, partnerTerm p j S τ e + γ * (if τ ∈ D.aPlaces ∩ S then (D.a : ℝ) else 0) +
          (∑' e : ℕ, if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0) + 2 * u := by
    -- A collision costs at most `v ≤ 1` times its term.
    linarith [localPrimeSum_add_le_mul_tsum_partnerTerm_add hj hp S τ,
      gammaPrime_mul_lowColumns_le (p := p) hj τ,
      mul_le_of_le_one_left (tsum_nonneg fun e ↦ by positivity :
        0 ≤ ∑' e : ℕ, if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0) hv_le]
  have h_sum : ∑ τ ∈ D.aPlaces, D.localPrimeSum p D.a τ + D.k * D.localPrimeSumTotal p +
        v * #(D.aPlaces ∩ S) * (D.a / D.x₁) ≤
      v * ∑ τ, ∑' e, partnerTerm p j S τ e + γ * (#(D.aPlaces ∩ S) * D.a) + D.collisionSum p S +
        D.f * (2 * u) := by
    simpa [sum_add_distrib, ← mul_sum, localPrimeSumTotal, collisionSum, mul_assoc, mul_left_comm,
      f,
      Core.numInfPlaces, -mem_inter] using
      sum_le_sum (s := univ) fun τ _ ↦ h_place τ
  have h_count : D.n (j + 1) ^ 3 * (1 + logb p (max (boxes D.columnCount (D.n (j + 1))) 1 : ℕ)) ≤
    u := by
    grw [one_add_logb_boxes_le hj]
    exact D.le_of_hasLogBound
  have h_losses : D.f * (5 * u) ≤ D.f * D.logB ^ 2 * (D.a / p) / D.m := by
    grw [mul_div_assoc, mul_assoc, ← hu, (D.le_of_hasLogBound : 5 ≤ D.logB ^ 2)]
  rw [divisibilityBound, boxes_sub_boxes_eraseHeightOne hj, gain,
    mul_div_cancel_left₀ _ (HasLogBound.pos D).ne', mul_assoc (D.f : ℝ) (_ ^ 3)]
  have h_predicted : v * ∑ τ, ∑' e, partnerTerm p j S τ e - D.f * (2 * u) ≤
      predictedDivisibility P.d p (P.partner D.towerExp p) (eraseHeightOne D.columnCount S)
        (D.n (j + 1)) :=
    sub_le_predictedDivisibility (p := p) hj S
  linarith [mul_le_mul_of_nonneg_left h_count (D.f.cast_nonneg (α := ℝ))]

end DivisibilityBound

end New.Data

end
