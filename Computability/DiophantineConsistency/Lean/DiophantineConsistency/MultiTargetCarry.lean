import DiophantineConsistency.MultiQuadraticCoding
import Diophantine.Paper1982.Packing

/-!
# A simultaneous signed coefficient test by carries and central divisibility

All selected positions are tested individually by one binary no-carry mask.
The strict half-base coefficient bound is an explicit hypothesis, so this
lemma never identifies a coefficient with a digit in the presence of carries.
The central-binomial corollary retains explicit bounds on its two packed
integers. Those bounds must still be discharged by a concrete source adapter.
-/

namespace DiophantineConsistency.MultiTargetCarry

open Polynomial Finset Jones1982
open SidonPositions QuadraticCoding MultiQuadraticCoding
open scoped BigOperators

/-- The shifted coefficient digits, evaluated in the power-of-two base. -/
def shiftedValue (t n : ℕ) (h : ℕ → ℤ) : ℕ :=
  Nat.ofDigits (2 ^ t) ((List.range n).map fun i => (h i + 2 ^ (t - 1)).toNat)

/-- A digit mask selecting any supplied finite set of positions. -/
def selectedMask (t n : ℕ) (positions : Finset ℕ) : ℕ :=
  Nat.ofDigits (2 ^ t) ((List.range n).map fun i =>
    if i ∈ positions then 2 ^ (t - 1) - 1 else 0)

private theorem map_range_getD (f : ℕ → ℕ) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

private theorem shifted_digit_bounds {t : ℕ} (ht : 1 ≤ t) {z : ℤ}
    (hz : |z| < 2 ^ (t - 1)) :
    0 < (z + 2 ^ (t - 1)).toNat ∧ (z + 2 ^ (t - 1)).toNat < 2 ^ t := by
  have hpos : 0 < z + 2 ^ (t - 1) := by
    have := (abs_lt.mp hz).1
    linarith
  have hpow : (2 : ℤ) ^ t = 2 * 2 ^ (t - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel ht]
  have hlt : z + 2 ^ (t - 1) < 2 ^ t := by
    have := (abs_lt.mp hz).2
    linarith
  constructor
  · rw [Int.lt_toNat]
    push_cast
    exact hpos
  · rw [Int.toNat_lt hpos.le]
    push_cast
    exact hlt

/-- The numerical mask is the exact sparse sum of the selected cells. -/
theorem selectedMask_eq {n : ℕ} (t : ℕ) (positions : Finset ℕ)
    (hp : ∀ i ∈ positions, i < n) :
    selectedMask t n positions =
      (2 ^ (t - 1) - 1) * ∑ i ∈ positions, (2 ^ t) ^ i := by
  rw [selectedMask, ofDigits_map_range]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter,
    Finset.filter_mem_eq_of_subset (fun i hi => mem_range.mpr (hp i hi)), Finset.mul_sum]

/-- No-carry of one mask is exactly the conjunction of the selected signed zeros. -/
theorem tau_shifted_selected_iff {t n : ℕ} (ht : 1 ≤ t)
    (positions : Finset ℕ) (hp : ∀ i ∈ positions, i < n)
    (h : ℕ → ℤ) (hb : ∀ i < n, |h i| < 2 ^ (t - 1)) :
    τ 2 (shiftedValue t n h) (selectedMask t n positions) = 0 ↔
      ∀ i ∈ positions, h i = 0 := by
  have hd : ∀ x ∈ (List.range n).map (fun i => (h i + 2 ^ (t - 1)).toNat), x < 2 ^ t := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact (shifted_digit_bounds ht (hb i (List.mem_range.mp hi))).2
  have hm : ∀ x ∈ (List.range n).map
      (fun i => if i ∈ positions then 2 ^ (t - 1) - 1 else 0), x < 2 ^ t := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    have hpow : 2 ^ (t - 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
    have hpos : 0 < 2 ^ (t - 1) := by positivity
    split <;> omega
  rw [shiftedValue, selectedMask,
    tau_ofDigits_iff (B := 2 ^ t) (n := n) rfl hd hm (by simp) (by simp)]
  constructor
  · intro hn i hi
    have hc := hn i (hp i hi)
    rw [map_range_getD _ (hp i hi), map_range_getD _ (hp i hi), if_pos hi] at hc
    apply (lemma_2_8' ht (hb i (hp i hi))).mpr
    simpa only [add_comm] using hc
  · intro hz i hi
    rw [map_range_getD _ hi, map_range_getD _ hi]
    by_cases hip : i ∈ positions
    · rw [if_pos hip]
      have hc := (lemma_2_8' ht (hb i hi)).mp (hz i hip)
      simpa only [add_comm] using hc
    · rw [if_neg hip]
      exact τ_zero_right _

/-- The shift has exactly the stated finite integer value. -/
theorem shiftedValue_cast (t n : ℕ) (h : ℕ → ℤ)
    (hb : ∀ i < n, |h i| < 2 ^ (t - 1)) :
    (shiftedValue t n h : ℤ) =
      ∑ i ∈ range n, (h i + 2 ^ (t - 1)) * (2 ^ t : ℤ) ^ i := by
  rw [shiftedValue, ofDigits_map_range]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hpos : 0 ≤ h i + 2 ^ (t - 1) := by
    have := (abs_lt.mp (hb i (mem_range.mp hi))).1
    linarith
  rw [Int.toNat_of_nonneg hpos]

/-- Doubling both arguments preserves the simultaneous carry test. -/
theorem tau_doubled_selected_iff {t n : ℕ} (ht : 1 ≤ t)
    (positions : Finset ℕ) (hp : ∀ i ∈ positions, i < n)
    (h : ℕ → ℤ) (hb : ∀ i < n, |h i| < 2 ^ (t - 1)) :
    τ 2 (2 * shiftedValue t n h) (2 * selectedMask t n positions) = 0 ↔
      ∀ i ∈ positions, h i = 0 := by
  have hs := lemma_2_4_τ 1 (shiftedValue t n h) (selectedMask t n positions)
  simp only [pow_one] at hs
  rw [hs]
  exact tau_shifted_selected_iff ht positions hp h hb

/-- In the doubled version, the sparse mask has the article's `B-2` factor. -/
theorem doubledMask_eq {t n : ℕ} (ht : 1 ≤ t) (positions : Finset ℕ)
    (hp : ∀ i ∈ positions, i < n) :
    2 * selectedMask t n positions = (2 ^ t - 2) * ∑ i ∈ positions, (2 ^ t) ^ i := by
  have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel ht]
  have hhalf : 1 ≤ 2 ^ (t - 1) := Nat.one_le_two_pow
  have hfactor : 2 ^ t - 2 = 2 * (2 ^ (t - 1) - 1) := by omega
  rw [selectedMask_eq t positions hp, hfactor]
  ring

/-- The standard central-binomial rank code, with supplied simultaneous-test data. -/
def centralRank (t n α : ℕ) (positions : Finset ℕ) (h : ℕ → ℤ) : ℕ :=
  centralCode (2 ^ α) (2 * shiftedValue t n h) (2 * selectedMask t n positions)

/-- The simultaneous zeros are equivalent to one central-binomial divisibility
condition once its explicit numerical size conditions have been proved. -/
theorem central_divisibility_iff {t n α : ℕ} (ht : 1 ≤ t)
    (positions : Finset ℕ) (hp : ∀ i ∈ positions, i < n)
    (h : ℕ → ℤ) (hb : ∀ i < n, |h i| < 2 ^ (t - 1))
    (hS : 2 * shiftedValue t n h < 2 ^ α)
    (hT : 2 * selectedMask t n positions < 2 ^ α) :
    (2 ^ α) ^ 2 ∣ (2 * centralRank t n α positions h).choose
      (centralRank t n α positions h) ↔ ∀ i ∈ positions, h i = 0 := by
  have hc := lemma_2_16 hS hT
    (R := centralRank t n α positions h) rfl
  exact hc.symm.trans (tau_doubled_selected_iff ht positions hp h hb)

/-- The target cells of a supplied finite quadratic family. -/
def targetPositions (m r : ℕ) : Finset ℕ :=
  univ.image (fun j : Fin r => target m j.val)

theorem targetPositions_bounded (m r : ℕ) :
    ∀ i ∈ targetPositions m r, i < targetBound m r := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := mem_image.mp hi
  exact target_lt_bound m j

/-- The single ordinary polynomial whose selected coefficients are the row values. -/
noncomputable def rowProduct {m r : ℕ} (a : Fin r → PairIndex m → ℤ)
    (u : Fin (m + 1) → ℤ) : ℤ[X] := encoded u ^ 2 * combined a

/-- The complete support interval of every finite row stays below the bound. -/
theorem target_upper_lt_bound (m : ℕ) {r : ℕ} (j : Fin r) :
    target m j.val + coefficientPosition m < targetBound m r := by
  have h := Nat.mul_le_mul_right (stride m) (Nat.succ_le_of_lt j.isLt)
  rw [Nat.succ_mul] at h
  dsimp only [target, targetBound, stride] at *
  omega

/-- No omitted higher coefficient exists beyond the finite digit block. -/
theorem coeff_rowProduct_eq_zero_of_bound {m r : ℕ}
    (a : Fin r → PairIndex m → ℤ) (u : Fin (m + 1) → ℤ)
    {n : ℕ} (hn : targetBound m r ≤ n) : (rowProduct a u).coeff n = 0 := by
  rw [rowProduct, combined, Finset.mul_sum, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  apply coeff_row_eq_zero_of_outside
  right
  exact (target_upper_lt_bound m j).trans_le hn

theorem rowProduct_degree_lt {m r : ℕ} (hr : 0 < r)
    (a : Fin r → PairIndex m → ℤ) (u : Fin (m + 1) → ℤ) :
    (rowProduct a u).natDegree < targetBound m r := by
  have hbound : 0 < targetBound m r := by
    exact Nat.mul_pos hr (by unfold stride; omega)
  have hdegree : (rowProduct a u).natDegree ≤ targetBound m r - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    apply coeff_rowProduct_eq_zero_of_bound a u
    omega
  omega

/-- The finite shifted digits evaluate to the full polynomial plus its offset,
not merely to a truncation of the polynomial. -/
theorem shifted_rowProduct_cast {m r : ℕ} (hr : 0 < r) (t : ℕ)
    (a : Fin r → PairIndex m → ℤ) (u : Fin (m + 1) → ℤ)
    (hb : ∀ i < targetBound m r, |(rowProduct a u).coeff i| < 2 ^ (t - 1)) :
    (shiftedValue t (targetBound m r) (rowProduct a u).coeff : ℤ) =
      (rowProduct a u).eval (2 ^ t) +
        (2 ^ (t - 1) : ℤ) * ∑ i ∈ range (targetBound m r), (2 ^ t : ℤ) ^ i := by
  rw [shiftedValue_cast t _ _ hb]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← eval_eq_sum_range' (rowProduct_degree_lt hr a u) (2 ^ t : ℤ)]

/-- The doubled shifted value is the expected signed-polynomial evaluation
with a positive `B`-multiple geometric offset. -/
theorem doubled_shifted_rowProduct_cast {m r t : ℕ} (hr : 0 < r) (ht : 1 ≤ t)
    (a : Fin r → PairIndex m → ℤ) (u : Fin (m + 1) → ℤ)
    (hb : ∀ i < targetBound m r, |(rowProduct a u).coeff i| < 2 ^ (t - 1)) :
    ((2 * shiftedValue t (targetBound m r) (rowProduct a u).coeff : ℕ) : ℤ) =
      2 * (rowProduct a u).eval (2 ^ t) +
        (2 ^ t : ℤ) * ∑ i ∈ range (targetBound m r), (2 ^ t : ℤ) ^ i := by
  push_cast
  rw [shifted_rowProduct_cast hr t a u hb]
  have hpow : (2 : ℤ) ^ t = 2 * 2 ^ (t - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel ht]
  rw [hpow]
  ring

/-- Selected coefficient zeros mean every row is zero, with no cancellation
between different rows. -/
theorem selected_coefficients_iff {m r : ℕ} (a : Fin r → PairIndex m → ℤ)
    (u : Fin (m + 1) → ℤ) :
    (∀ i ∈ targetPositions m r, (rowProduct a u).coeff i = 0) ↔
      ∀ j : Fin r, quadraticValue (a j) u = 0 := by
  constructor
  · intro hz j
    have hc := hz (target m j.val) (mem_image.mpr ⟨j, mem_univ _, rfl⟩)
    rw [rowProduct, coeff_square_mul_combined] at hc
    exact (mul_eq_zero.mp hc).resolve_left (by decide)
  · intro hz i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    rw [rowProduct, coeff_square_mul_combined, hz j, mul_zero]

/-- The proved multi-quadratic coefficient encoding now feeds one literal
binary no-carry test. The half-base magnitude bound remains explicit. -/
theorem tau_quadratics_iff {m r t : ℕ} (ht : 1 ≤ t)
    (a : Fin r → PairIndex m → ℤ) (u : Fin (m + 1) → ℤ)
    (hb : ∀ i < targetBound m r, |(rowProduct a u).coeff i| < 2 ^ (t - 1)) :
    τ 2 (2 * shiftedValue t (targetBound m r) (rowProduct a u).coeff)
      (2 * selectedMask t (targetBound m r) (targetPositions m r)) = 0 ↔
      ∀ j : Fin r, quadraticValue (a j) u = 0 :=
  (tau_doubled_selected_iff ht (targetPositions m r) (targetPositions_bounded m r)
    (rowProduct a u).coeff hb).trans (selected_coefficients_iff a u)

/-- Central-binomial divisibility for the same supplied quadratic family,
conditional only on the displayed arithmetic magnitude and packing bounds. -/
theorem central_quadratics_iff {m r t α : ℕ} (ht : 1 ≤ t)
    (a : Fin r → PairIndex m → ℤ) (u : Fin (m + 1) → ℤ)
    (hb : ∀ i < targetBound m r, |(rowProduct a u).coeff i| < 2 ^ (t - 1))
    (hS : 2 * shiftedValue t (targetBound m r) (rowProduct a u).coeff < 2 ^ α)
    (hT : 2 * selectedMask t (targetBound m r) (targetPositions m r) < 2 ^ α) :
    (2 ^ α) ^ 2 ∣
      (2 * centralRank t (targetBound m r) α (targetPositions m r) (rowProduct a u).coeff).choose
        (centralRank t (targetBound m r) α (targetPositions m r) (rowProduct a u).coeff) ↔
      ∀ j : Fin r, quadraticValue (a j) u = 0 :=
  (central_divisibility_iff ht (targetPositions m r) (targetPositions_bounded m r)
    (rowProduct a u).coeff hb hS hT).trans (selected_coefficients_iff a u)

end DiophantineConsistency.MultiTargetCarry
