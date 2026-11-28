import GRHArticle.ProgressionFree.FiniteGPMaskCertificate
import GRHArticle.ProgressionFree.FourPrimeLowBoxData
import GRHArticle.ProgressionFree.FourPrimeWeightedLineCapacities

/-!
# Weighted capacities of the whole four-prime candidate mask

The mixed-radix coding makes every nine-bit group a line with the last
three exponents fixed. The total score is bounded by the sum of the
certified weighted line capacities.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The index stores the first exponent in its least significant digit. -/
def fourPrimeEncode (a : Fin 4 → ℕ) : ℕ :=
  a 0 + 9*(a 1 + 9*(a 2 + 3*a 3))

/-- Decode an index of the (9\times9\times3\times3) box. -/
def fourPrimeDecode (j : ℕ) : Fin 4 → ℕ :=
  ![j%9,j/9%9,j/81%3,j/243]

/-- One position on the line with the last three coordinates fixed. -/
def fourPrimeRowPoint (row a : ℕ) : Fin 4 → ℕ :=
  ![a,row%9,row/9%3,row/27]

theorem fourPrimeDecode_eq_rowPoint (j : ℕ) :
    fourPrimeDecode j = fourPrimeRowPoint (j/9) (j%9) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · change (j/81)%3 = (j/9/9)%3
    rw [Nat.div_div_eq_div_mul]
  · change j/243 = j/9/27
    rw [Nat.div_div_eq_div_mul]

theorem fourPrimeDecode_rowPoint (row a : ℕ) (ha : a < 9) :
    fourPrimeDecode (9*row+a) = fourPrimeRowPoint row a := by
  rw [fourPrimeDecode_eq_rowPoint]
  have hd : (9*row+a)/9 = row := by omega
  have hm : (9*row+a)%9 = a := by omega
  rw [hd,hm]

theorem fourPrimeEncode_lt {a : Fin 4 → ℕ} (ha : a ∈ exponentBox fourPrimeLowBoxLimit) :
    fourPrimeEncode a < 729 := by
  have h := mem_exponentBox.mp ha
  have h₀ : a 0 ≤ 8 := h 0
  have h₁ : a 1 ≤ 8 := h 1
  have h₂ : a 2 ≤ 2 := h 2
  have h₃ : a 3 ≤ 2 := h 3
  unfold fourPrimeEncode
  omega

theorem fourPrimeDecode_encode {a : Fin 4 → ℕ} (ha : a ∈ exponentBox fourPrimeLowBoxLimit) :
    fourPrimeDecode (fourPrimeEncode a) = a := by
  have h := mem_exponentBox.mp ha
  have h₀ : a 0 ≤ 8 := h 0
  have h₁ : a 1 ≤ 8 := h 1
  have h₂ : a 2 ≤ 2 := h 2
  have h₃ : a 3 ≤ 2 := h 3
  funext i
  fin_cases i
  · change (a 0+9*(a 1+9*(a 2+3*a 3)))%9 = a 0
    omega
  · change (a 0+9*(a 1+9*(a 2+3*a 3)))/9%9 = a 1
    omega
  · change (a 0+9*(a 1+9*(a 2+3*a 3)))/81%3 = a 2
    omega
  · change (a 0+9*(a 1+9*(a 2+3*a 3)))/243 = a 3
    omega

private theorem mem_greedyExponents_of_lt_nine_iff {a : ℕ} (ha : a < 9) :
    a ∈ greedyExponents ↔ a%3 ≤ 1 ∧ a/3 ≤ 1 := by
  rw [mem_greedyExponents_iff a,mem_greedyExponents_iff (a/3),
    Nat.mod_eq_of_lt (show a/3 < 3 by omega),Nat.div_eq_of_lt (show a/3 < 3 by omega)]
  simp [zero_mem_greedyExponents]

private theorem mem_greedyExponents_of_lt_three_iff {a : ℕ} (ha : a < 3) :
    a ∈ greedyExponents ↔ a ≤ 1 := by
  rw [mem_greedyExponents_iff a,Nat.mod_eq_of_lt ha,Nat.div_eq_of_lt ha]
  simp [zero_mem_greedyExponents]

/-- The fixed coordinates contribute this common integer factor. -/
def fourPrimeRowFactor (q : Fin 4 → ℕ) (row : ℕ) : ℕ :=
  q 1^(8-row%9) * (q 2^(2-row/9%3) * q 3^(2-row/27))

/-- Whether all the fixed coordinates in the line pass the ternary test. -/
def fourPrimeRowOtherGood (row : ℕ) : Bool :=
  decide (row%9%3 ≤ 1 ∧ row%9/3 ≤ 1 ∧ row/9%3 ≤ 1 ∧ row/27 ≤ 1)

private theorem fourPrimeBoxGood_rowPoint (row a : ℕ) (hr : row < 81) (ha : a < 9) :
    fourPrimeBoxGood (fourPrimeRowPoint row a) =
      (fourPrimeRowOtherGood row && decide (a%3 ≤ 1 ∧ a/3 ≤ 1)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [fourPrimeBoxGood_iff,Bool.and_eq_true,fourPrimeRowOtherGood,decide_eq_true_eq]
  have h₁ : row%9 < 9 := Nat.mod_lt _ (by decide)
  have h₂ : row/9%3 < 3 := Nat.mod_lt _ (by decide)
  have h₃ : row/27 < 3 := by omega
  constructor
  · intro h
    have h1 := (mem_greedyExponents_of_lt_nine_iff h₁).mp (h 1)
    have h2 := (mem_greedyExponents_of_lt_three_iff h₂).mp (h 2)
    have h3 := (mem_greedyExponents_of_lt_three_iff h₃).mp (h 3)
    exact ⟨⟨h1.1,h1.2,h2,h3⟩,(mem_greedyExponents_of_lt_nine_iff ha).mp (h 0)⟩
  · rintro ⟨⟨h₀,h₁',h₂',h₃'⟩,ha'⟩ i
    fin_cases i
    · exact (mem_greedyExponents_of_lt_nine_iff ha).mpr ha'
    · exact (mem_greedyExponents_of_lt_nine_iff h₁).mpr ⟨h₀,h₁'⟩
    · exact (mem_greedyExponents_of_lt_three_iff h₂).mpr h₂'
    · exact (mem_greedyExponents_of_lt_three_iff h₃).mpr h₃'

theorem fourPrimeBoxScore_rowPoint (q : Fin 4 → ℕ) (row a : ℕ) (hr : row < 81) (ha : a < 9) :
    fourPrimeBoxScore q (fourPrimeRowPoint row a) =
      fourPrimeRowFactor q row * fourPrimeLineScore (q 0) (fourPrimeRowOtherGood row) a := by
  rw [fourPrimeBoxScore,fourPrimeBoxGood_rowPoint row a hr ha]
  change _ * (q 0^(8-a) * fourPrimeRowFactor q row) = _
  rw [fourPrimeLineScore]
  ring

/-- An admitted subset of a single row, written in first-coordinate indices. -/
def fourPrimeRowSubset (A : Finset ℕ) (row : ℕ) : Finset ℕ :=
  (A.filter (fun j ↦ j/9=row)).image (· %9)

/-- Bound the candidate mask by summing the certified capacities of its lines. -/
def fourPrimeMaskCapacity (q : Fin 4 → ℕ) (mask : ℕ) : ℕ :=
  ((List.range 81).map (fun row ↦ fourPrimeRowFactor q row *
    fourPrimeLineCapacity (q 0) (fourPrimeRowOtherGood row) (mask >>> (9*row)))).sum

/-- The total integer score of admissible codes fits their masked capacities. -/
theorem sum_fourPrimeCodeScore_le_maskCapacity (q : Fin 4 → ℕ) (hP : q 0 = 2 ∨ q 0 = 3)
    (A : Finset ℕ) (hA : A ⊆ range 729)
    (hFree : ∀ row < 81, ThreeAPFree (fourPrimeRowSubset A row : Set ℕ))
    (mask : ℕ) (hMask : gpMaskContains A mask) :
    (∑ a ∈ A, fourPrimeBoxScore q (fourPrimeDecode a)) ≤ fourPrimeMaskCapacity q mask := by
  have hMap : ∀ a ∈ A, a/9 ∈ range 81 := by
    intro a ha
    have h := mem_range.mp (hA ha)
    exact mem_range.mpr (by omega)
  rw [←sum_fiberwise_of_maps_to hMap]
  change _ ≤ ∑ row ∈ range 81, fourPrimeRowFactor q row *
    fourPrimeLineCapacity (q 0) (fourPrimeRowOtherGood row) (mask >>> (9*row))
  apply sum_le_sum
  intro row hRow
  have hr := mem_range.mp hRow
  let S := A.filter (fun j ↦ j/9=row)
  let T := fourPrimeRowSubset A row
  have hSub : T ⊆ range 9 := by
    intro a ha
    obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    exact mem_range.mpr (Nat.mod_lt _ (by decide))
  have hInj : Set.InjOn (·%9) (S : Set ℕ) := by
    intro a ha b hb he
    have h₁ := (mem_filter.mp ha).2
    have h₂ := (mem_filter.mp hb).2
    change a%9 = b%9 at he
    omega
  have hB (a : ℕ) (ha : a ∈ T) : (mask >>> (9*row)).testBit a = true := by
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    have hz := (mem_filter.mp hj).2
    rw [Nat.testBit_shiftRight,show 9*row+j%9 = j by omega]
    exact hMask j (mem_filter.mp hj).1
  calc
    (∑ j ∈ S, fourPrimeBoxScore q (fourPrimeDecode j)) =
        ∑ j ∈ S, fourPrimeRowFactor q row * fourPrimeLineScore (q 0) (fourPrimeRowOtherGood row) (j%9) := by
      apply sum_congr rfl
      intro j hj
      rw [fourPrimeDecode_eq_rowPoint,(mem_filter.mp hj).2]
      exact fourPrimeBoxScore_rowPoint q row (j%9) hr (Nat.mod_lt _ (by decide))
    _ = fourPrimeRowFactor q row * ∑ a ∈ T, fourPrimeLineScore (q 0) (fourPrimeRowOtherGood row) a := by
      rw [mul_sum]
      rw [show T = S.image (·%9) from rfl,sum_image hInj]
    _ ≤ _ := Nat.mul_le_mul_left _ (sum_fourPrimeLineScore_le_capacity (q 0) hP _
      (mask >>> (9*row)) hSub (hFree row hr) hB)

end GRHArticle.ProgressionFree
