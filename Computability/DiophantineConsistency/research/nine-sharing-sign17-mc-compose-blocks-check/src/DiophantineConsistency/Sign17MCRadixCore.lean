import DiophantineConsistency.Sign17ExactDegree
import Mathlib.Algebra.Ring.GeomSum

/-! SOURCE-ONLY: narrow digit lemmas adapted from LowMaskCoding/Section4. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MCRadixCore
open Finset LowMaskCoding
open scoped BigOperators

def maskDigit (B b : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=
  if j ∈ S then B-b else B-1

def maskList (B b len : ℕ) (S : Finset ℕ) : List ℕ :=
  (List.range len).map (maskDigit B b S)

theorem ofDigits_map_range (b : ℕ) (f : ℕ → ℕ) :
    ∀ n : ℕ, Nat.ofDigits b ((List.range n).map f) = ∑ j ∈ range n, f j * b ^ j
  | 0 => by simp [Nat.ofDigits]
  | n + 1 => by
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ofDigits_map_range b f n,
      Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.length_map, List.length_range,
      Nat.ofDigits_singleton]
    ring

private theorem sum_range_support {S : Finset ℕ} {len : ℕ}
    (hS : S ⊆ range len) (f : ℕ → ℕ) :
    (∑ j ∈ range len, if j ∈ S then f j else 0) = ∑ j ∈ S, f j := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_of_subset hS]

theorem ofDigits_maskList_add {B b len : ℕ} {S : Finset ℕ}
    (hb : 1 ≤ b) (hbB : b ≤ B) (hS : S ⊆ range len) :
    Nat.ofDigits B (maskList B b len S) + (b-1) * supportValue B S + 1 = B ^ len := by
  have hB : 1 ≤ B := hb.trans hbB
  have hgeom := geom_sum_mul_add (B-1) len
  rw [Nat.sub_add_cancel hB] at hgeom
  have hsum : Nat.ofDigits B (maskList B b len S) + (b-1) * supportValue B S =
      (∑ j ∈ range len, B ^ j) * (B-1) := by
    unfold maskList supportValue
    rw [ofDigits_map_range, ← sum_range_support hS (fun j => B ^ j),
      Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ S
    · simp only [maskDigit, if_pos hj]
      have he : B-b+(b-1) = B-1 := by omega
      calc
        (B-b) * B ^ j + (b-1) * B ^ j = (B-b+(b-1)) * B ^ j := by ring
        _ = B ^ j * (B-1) := by rw [he]; ring
    · simp only [maskDigit, if_neg hj, mul_zero, add_zero]
      ring
  omega

theorem ofDigits_maskList {B b len : ℕ} {S : Finset ℕ}
    (hb : 1 ≤ b) (hbB : b ≤ B) (hS : S ⊆ range len) :
    Nat.ofDigits B (maskList B b len S) = mask B b len S := by
  have h := ofDigits_maskList_add hb hbB hS
  unfold mask
  omega

end DiophantineConsistency.Sign17MCRadixCore
#print axioms DiophantineConsistency.Sign17MCRadixCore.ofDigits_map_range
#print axioms DiophantineConsistency.Sign17MCRadixCore.ofDigits_maskList
