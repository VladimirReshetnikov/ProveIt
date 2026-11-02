import DiophantineConsistency.ArithmeticMaskConstants
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
noncomputable section
namespace CompactListMask
open Finset
open scoped BigOperators

def digit (B special : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=
  if j=special then B-4 else if j∈S then B-2 else B-1

def defect (special : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=
  if j=special then 3 else if j∈S then 1 else 0

def digits (B len special : ℕ) (S : Finset ℕ) : List ℕ :=
  (List.range len).map (digit B special S)

theorem ofDigits_map_range (B : ℕ) (f : ℕ → ℕ) :
    ∀ n : ℕ, Nat.ofDigits B ((List.range n).map f) = ∑ j ∈ range n, f j * B^j
  | 0 => by simp
  | n+1 => by
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ofDigits_map_range B f n,
      Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.length_map, List.length_range,
      Nat.ofDigits_singleton]
    ring

/-- Exact finite symbolic recipe, with no expansion of the large numeral. -/
theorem digits_add_defect (B len special : ℕ) (S : Finset ℕ) (hB : 4 ≤ B) :
    Nat.ofDigits B (digits B len special S) +
      (∑ j ∈ range len, defect special S j * B^j) + 1 = B^len := by
  have hgeom := geom_sum_mul_add (B-1) len
  rw [Nat.sub_add_cancel (by omega : 1 ≤ B)] at hgeom
  have hsum : Nat.ofDigits B (digits B len special S) +
      (∑ j ∈ range len, defect special S j * B^j) =
      (∑ j ∈ range len, B^j) * (B-1) := by
    unfold digits
    rw [ofDigits_map_range, ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hs : j = special
    · simp only [digit, defect, if_pos hs]
      have he : B-4+3=B-1 := by omega
      calc
        (B-4)*B^j+3*B^j = (B-4+3)*B^j := by ring
        _ = B^j*(B-1) := by rw [he]; ring
    · by_cases hS : j ∈ S
      · simp only [digit, defect, if_neg hs, if_pos hS, one_mul]
        have he : B-2+1=B-1 := by omega
        calc
          (B-2)*B^j+B^j = (B-2+1)*B^j := by ring
          _ = B^j*(B-1) := by rw [he]; ring
      · simp only [digit, defect, if_neg hs, if_neg hS, zero_mul, add_zero]
        ring
  omega
end CompactListMask
#print axioms CompactListMask.digits_add_defect
