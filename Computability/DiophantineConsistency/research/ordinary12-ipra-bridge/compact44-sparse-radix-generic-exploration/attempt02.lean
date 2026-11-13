import Mathlib.Data.Nat.Digits.Lemmas

open Finset

namespace SparseRadix

theorem ofDigits_map_range (b : ℕ) (f : ℕ → ℕ) :
    ∀ n : ℕ, Nat.ofDigits b ((List.range n).map f) = ∑ j ∈ range n, f j * b ^ j
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ofDigits_map_range b f n,
      Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.length_map, List.length_range,
      Nat.ofDigits_singleton]
    ring

theorem digit_ofDigits (b : ℕ) (L : List ℕ) (hb : 0 < b)
    (hL : ∀ x ∈ L, x < b) (i : ℕ) (hi : i < L.length) :
    (Nat.ofDigits b L / b ^ i) % b = L[i] := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i hb L hL, List.drop_eq_getElem_cons hi,
    Nat.ofDigits_cons]
  have h := hL L[i] (List.getElem_mem hi)
  simp [Nat.add_mod, Nat.mod_eq_of_lt h]

theorem digit_finite_sum (b n i : ℕ) (f : ℕ → ℕ) (hb : 0 < b)
    (hf : ∀ j < n, f j < b) (hi : i < n) :
    ((∑ j ∈ range n, f j * b ^ j) / b ^ i) % b = f i := by
  let L := (List.range n).map f
  have hL : ∀ x ∈ L, x < b := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact hf j (List.mem_range.mp hj)
  have hiL : i < L.length := by simpa [L] using hi
  have h := digit_ofDigits b L hb hL i hiL
  simpa [L, ofDigits_map_range] using h

/-- Aggregation preserves collisions; no term is overwritten. -/
def coefficientAt (terms : List (ℕ × ℕ)) (j : ℕ) : ℕ :=
  ((terms.filter (fun t => t.1 = j)).map Prod.snd).sum

theorem finite_sum_lt (b n : ℕ) (f : ℕ → ℕ) (hb : 1 < b)
    (hf : ∀ j < n, f j < b) :
    (∑ j ∈ range n, f j * b ^ j) < b ^ n := by
  let L := (List.range n).map f
  have hL : ∀ x ∈ L, x < b := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact hf j (List.mem_range.mp hj)
  have h := Nat.ofDigits_lt_base_pow_length hb hL
  simpa [L, ofDigits_map_range] using h

theorem sparse_digit (b n i : ℕ) (terms : List (ℕ × ℕ)) (hb : 0 < b)
    (hcoeff : ∀ j < n, coefficientAt terms j < b) (hi : i < n) :
    ((∑ j ∈ range n, coefficientAt terms j * b ^ j) / b ^ i) % b =
      coefficientAt terms i :=
  digit_finite_sum b n i (coefficientAt terms) hb hcoeff hi

#print axioms SparseRadix.ofDigits_map_range
#print axioms SparseRadix.digit_ofDigits
#print axioms SparseRadix.digit_finite_sum
#print axioms SparseRadix.finite_sum_lt
#print axioms SparseRadix.sparse_digit
end SparseRadix
