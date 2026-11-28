import GRHArticle.ProgressionFree.FourPrimeMaskCapacityUpdate

/-!
# The executable masked check for each four-prime box

The first exponent is the low mixed-radix digit. Completing a three-term
progression in exponent coordinates therefore gives the candidate to clear
directly, without searching for its integer value.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private def vectorBoxCompletion (x y : ℕ) : Option ℕ :=
  let a := fourPrimeDecode x
  let b := fourPrimeDecode y
  let c := fun i ↦ 2*b i-a i
  if x ≠ y ∧ ∀ i, a i ≤ 2*b i ∧ c i ≤ fourPrimeLowBoxLimit i then
    some (fourPrimeEncode c)
  else none

/-- The allowable completion of two different exponents in the low box.
The executable test reads its four mixed-radix digits directly. -/
def fourPrimeBoxCompletion (x y : ℕ) : Option ℕ :=
  let a₀ := x%9
  let a₁ := x/9%9
  let a₂ := x/81%3
  let a₃ := x/243
  let b₀ := y%9
  let b₁ := y/9%9
  let b₂ := y/81%3
  let b₃ := y/243
  let c₀ := 2*b₀-a₀
  let c₁ := 2*b₁-a₁
  let c₂ := 2*b₂-a₂
  let c₃ := 2*b₃-a₃
  if x ≠ y ∧ (a₀ ≤ 2*b₀ ∧ c₀ ≤ 8) ∧ (a₁ ≤ 2*b₁ ∧ c₁ ≤ 8) ∧
      (a₂ ≤ 2*b₂ ∧ c₂ ≤ 2) ∧ (a₃ ≤ 2*b₃ ∧ c₃ ≤ 2) then
    some (c₀+9*(c₁+9*(c₂+3*c₃)))
  else none

private theorem fourPrimeBoxCompletion_eq_vector (x y : ℕ) :
    fourPrimeBoxCompletion x y = vectorBoxCompletion x y := by
  let valid (i : Fin 4) :=
    (fourPrimeDecode x i ≤ 2*fourPrimeDecode y i ∧
      2*fourPrimeDecode y i-fourPrimeDecode x i ≤ fourPrimeLowBoxLimit i)
  have h : (valid 0 ∧ valid 1 ∧ valid 2 ∧ valid 3) = (∀ i, valid i) := by
    apply propext
    constructor
    · rintro ⟨h₀,h₁,h₂,h₃⟩ i
      fin_cases i
      · exact h₀
      · exact h₁
      · exact h₂
      · exact h₃
    · intro h
      exact ⟨h 0,h 1,h 2,h 3⟩
  let z := some (fourPrimeEncode (fun i ↦ 2*fourPrimeDecode y i-fourPrimeDecode x i))
  change (if x ≠ y ∧ valid 0 ∧ valid 1 ∧ valid 2 ∧ valid 3 then z else none) =
    (if x ≠ y ∧ ∀ i, valid i then z else none)
  have he : (x ≠ y ∧ valid 0 ∧ valid 1 ∧ valid 2 ∧ valid 3) ↔ (x ≠ y ∧ ∀ i, valid i) :=
    and_congr_right (fun _ ↦ Iff.of_eq h)
  by_cases hb : x ≠ y ∧ ∀ i, valid i
  · rw [if_pos (he.mpr hb),if_pos hb]
  · rw [if_neg (fun hc ↦ hb (he.mp hc)),if_neg hb]

/-- A recorded completion satisfies the coordinatewise midpoint identity. -/
theorem fourPrimeBoxCompletion_spec {x y z : ℕ}
    (h : fourPrimeBoxCompletion x y = some z) :
    x ≠ y ∧ fourPrimeDecode x + fourPrimeDecode z = fourPrimeDecode y + fourPrimeDecode y := by
  rw [fourPrimeBoxCompletion_eq_vector] at h
  dsimp only [vectorBoxCompletion] at h
  split at h
  · rename_i hc
    injection h with hz
    subst z
    refine ⟨hc.1,?_⟩
    rw [fourPrimeDecode_encode (mem_exponentBox.mpr fun i ↦ (hc.2 i).2)]
    funext i
    have hBound := (hc.2 i).1
    change fourPrimeDecode x i + (2*fourPrimeDecode y i-fourPrimeDecode x i) =
      fourPrimeDecode y i + fourPrimeDecode y i
    omega
  · contradiction

/-- Set the bits corresponding to the given candidate codes. -/
def fourPrimeCodeMask : List ℕ → ℕ
  | [] => 0
  | a::tail => (1 <<< a) ||| fourPrimeCodeMask tail

theorem testBit_fourPrimeCodeMask {L : List ℕ} {a : ℕ} (ha : a ∈ L) :
    (fourPrimeCodeMask L).testBit a = true := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    rw [fourPrimeCodeMask,Nat.testBit_lor,Nat.shiftLeft_eq,one_mul]
    rcases List.mem_cons.mp ha with rfl | h
    · simp
    · simp [ih h]

/-- Ordered candidates on a prefix of the low box. -/
def fourPrimeBoxCodes (q r : Fin 4 → ℕ) : List ℕ :=
  (fourPrimeSortedExponents q r).map fourPrimeEncode

/-- The optimized check uses a mixed-radix candidate mask and packed
weighted row capacities. -/
def fourPrimeMaskBoxCheck (q r : Fin 4 → ℕ) : Bool :=
  let L := fourPrimeBoxCodes q r
  finiteGPMaskCheck (fourPrimeMaskCapacity q) fourPrimeBoxCompletion
    (fourPrimeBoxTarget q r) L [] (fourPrimeCodeMask L)

theorem gpMaskContains_fourPrimeBoxCodes (q r : Fin 4 → ℕ) {A : Finset ℕ}
    (hA : ∀ x ∈ A, ∃ a ∈ exponentBox r, fourPrimeEncode a = x) :
    gpMaskContains A (fourPrimeCodeMask (fourPrimeBoxCodes q r)) := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := hA x hx
  apply testBit_fourPrimeCodeMask
  apply List.mem_map.mpr
  exact ⟨a,by
    change a ∈ ((fourPrimeSortedExponents q r : List (Fin 4 → ℕ)) : Multiset (Fin 4 → ℕ))
    rw [fourPrimeSortedExponents_coe]
    exact ha,rfl⟩

/-- The executable variant initializes the row capacities once, then
updates only the row of a bit when it is removed. -/
def fourPrimeCachedMaskBoxCheck (q r : Fin 4 → ℕ) : Bool :=
  let L := fourPrimeBoxCodes q r
  let mask := fourPrimeCodeMask L
  finiteGPCachedMaskCheck (fourPrimeMaskCapacityUpdate q) fourPrimeBoxCompletion
    (fourPrimeBoxTarget q r) L [] (mask,fourPrimeMaskCapacity q mask)

/-- Cached and recomputed capacities give the same finite check. -/
theorem fourPrimeCachedMaskBoxCheck_eq (q r : Fin 4 → ℕ) :
    fourPrimeCachedMaskBoxCheck q r = fourPrimeMaskBoxCheck q r :=
  finiteGPCachedMaskCheck_eq (fourPrimeMaskCapacity q) (fourPrimeMaskCapacityUpdate q)
    (fourPrimeMaskCapacityUpdate_correct q) fourPrimeBoxCompletion (fourPrimeBoxTarget q r) _ _ _

end GRHArticle.ProgressionFree
