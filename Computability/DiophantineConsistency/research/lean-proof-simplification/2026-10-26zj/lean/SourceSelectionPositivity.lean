import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic

/-!
This file checks the positivity kernel and the shape of the proposed adapter.
It does not import or rebuild DiophantineConsistency. The actual production
adapters, in source-selection-api-migration.patch and the alternative
source-selection-positivity.patch, still need the pinned project.
-/
namespace SourceSelectionPositivity
open scoped BigOperators

/-- The same finite weighted sum used by NativeCyclicConvolution.word. -/
def cyclicWord {n : ℕ} [NeZero n] (ρ : ℕ) (c : ZMod n → ℕ) : ℕ :=
  ∑ i : ZMod n, c i * ρ ^ i.val

/-- A known selected coordinate suffices; its index need not be nonzero. -/
theorem positive_of_selected {n : ℕ} [NeZero n] {ρ : ℕ} (hρ : 0 < ρ)
    (c : ZMod n → ℕ) (i : ZMod n) (hi : c i = 1) : 0 < cyclicWord ρ c := by
  have hp : 0 < c i * ρ ^ i.val := by
    rw [hi, one_mul]
    exact pow_pos hρ _
  exact hp.trans_le (Finset.single_le_sum
    (fun j _ => Nat.zero_le (c j * ρ ^ j.val)) (Finset.mem_univ i))

/-- The existing production positivity API, generalized only in the radix. -/
theorem positive_of_digit {n : ℕ} [NeZero n] {ρ : ℕ} (hρ : 0 < ρ)
    (c : ZMod n → ℕ) (i : ZMod n) (hi : 0 < c i) : 0 < cyclicWord ρ c := by
  have hp : 0 < c i * ρ ^ i.val := Nat.mul_pos hi (pow_pos hρ _)
  exact hp.trans_le (Finset.single_le_sum
    (fun j _ => Nat.zero_le (c j * ρ ^ j.val)) (Finset.mem_univ i))

def Selected {ι : Type*} (f : ι → ℕ) (i : ι) : Prop :=
  f i = 1 ∧ ∀ j, j ≠ i → f j = 0

def selectorValue {N : ℕ} (position : Fin 942 → ℕ)
    (c : ZMod (N*2011) → ℕ) (b : ZMod (N*2011)) (i : Fin 942) : ℕ :=
  c (b + (position i : ZMod (N*2011)))

/-- Exact two-line body proposed for the existing production theorem. -/
theorem assembled_positive_rewrite {N : ℕ} [NeZero N]
    (assemble : (ZMod N → Fin 942) → (ZMod N → ℕ) → (ZMod N → ℕ) →
      ZMod (N*2011) → ℕ)
    (base : ZMod N → ZMod (N*2011)) (position : Fin 942 → ℕ)
    (hselect : ∀ a dummy marker j,
      Selected (selectorValue position (assemble a dummy marker) (base j)) (a j))
    (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) :
    0 < cyclicWord (2^47) (assemble a dummy marker) := by
  apply positive_of_digit (by decide) _ _
  exact (hselect a dummy marker 0).1.symm ▸ Nat.zero_lt_one

/-- Source-shaped adapter. The only assembly input is the existing selected
coordinate equation; the dummy and marker maps have no bound assumptions. -/
theorem assembled_positive {N : ℕ} [NeZero N]
    (assemble : (ZMod N → Fin 942) → (ZMod N → ℕ) → (ZMod N → ℕ) →
      ZMod (N*2011) → ℕ)
    (base : ZMod N → ZMod (N*2011)) (position : Fin 942 → ℕ)
    (hselect : ∀ a dummy marker j,
      assemble a dummy marker (base j + (position (a j) : ZMod (N*2011))) = 1)
    (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) :
    0 < cyclicWord (2^47) (assemble a dummy marker) := by
  exact positive_of_selected (by decide) _ _ (hselect a dummy marker 0)

/-- Modulus 2011 is the N=1 cell. Arbitrary numeric control digits, even
larger than the radix, do not affect positivity at the selected slot. -/
example (d m : ℕ) :
    0 < cyclicWord (2^47) (fun i : ZMod 2011 =>
      if i = 941 then 1 else if i = 977 then d else if i = 1004 then m else 0) := by
  apply positive_of_selected (by decide) _ (941 : ZMod 2011)
  simp

/-- A selected origin is also valid: no nonzero-position premise is used. -/
example (d m : ℕ) :
    0 < cyclicWord (2^47) (fun i : ZMod 2011 =>
      if i = 0 then 1 else if i = 977 then d else if i = 1004 then m else 0) := by
  apply positive_of_selected (by decide) _ (0 : ZMod 2011)
  simp

#print axioms positive_of_selected
#print axioms assembled_positive
#print axioms assembled_positive_rewrite
end SourceSelectionPositivity
