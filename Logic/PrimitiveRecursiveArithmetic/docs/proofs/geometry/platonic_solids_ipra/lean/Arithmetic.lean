import Mathlib

/-!
# Arithmetic kernel of the five-solid classification

Target toolchain: Lean 4.32.0, Mathlib v4.32.0 (the pinned ProveIt toolchain).
This file is SOURCE-REVIEWED BUT UNCOMPILED: no Lean executable was available
in the production environment. It contains no `sorry`, `admit`, or new axioms.

This is a theorem in Lean's ambient arithmetic. It is NOT, by itself, a
deeply embedded derivation in iPRA. The accompanying roadmap describes the
separate `Prf PRAAx` construction. Geometry and Euler's formula are deliberately
not disguised as axioms of this file: the hypotheses below are its exact scope.
-/

namespace PlatonicIPRA

/-- The five possible ordered face/valence pairs. -/
def Allowed (p q : ℤ) : Prop :=
  (p = 3 ∧ q = 3) ∨
  (p = 4 ∧ q = 3) ∨
  (p = 3 ∧ q = 4) ∨
  (p = 5 ∧ q = 3) ∨
  (p = 3 ∧ q = 5)

/-- The only nonlinear inequality needed for classification. All branching
below is on decidable integer comparisons, not arbitrary propositions. -/
theorem allowed_of_inequality (p q : ℤ)
    (hp : 3 ≤ p) (hq : 3 ≤ q) (h : p * q < 2 * p + 2 * q) :
    Allowed p q := by
  have hp5 : p ≤ 5 := by
    by_cases hb : p ≤ 5
    · exact hb
    · have hp6 : 6 ≤ p := by omega
      have hn : 0 ≤ (p - 6) * (q - 3) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
  have hq5 : q ≤ 5 := by
    by_cases hb : q ≤ 5
    · exact hb
    · have hq6 : 6 ≤ q := by omega
      have hn : 0 ≤ (q - 6) * (p - 3) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
  unfold Allowed
  interval_cases p <;> interval_cases q <;> norm_num at *

/-- Incidence double-counting and the Euler identity imply the five cases. -/
theorem arithmetic_classification (p q V E F : ℤ)
    (hp : 3 ≤ p) (hq : 3 ≤ q) (hE : 0 < E)
    (hface : p * F = 2 * E) (hvertex : q * V = 2 * E)
    (heuler : V + F = E + 2) : Allowed p q := by
  have hf := congrArg (fun x : ℤ => q * x) hface
  have hv := congrArg (fun x : ℤ => p * x) hvertex
  have he := congrArg (fun x : ℤ => p * q * x) heuler
  have hidentity : E * (2 * p + 2 * q - p * q) = 2 * p * q := by
    nlinarith only [hf, hv, he]
  have hpositive : 0 < 2 * p * q :=
    mul_pos (by omega) (by omega)
  have hdelta : 0 < 2 * p + 2 * q - p * q := by
    by_cases hd : 0 < 2 * p + 2 * q - p * q
    · exact hd
    · have hz : E * (2 * p + 2 * q - p * q) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hE) (by omega)
      omega
  exact allowed_of_inequality p q hp hq (by omega)

/-- Full numerical table. The order of counts is V, E, F. -/
def TableEntry (p q V E F : ℤ) : Prop :=
  (p = 3 ∧ q = 3 ∧ V = 4 ∧ E = 6 ∧ F = 4) ∨
  (p = 4 ∧ q = 3 ∧ V = 8 ∧ E = 12 ∧ F = 6) ∨
  (p = 3 ∧ q = 4 ∧ V = 6 ∧ E = 12 ∧ F = 8) ∨
  (p = 5 ∧ q = 3 ∧ V = 20 ∧ E = 30 ∧ F = 12) ∨
  (p = 3 ∧ q = 5 ∧ V = 12 ∧ E = 30 ∧ F = 20)

theorem counts_classification (p q V E F : ℤ)
    (hp : 3 ≤ p) (hq : 3 ≤ q) (hE : 0 < E)
    (hface : p * F = 2 * E) (hvertex : q * V = 2 * E)
    (heuler : V + F = E + 2) : TableEntry p q V E F := by
  have ha := arithmetic_classification p q V E F hp hq hE hface hvertex heuler
  rcases ha with h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    unfold TableEntry <;> omega

/-- A finite list, avoiding any implicit quotient by geometric similarity. -/
def candidatePairs : List (ℕ × ℕ) :=
  [(3, 3), (4, 3), (3, 4), (5, 3), (3, 5)]

theorem candidatePairs_length : candidatePairs.length = 5 := rfl
theorem candidatePairs_nodup : candidatePairs.Nodup := by decide

#print axioms arithmetic_classification
#print axioms counts_classification
#print axioms candidatePairs_nodup

end PlatonicIPRA
