import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith

/-!
# Cancelling the scaled strong norm in the short consistency candidate

This file checks a local transformation of the reports' P67/P68 equations.
It does not assume or prove their native-window compiler correctness.
The coefficient replacement uses the fact that the strong Pell norm is a
unit at a zero, and that its discriminant excludes the negative unit.
-/

namespace DiophantineConsistency.ShortEquation

/-- A discriminant one below a square excludes a Pell norm of -1 modulo 4. -/
theorem strong_ne_neg_one (a f t : ℤ) :
    f ^ 2 - ((a + 2) ^ 2 - 1) * t ^ 2 ≠ -1 := by
  intro h
  have hm := congrArg (fun z : ℤ => (z : ZMod 4)) h
  push_cast at hm
  have bad : ∀ a f t : ZMod 4,
      f ^ 2 - ((a + 2) ^ 2 - 1) * t ^ 2 ≠ -1 := by decide
  exact bad _ _ _ hm

/-- The final product, with its auxiliary coefficient supplied separately. -/
def product (m coefficient gap y strong : ℤ) : ℤ :=
  m * (coefficient * gap + y ^ 2) * strong - 1

/-- At a zero, the strong factor is an integer unit; its sign is already fixed. -/
theorem strong_eq_one {m coefficient gap y strong : ℤ}
    (hnegative : strong ≠ -1) (h : product m coefficient gap y strong = 0) :
    strong = 1 := by
  have hmul : (m * (coefficient * gap + y ^ 2)) * strong = 1 := by
    unfold product at h
    linarith
  have hu : IsUnit strong := IsUnit.of_mul_eq_one_right _ hmul
  rcases Int.isUnit_iff.mp hu with hpos | hneg
  · exact hpos
  · exact (hnegative hneg).elim

/-- The auxiliary coefficient may be reduced before cancelling the discriminant. -/
theorem replace_coefficient {m δ f t gap y : ℤ}
    (hnegative : f ^ 2 - δ * t ^ 2 ≠ -1) :
    product m (δ ^ 2 * t ^ 2) gap y (f ^ 2 - δ * t ^ 2) = 0 ↔
      product m (δ * (f ^ 2 - 1)) gap y (f ^ 2 - δ * t ^ 2) = 0 := by
  have equal_coefficients (hn : f ^ 2 - δ * t ^ 2 = 1) :
      δ ^ 2 * t ^ 2 = δ * (f ^ 2 - 1) := by
    calc
      δ ^ 2 * t ^ 2 = δ * (δ * t ^ 2) := by ring
      _ = δ * (f ^ 2 - 1) := by congr 1; linarith
  constructor <;> intro h
  · rwa [← equal_coefficients (strong_eq_one hnegative h)]
  · rwa [equal_coefficients (strong_eq_one hnegative h)]

/-- The scaled product differs from the unscaled product by exactly δ. -/
theorem scaled_identity (m δ f t gap y : ℤ) :
    m * (δ ^ 2 * t ^ 2 * gap + y ^ 2) * (δ * f ^ 2 - δ ^ 2 * t ^ 2) - δ =
      δ * product m (δ ^ 2 * t ^ 2) gap y (f ^ 2 - δ * t ^ 2) := by
  unfold product
  ring

/-- A fully checked local equivalence used by the degree-111 candidate.
The variables m, gap and y may be arbitrary integers. -/
theorem scaled_zero_iff_reduced {m a f t gap y : ℤ}
    (hδ : (a + 2) ^ 2 - 1 ≠ 0) :
    let δ := (a + 2) ^ 2 - 1
    m * (δ ^ 2 * t ^ 2 * gap + y ^ 2) * (δ * f ^ 2 - δ ^ 2 * t ^ 2) - δ = 0 ↔
      product m (δ * (f ^ 2 - 1)) gap y (f ^ 2 - δ * t ^ 2) = 0 := by
  dsimp only
  rw [scaled_identity, mul_eq_zero]
  simp only [hδ, false_or]
  exact replace_coefficient (strong_ne_neg_one a f t)

end DiophantineConsistency.ShortEquation
