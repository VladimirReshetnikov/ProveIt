import IPRADerivations.Core.OrderCertificates

/-!
# `R(3,3) > 5` in iPRA: the pentagon colouring

Packet: `combinatorics/ramsey_ipra`, `ramsey.tex`, Section "Graph bounds and two exact thresholds": "On five
cyclically ordered vertices color the sides red and the diagonals blue. Each color forms a cycle of length
five, so neither has a triangle. Consequently `R(3,3) = 6`."

The colouring is given by numerals: `pX i j = 1` on the sides `{i, i+1}` and `{0, 4}` (for `i < j`), and
`pY = 1 − pX`.

* `pent_idem`, `pent_compl`: it is a colouring in the sense of `Combinatorics/RamseyTriangle` (`x² ≐ x`,
  `x + y ≐ 1`);
* `pentagon`: for every triangle `a < b < c` the monochromatic indicator
  `x_ab x_ac x_bc + y_ab y_ac y_bc` is `≐ 0`.

With `RamseyTriangle.ramsey33` (some indicator is positive on six vertices) this is the exact threshold
`R(3,3) = 6` for colourings given by indicator terms.
-/

namespace LeanProofs.IPRA.Combinatorics.RamseyPentagon

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The red indicator of the pentagon colouring (for `i < j`): the sides. -/
def pX (i j : Fin 5) : ℕ := if j.val = i.val + 1 ∨ (i.val = 0 ∧ j.val = 4) then 1 else 0

/-- The blue indicator: the diagonals. -/
def pY (i j : Fin 5) : ℕ := 1 - pX i j

theorem pX_idem : ∀ i j : Fin 5, pX i j * pX i j = pX i j := by decide

theorem pX_compl : ∀ i j : Fin 5, pX i j + pY i j = 1 := by decide

theorem no_triangle : ∀ a b c : Fin 5, a < b → b < c →
    pX a b * pX a c * pX b c + pY a b * pY a c * pY b c = 0 := by decide

/-- `x² ≐ x` for the pentagon colouring. -/
theorem pent_idem (i j : Fin 5) : Γ ⊢[PRAAx] num (pX i j) * num (pX i j) ≐ (num (pX i j) : PTm n) := by
  apply deriveNat
  ipra_simps
  have h := congrArg (Nat.cast : ℕ → Groth (Q Γ)) (pX_idem i j)
  push_cast at h
  exact h

/-- `x + y ≐ 1` for the pentagon colouring. -/
theorem pent_compl (i j : Fin 5) : Γ ⊢[PRAAx] num (pX i j) + num (pY i j) ≐ (succ zero : PTm n) := by
  apply deriveNat
  ipra_simps
  have h := congrArg (Nat.cast : ℕ → Groth (Q Γ)) (pX_compl i j)
  push_cast at h
  linear_combination h

/-- The pentagon colouring has no monochromatic triangle: every indicator vanishes. -/
theorem pentagon (a b c : Fin 5) (hab : a < b) (hbc : b < c) :
    Γ ⊢[PRAAx] num (pX a b) * num (pX a c) * num (pX b c) + num (pY a b) * num (pY a c) * num (pY b c) ≐
      (zero : PTm n) := by
  apply deriveNat
  ipra_simps
  have h := congrArg (Nat.cast : ℕ → Groth (Q Γ)) (no_triangle a b c hab hbc)
  push_cast at h
  exact h

end LeanProofs.IPRA.Combinatorics.RamseyPentagon
