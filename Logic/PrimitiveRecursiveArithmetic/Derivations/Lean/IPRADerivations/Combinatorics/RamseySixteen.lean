import IPRADerivations.Core.OrderCertificates

/-!
# `R(3,3,3) > 16` in iPRA: the Greenwood–Gleason colouring

Packet: `combinatorics/ramsey_ipra`, `ramsey.tex`, "Three colors": "Symmetric difference gives an abelian
group on the resulting 16 classes … Its fifteen nonzero elements fall into three sets of five … Color `{x, y}`
by the set containing the nonzero sum `x + y`. No one of the three sets contains two distinct elements and
their sum … This proves the Greenwood–Gleason value `R(3,3,3) = 17` using only five-bit arithmetic for the
lower bound."

The sixteen vertices are the numbers `0, …, 15` with bitwise exclusive or as the group law, and the three
sum-free classes are the cosets of the cubes in `GF(16)^*` (`cls`):
`{1, 8, 10, 12, 15}`, `{2, 3, 7, 11, 13}`, `{4, 5, 6, 9, 14}`.

* `ind k x y`: the indicator that the edge `{x, y}` has colour `k`;
* `gg_partition`: every edge has exactly one colour, `ind 0 + ind 1 + ind 2 ≐ 1`;
* `greenwood_gleason`: for every triangle `a < b < c` the monochromatic indicator
  `∑_k ind k a b · ind k a c · ind k b c` is `≐ 0`.

The upper bound `R(3,3,3) ≤ 17` is not assembled; its pivot count is `RamseyBounds.three_color_pivot` and its
two-colour step is `RamseyTriangle.ramsey33`.
-/

namespace LeanProofs.IPRA.Combinatorics.RamseySixteen

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The class of a nonzero element of the group (`3` for zero). -/
def cls : ℕ → ℕ
  | 1 => 0 | 8 => 0 | 10 => 0 | 12 => 0 | 15 => 0
  | 2 => 1 | 3 => 1 | 7 => 1 | 11 => 1 | 13 => 1
  | 4 => 2 | 5 => 2 | 6 => 2 | 9 => 2 | 14 => 2
  | _ => 3

/-- The indicator that the edge `{x, y}` has colour `k`. -/
def ind (k : ℕ) (x y : Fin 16) : ℕ := if cls (x.val ^^^ y.val) = k then 1 else 0

set_option maxRecDepth 100000 in
theorem one_colour : ∀ a b : Fin 16, a < b → ind 0 a b + ind 1 a b + ind 2 a b = 1 := by decide

set_option maxRecDepth 100000 in
theorem no_triangle : ∀ a b c : Fin 16, a < b → b < c →
    ind 0 a b * ind 0 a c * ind 0 b c + ind 1 a b * ind 1 a c * ind 1 b c +
      ind 2 a b * ind 2 a c * ind 2 b c = 0 := by decide

/-- Every edge has exactly one of the three colours. -/
theorem gg_partition (a b : Fin 16) (hab : a < b) :
    Γ ⊢[PRAAx] num (ind 0 a b) + num (ind 1 a b) + num (ind 2 a b) ≐ (succ zero : PTm n) := by
  apply deriveNat
  ipra_simps
  have h := congrArg (Nat.cast : ℕ → Groth (Q Γ)) (one_colour a b hab)
  push_cast at h
  linear_combination h

/-- The Greenwood–Gleason colouring of `K_16` has no monochromatic triangle. -/
theorem greenwood_gleason (a b c : Fin 16) (hab : a < b) (hbc : b < c) :
    Γ ⊢[PRAAx] num (ind 0 a b) * num (ind 0 a c) * num (ind 0 b c) +
        num (ind 1 a b) * num (ind 1 a c) * num (ind 1 b c) +
        num (ind 2 a b) * num (ind 2 a c) * num (ind 2 b c) ≐ (zero : PTm n) := by
  apply deriveNat
  ipra_simps
  have h := congrArg (Nat.cast : ℕ → Groth (Q Γ)) (no_triangle a b c hab hbc)
  push_cast at h
  exact h

end LeanProofs.IPRA.Combinatorics.RamseySixteen
