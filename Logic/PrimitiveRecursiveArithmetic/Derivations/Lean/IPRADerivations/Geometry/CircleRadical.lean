import IPRADerivations.Geometry.TriangleCentres

/-!
# Tangents from a point, radical axes and the concyclicity determinant

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/circles.tex`, Theorems
`circ:external-tangents`, `circ:radical` and `circ:cyclic-determinant`. Points have two integer-term coordinates,
with `dot`, `det`, `nsq` of `Geometry/TriangleCentres`. As iPRA derivations:

* `tangent_dot`, `tangent_on_circle`, `tangent_length`: (C7) for `p = P − O`, `s = |p|²` and a term `ζ` with
  `ζ² = ρ (s − ρ)` (the square root `√(ρ (s − ρ))`), the point `s u = ρ p + ζ J p` satisfies "`p · u = ρ`"
  (tangency), `|s u|² = s² ρ` (it is on the circle) and `|s p − s u|² = s² (s − ρ)`: "The tangent segments have
  equal length `√(s − ρ)`";
* `radical_axis`: (C8) "`(|x|² − ρ₁) − (|x − d|² − ρ₂) = 2 x · d − |d|² − ρ₁ + ρ₂`";
* `radical_centre_2`, `radical_centre_3`: "Cramer's formula supplies their unique solution": for the two linear
  equations `2 x · d₂ = k₂`, `2 x · d₃ = k₃`, the point `x' = k₂ J'd₃ − k₃ J'd₂` (the solution times
  `2 [d₂, d₃]`) has `x' · d₂ = k₂ [d₂, d₃]` and `x' · d₃ = k₃ [d₂, d₃]`;
* `concyclic_powers`, `concyclic_test`: (C11) the determinant with rows `(|P|², P_x, P_y, 1)`, expanded along its
  first column (`cyc`), is unchanged when `|P|²` is replaced by the power `|P − O|² − ρ` ("Replace the first
  column by the first column minus `2 O_x` times the second, minus `2 O_y` times the third, plus `(|O|² − ρ)`
  times the fourth"), and for `A, B, C` on the circle it equals "`−(|D − O|² − ρ) [B − A, C − A]`".

Not derived: the exhaustion "two and only two points of tangency", and the cancellation of `[B − A, C − A]` in
the concyclicity test.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.CircleRadical

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The doubled signed area `[Q − P, R − P]`, the minor of the rows `(P, 1)`, `(Q, 1)`, `(R, 1)`. -/
def area (p₁ p₂ q₁ q₂ r₁ r₂ : ZT n) : ZT n := det (q₁ - p₁) (q₂ - p₂) (r₁ - p₁) (r₂ - p₂)

/-- The concyclicity determinant, expanded along the column of the entries `e_P` (`|P|²` in (C11)). -/
def cyc (eA eB eC eD a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ZT n) : ZT n :=
  eA * area b₁ b₂ c₁ c₂ d₁ d₂ - eB * area a₁ a₂ c₁ c₂ d₁ d₂ + eC * area a₁ a₂ b₁ b₂ d₁ d₂ -
    eD * area a₁ a₂ b₁ b₂ c₁ c₂

local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [cyc, area, dot, det, nsq, zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg,
    ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)

local macro "geo" : tactic => `(tactic| (apply ZT.derive; gsimp; ring))

/-! ## The tangents from an exterior point -/

/-- Tangency: `p · (ρ p + ζ J p) = ρ |p|²`. -/
theorem tangent_dot (p₁ p₂ ρ ζ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot p₁ p₂ (ρ * p₁ - ζ * p₂) (ρ * p₂ + ζ * p₁)) (ρ * nsq p₁ p₂) := by
  geo

/-- The point of tangency is on the circle: `|ρ p + ζ J p|² = s² ρ` when `ζ² = ρ (s − ρ)`. -/
theorem tangent_on_circle {p₁ p₂ ρ ζ : ZT n}
    (hζ : Γ ⊢[PRAAx] ZT.eq (ζ * ζ) (ρ * (nsq p₁ p₂ - ρ))) :
    Γ ⊢[PRAAx] ZT.eq (nsq (ρ * p₁ - ζ * p₂) (ρ * p₂ + ζ * p₁)) (nsq p₁ p₂ * nsq p₁ p₂ * ρ) := by
  have e := ZT.toZ_eq hζ
  apply ZT.derive
  gsimp at e ⊢
  linear_combination (ZT.toZ Γ p₁ * ZT.toZ Γ p₁ + ZT.toZ Γ p₂ * ZT.toZ Γ p₂) * e

/-- The tangent length: `|s p − (ρ p + ζ J p)|² = s² (s − ρ)` when `ζ² = ρ (s − ρ)`. -/
theorem tangent_length {p₁ p₂ ρ ζ : ZT n}
    (hζ : Γ ⊢[PRAAx] ZT.eq (ζ * ζ) (ρ * (nsq p₁ p₂ - ρ))) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq (nsq p₁ p₂ * p₁ - (ρ * p₁ - ζ * p₂)) (nsq p₁ p₂ * p₂ - (ρ * p₂ + ζ * p₁)))
      (nsq p₁ p₂ * nsq p₁ p₂ * (nsq p₁ p₂ - ρ)) := by
  have e := ZT.toZ_eq hζ
  apply ZT.derive
  gsimp at e ⊢
  linear_combination (ZT.toZ Γ p₁ * ZT.toZ Γ p₁ + ZT.toZ Γ p₂ * ZT.toZ Γ p₂) * e

/-! ## Radical axes -/

/-- The difference of the powers of `x` with respect to two circles. -/
theorem radical_axis (x₁ x₂ d₁ d₂ ρ₁ ρ₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((nsq x₁ x₂ - ρ₁) - (nsq (x₁ - d₁) (x₂ - d₂) - ρ₂))
      (ZT.natLit 2 * dot x₁ x₂ d₁ d₂ - nsq d₁ d₂ - ρ₁ + ρ₂) := by
  geo

/-- The radical centre satisfies the first equation: `x' · d₂ = k₂ [d₂, d₃]`. -/
theorem radical_centre_2 (d₂₁ d₂₂ d₃₁ d₃₂ k₂ k₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot (k₂ * d₃₂ - k₃ * d₂₂) (k₃ * d₂₁ - k₂ * d₃₁) d₂₁ d₂₂)
      (k₂ * det d₂₁ d₂₂ d₃₁ d₃₂) := by
  geo

/-- The radical centre satisfies the second equation: `x' · d₃ = k₃ [d₂, d₃]`. -/
theorem radical_centre_3 (d₂₁ d₂₂ d₃₁ d₃₂ k₂ k₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot (k₂ * d₃₂ - k₃ * d₂₂) (k₃ * d₂₁ - k₂ * d₃₁) d₃₁ d₃₂)
      (k₃ * det d₂₁ d₂₂ d₃₁ d₃₂) := by
  geo

/-! ## The concyclicity determinant -/

/-- The determinant (C11) is unchanged when `|P|²` is replaced by the power `|P − O|² − ρ`. -/
theorem concyclic_powers (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ o₁ o₂ ρ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (cyc (nsq a₁ a₂) (nsq b₁ b₂) (nsq c₁ c₂) (nsq d₁ d₂) a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂)
      (cyc (nsq (a₁ - o₁) (a₂ - o₂) - ρ) (nsq (b₁ - o₁) (b₂ - o₂) - ρ) (nsq (c₁ - o₁) (c₂ - o₂) - ρ)
        (nsq (d₁ - o₁) (d₂ - o₂) - ρ) a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂) := by
  geo

/-- For `A, B, C` on the circle `(O, ρ)`, the determinant (C11) is `−(|D − O|² − ρ) [B − A, C − A]`. -/
theorem concyclic_test {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ o₁ o₂ ρ : ZT n}
    (hA : Γ ⊢[PRAAx] ZT.eq (nsq (a₁ - o₁) (a₂ - o₂)) ρ) (hB : Γ ⊢[PRAAx] ZT.eq (nsq (b₁ - o₁) (b₂ - o₂)) ρ)
    (hC : Γ ⊢[PRAAx] ZT.eq (nsq (c₁ - o₁) (c₂ - o₂)) ρ) :
    Γ ⊢[PRAAx] ZT.eq
      (cyc (nsq a₁ a₂) (nsq b₁ b₂) (nsq c₁ c₂) (nsq d₁ d₂) a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂)
      (-((nsq (d₁ - o₁) (d₂ - o₂) - ρ) * area a₁ a₂ b₁ b₂ c₁ c₂)) := by
  have eA := ZT.toZ_eq hA
  have eB := ZT.toZ_eq hB
  have eC := ZT.toZ_eq hC
  have eP := ZT.toZ_eq (concyclic_powers (Γ := Γ) a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ o₁ o₂ ρ)
  apply ZT.derive
  gsimp at eA eB eC eP ⊢
  linear_combination eP +
    ((ZT.toZ Γ c₁ - ZT.toZ Γ b₁) * (ZT.toZ Γ d₂ - ZT.toZ Γ b₂) -
        (ZT.toZ Γ c₂ - ZT.toZ Γ b₂) * (ZT.toZ Γ d₁ - ZT.toZ Γ b₁)) * eA -
      ((ZT.toZ Γ c₁ - ZT.toZ Γ a₁) * (ZT.toZ Γ d₂ - ZT.toZ Γ a₂) -
        (ZT.toZ Γ c₂ - ZT.toZ Γ a₂) * (ZT.toZ Γ d₁ - ZT.toZ Γ a₁)) * eB +
      ((ZT.toZ Γ b₁ - ZT.toZ Γ a₁) * (ZT.toZ Γ d₂ - ZT.toZ Γ a₂) -
        (ZT.toZ Γ b₂ - ZT.toZ Γ a₂) * (ZT.toZ Γ d₁ - ZT.toZ Γ a₁)) * eC

end LeanProofs.IPRA.Geometry.CircleRadical
