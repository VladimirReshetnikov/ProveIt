import IPRADerivations.Core.Tactic

/-!
# Triangle formulas (`docs/proofs/geometry/triangle_formulas_ipra`)

Derivations in `Prf PRAAx` of the algebraic core of the packet's proofs of
Heron's formula and the laws of cosines and sines:

* the two-square identity `(xz + yw)² + (xw − yz)² = (x² + y²)(z² + w²)`
  (`triangle_formulas_ipra.tex`, the product rule for complex moduli);
* the factorisation `4b²c² − (b² + c² − a²)² = (a+b+c)(−a+b+c)(a−b+c)(a+b−c)`;
* Heron's formula in coordinates: for a triangle with integer vertices
  `P₁, P₂, P₃`, doubled signed area `D` and squared side lengths `A, B, C`,
  `4D² = 2AB + 2BC + 2CA − A² − B² − C²`, i.e. `16Δ² = …` with `Δ = D/2`;
* the law of cosines in coordinates: `A = B + C − 2⟨P₂ − P₁, P₃ − P₁⟩`.

Integers are differences of natural numbers (`ZT`); each theorem is the
universal closure of an iPRA formula over natural-number variables.
-/

namespace LeanProofs.IPRA.Geometry.TriangleFormulas

open_ipra

/-! ## The two-square identity -/

section TwoSquares

/-- Integer variables `x, y, z, w` over eight natural-number variables. -/
abbrev x : ZT 8 := .var2 0 1
abbrev y : ZT 8 := .var2 2 3
abbrev z : ZT 8 := .var2 4 5
abbrev w : ZT 8 := .var2 6 7

/-- `(xz + yw)² + (xw − yz)² = (x² + y²)(z² + w²)` over the integers. -/
def twoSquaresFormula : Fm PTm 8 :=
  ZT.eq (ZT.sq (x * z + y * w) + ZT.sq (x * w - y * z)) ((ZT.sq x + ZT.sq y) * (ZT.sq z + ZT.sq w))

theorem twoSquares_open : ([] : List (Fm PTm 8)) ⊢[PRAAx] twoSquaresFormula := by
  unfold twoSquaresFormula; ipra_ring

/-- The two-square identity, as a closed theorem of iPRA. -/
theorem twoSquares : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 twoSquaresFormula :=
  closeAll 8 twoSquares_open

end TwoSquares

/-! ## The Heron factorisation in the side lengths -/

section HeronSides

abbrev a : ZT 3 := .ofNat (var 0)
abbrev b : ZT 3 := .ofNat (var 1)
abbrev c : ZT 3 := .ofNat (var 2)

/-- `4b²c² − (b² + c² − a²)² = (a+b+c)(−a+b+c)(a−b+c)(a+b−c)` for natural `a, b, c`. -/
def heronFactorFormula : Fm PTm 3 :=
  ZT.eq (ZT.natLit 4 * ZT.sq b * ZT.sq c - ZT.sq (ZT.sq b + ZT.sq c - ZT.sq a))
    ((a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c))

theorem heronFactor : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 3 heronFactorFormula :=
  closeAll 3 (by unfold heronFactorFormula; ipra_ring)

end HeronSides

/-! ## Heron's formula and the law of cosines in coordinates -/

section Coordinates

/-- Integer coordinates of `P₁ = (x₁, y₁)`, `P₂ = (x₂, y₂)`, `P₃ = (x₃, y₃)`. -/
abbrev x₁ : ZT 12 := .var2 0 1
abbrev y₁ : ZT 12 := .var2 2 3
abbrev x₂ : ZT 12 := .var2 4 5
abbrev y₂ : ZT 12 := .var2 6 7
abbrev x₃ : ZT 12 := .var2 8 9
abbrev y₃ : ZT 12 := .var2 10 11

/-- Twice the signed area. -/
def D : ZT 12 := (x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁)
/-- Squared side lengths opposite `P₁`, `P₂`, `P₃`. -/
def A : ZT 12 := ZT.sq (x₃ - x₂) + ZT.sq (y₃ - y₂)
def B : ZT 12 := ZT.sq (x₃ - x₁) + ZT.sq (y₃ - y₁)
def C : ZT 12 := ZT.sq (x₂ - x₁) + ZT.sq (y₂ - y₁)

/-- Heron: `4 D² = 2AB + 2BC + 2CA − A² − B² − C²`. -/
def heronFormula : Fm PTm 12 :=
  ZT.eq (ZT.natLit 4 * ZT.sq D)
    (ZT.natLit 2 * A * B + ZT.natLit 2 * B * C + ZT.natLit 2 * C * A
      - ZT.sq A - ZT.sq B - ZT.sq C)

theorem heron : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 heronFormula :=
  closeAll 12 (by unfold heronFormula D A B C; ipra_ring)

/-- The law of cosines: `A = B + C − 2 ⟨P₃ − P₁, P₂ − P₁⟩`. -/
def cosinesFormula : Fm PTm 12 :=
  ZT.eq A (B + C - ZT.natLit 2 * ((x₃ - x₁) * (x₂ - x₁) + (y₃ - y₁) * (y₂ - y₁)))

theorem lawOfCosines : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 cosinesFormula :=
  closeAll 12 (by unfold cosinesFormula A B C; ipra_ring)

end Coordinates

end LeanProofs.IPRA.Geometry.TriangleFormulas
