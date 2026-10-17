import GowersSzemeredi.Proofs16PolyPieceTwoInputs
import GowersSzemeredi.Proofs16PieceCoverWithRemainder
import GowersSzemeredi.Proofs16RoundedPowerWidth

/-! **One polynomial piece in dimension two.**

Let `(B, φ)` be a two-dimensional partial function. Assume it is dense in
eight-arrangements, respects almost all of them (the hypotheses of Lemma
16.4), and has the product property. Then a base point `x₀` and a dense
domain `D` exist on which `φ₁(h, x) = φ(x₀ + h, x)` is
`MultiplyLinearWith` at every scale, with explicit controls.

All four inputs of `section16_piece_cover_with` come from the proved
dimension-one cover `polyCoverAt_one`, off three global deletions of
`θ′N²` points each (`θ′ = θ₂/8`, `polyPieceBudget`):
* the spectrum relation, at the parameter `δ`, off its good set `JΔ`;
* the remainder, which is the single vertex `φ(x₀, x)`
  (`remainder_multiplyLinearWith_one_of_polyCover`), off the face's good
  fibres `Jr`;
* the slices, through Freiman families of every final-coordinate slice
  (`section16_final_freiman_families_of_product`), off `θ′N` points per
  slice.

The good domain of Lemma 16.7 has at least `θ₂N² = 8θ′N²` points, so `D`
keeps `5θ′N²`. The graph counts are `3·q(δ,θ′)`, `max(3·q(γ,θ′), 9)` and
`3·max(1,r)·q(γ,θ′)`, where `q = section16BaseFamilyBound`. Their width
exponents are the cubic `cubicBaseExponent`. So the piece cover is
polynomial in `1/ρ` and in `q(δ,θ′)`, `q(γ,θ′)`. The only remaining input
is Lemma 16.6 at a power width.

`section16_poly_piece_two_original` translates back by `(x₀, 0)`. It gives
a subset `D′ ⊆ B` of at least `5θ′N²` points on which `φ` itself has the
same cover: the extraction step of Theorem 16.2's loop in dimension two.

`section16_poly_piece_two` and `section16_poly_piece_two_original` are in
`Proofs16PolyPieceTwoSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The deletion budget: `θ₂/8`. -/
def polyPieceBudget (theta gamma : Real) : Real :=
  section16ThetaTwo (section16ThetaOne theta gamma 1) / 8

/-- The Freiman-family count of the spectrum relation. -/
def polyPieceSpecCount (theta gamma : Real) : Nat :=
  section16BaseFamilyBound (section16Delta (section16ThetaOne theta gamma 1))
    (polyPieceBudget theta gamma)

/-- The Freiman-family count of the faces and slices. -/
def polyPieceFaceCount (theta gamma : Real) : Nat :=
  section16BaseFamilyBound gamma (polyPieceBudget theta gamma)

def polyPieceTwoQb (theta gamma : Real) : Real → Real :=
  fun _ => ((3 * polyPieceSpecCount theta gamma : Nat) : Real)

def polyPieceTwoEb (theta gamma : Real) : Real → Real :=
  cubicBaseExponent (polyPieceSpecCount theta gamma)

def polyPieceTwoQr (theta gamma : Real) : Real → Real :=
  fun _ => max ((3 * polyPieceFaceCount theta gamma : Nat) : Real) 9

def polyPieceTwoEr (theta gamma : Real) : Real → Real :=
  fun s => cubicBaseExponent (polyPieceFaceCount theta gamma) s / 16

def polyPieceTwoPb (theta gamma : Real) : Nat → Real → Real :=
  fun r _ => ((3 * (max 1 r * polyPieceFaceCount theta gamma) : Nat) : Real)

def polyPieceTwoEs (theta gamma : Real) : Nat → Real → Real :=
  fun r => cubicBaseExponent (max 1 r * polyPieceFaceCount theta gamma)

/-- The graph count of the dimension-two piece. -/
def polyPieceTwoCount (theta gamma : Real) : Real → Real :=
  fun rho => max (pieceGraphBound (polyPieceTwoQr theta gamma) (polyPieceTwoPb theta gamma) rho)
    ((3 ^ (1 + 1) : Nat) : Real)

/-- The width exponent of the dimension-two piece. -/
def polyPieceTwoExponent (A Bq : Nat → Real) (theta gamma : Real) : Real → Real :=
  fun rho => section16CappedWidthExponent
    (pieceLineExponent Bq (polyPieceTwoQb theta gamma) (polyPieceTwoEb theta gamma)
        (polyPieceTwoEr theta gamma) rho *
      pieceSliceExponent (polyPieceTwoQr theta gamma) (polyPieceTwoEs theta gamma) rho / 4)
    (section16RoundedPowerThreshold
      (pieceWidthScale A (polyPieceTwoQb theta gamma) (section16Zeta theta gamma 1) rho)
      (pieceLineExponent Bq (polyPieceTwoQb theta gamma) (polyPieceTwoEb theta gamma)
        (polyPieceTwoEr theta gamma) rho)
      (pieceSliceExponent (polyPieceTwoQr theta gamma) (polyPieceTwoEs theta gamma) rho))

theorem appendCoordinate_init_add {N : Nat} (z : Point N 2) (x0 : Point N 1) :
    appendCoordinate (section16Init z + x0) (section16Last z) = z + appendCoordinate x0 0 := by
  conv_rhs => rw [← appendCoordinate_init_last z]
  rw [appendCoordinate_add, add_zero]

end LeanProofs.GowersSzemeredi
