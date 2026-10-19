import GowersSzemeredi.Proofs16Lemma9WithRemainder
import GowersSzemeredi.Proofs16CubicAllScaleCover

/-! The cover of one structured piece with every control explicit.

The existing piece covers (`AllScalePolynomialMultilinearCoverAt`,
`Section16AllBoxLineCoversWith.cubic_multiplyLinearWith`) take the
cross-section remainder with Gowers's printed `(γ, R)` controls. Here the
remainder has arbitrary controls `(Qr, Er)` on a sub-domain `D ⊆ B₁`. The
spectrum has controls `(Qb, Eb)`, and the slices have a provider `(Pb, Es)`.
The result is a `MultiplyLinearWith` cover of `φ₁` on `D` at every scale:
* the graph count is `pieceGraphBound`, polynomial in `Pb` at the sample
  bound `pieceSamples ≈ 24·Qr(ρ/8)/ρ`;
* the width exponent is the capped `e·a/4` of the line exponent
  `e = Er·Eb / B(⌊Qb⌋)` and the slice exponent `a = Es`. By
  `piece_cover_exponent_lower` (in `Proofs16PieceCoverWithRemainderSide`, outside the
  final route) it is at least `e·a/(16 + 4 log(16/z))`,
  where `z = ζ/A(⌊Qb⌋)`.

So the piece cover is polynomial whenever the inputs are. Lemma 16.6
enters through `AllScaleLemma166WidthAt` at the power width
`section16PowerWidth A B`. The polynomial width
`section16PolynomialLinearityWidth` is this form, with `A`, `B` polynomial
in the spectrum count.

`pieceGraphBound`, `pieceSamples_pos`, `pieceSliceExponent`,
`section16_piece_cover_with` and `section16_piece_large_box_profile` are in
`Proofs16PieceCoverWithRemainderSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A power-shaped linearity width `ζ/A(q) · m^(a/B(q))`. -/
def section16PowerWidth (A Bq : Nat → Real) (m q : Nat) (a zeta : Real) : Real :=
  zeta / A q * (m : Real) ^ (a / Bq q)

theorem section16PowerWidth_transfer {A Bq : Nat → Real}
    (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q) : Section16WidthTransfer (section16PowerWidth A Bq) := by
  intro m n q a c zeta hz ha _ hcell
  unfold section16PowerWidth
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hz (hA q).le)
  rw [mul_div_assoc, Real.rpow_mul (Nat.cast_nonneg m)]
  exact Real.rpow_le_rpow (by positivity) hcell (div_nonneg ha (hB q).le)

/-- The line exponent: the remainder and spectrum exponents through the power width. -/
def pieceLineExponent (Bq : Nat → Real) (Qb Eb Er : Real → Real) (rho : Real) : Real :=
  Er (rho / 8) * Eb (rho / 8) / Bq ⌊Qb (rho / 8)⌋₊

/-- The prefactor of the power width at loss `ρ`. -/
def pieceWidthScale (A : Nat → Real) (Qb : Real → Real) (zeta rho : Real) : Real :=
  zeta / A ⌊Qb (rho / 8)⌋₊

end LeanProofs.GowersSzemeredi
