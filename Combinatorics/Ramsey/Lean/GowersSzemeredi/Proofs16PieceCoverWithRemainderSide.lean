import GowersSzemeredi.Proofs16PieceCoverWithRemainder
import GowersSzemeredi.Proofs16CubicCapBound

/-! Declarations of `Proofs16PieceCoverWithRemainder` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The capped exponent of the piece cover keeps a constant multiple of the
product of the line and slice exponents. -/
theorem piece_cover_exponent_lower {A Bq : Nat → Real} {Qb Eb Qr Er : Real → Real}
    {Es : Nat → Real → Real} {zeta rho : Real}
    (hz : 0 < pieceWidthScale A Qb zeta rho) (hz1 : pieceWidthScale A Qb zeta rho ≤ 1)
    (he : 0 < pieceLineExponent Bq Qb Eb Er rho) (he1 : pieceLineExponent Bq Qb Eb Er rho ≤ 1)
    (ha : 0 < pieceSliceExponent Qr Es rho) (ha1 : pieceSliceExponent Qr Es rho ≤ 1) :
    pieceLineExponent Bq Qb Eb Er rho * pieceSliceExponent Qr Es rho /
        (16 + 4 * Real.log (16 / pieceWidthScale A Qb zeta rho)) ≤
      section16CappedWidthExponent
        (pieceLineExponent Bq Qb Eb Er rho * pieceSliceExponent Qr Es rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb zeta rho)
          (pieceLineExponent Bq Qb Eb Er rho) (pieceSliceExponent Qr Es rho)) :=
  section16_cubic_capped_exponent_lower hz hz1 he he1 ha ha1

end LeanProofs.GowersSzemeredi
