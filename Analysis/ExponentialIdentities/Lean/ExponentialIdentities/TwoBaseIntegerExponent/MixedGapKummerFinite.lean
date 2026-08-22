import Mathlib.Tactic

/-!
# Finite mixed-gap Kummer algebra

This file isolates the bounded algebra behind the mixed-gap Kummer-symbol
obstruction.  The character values are represented by arbitrary elements of a
commutative ring.  There is no Kummer realization, Frobenius distribution, or
Chebotarev input here.

The final theorem is the valuation-level denominator observation used after a
separator prime is known: if at least one numerator has valuation zero, one of
the two reduced denominators retains at least the minimum of the original
denominator valuations.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace MixedGapKummerFinite

/-- The determinant of the two abstract residue-character rows
`(kTwo, kThree)` and `(kM, kA)`. -/
def kummerDeterminant {R : Type*} [CommRing R]
    (kTwo kThree kM kA : R) : R :=
  kTwo * kA - kThree * kM

/-- Abstract mixed-gap determinant identity.

For an additive residue character, the hypotheses are the images of
`M^q = 2^p` and `A^q = 3^p'`.  The conclusion is valid over every
commutative ring and uses no division by `q`.
-/
theorem mixedGap_determinant_identity
    {R : Type*} [CommRing R]
    (kTwo kThree kM kA q p p' : R)
    (hM : q * kM = p * kTwo)
    (hA : q * kA = p' * kThree) :
    q * kummerDeterminant kTwo kThree kM kA =
      (p' - p) * kTwo * kThree := by
  unfold kummerDeterminant
  linear_combination kTwo * hA - kThree * hM

/-- Equal residue exponents force the abstract Kummer determinant to vanish. -/
theorem kummerDeterminant_eq_zero_of_sameResidue
    {R : Type*} [CommRing R]
    (kTwo kThree kM kA e : R)
    (hM : kM = e * kTwo)
    (hA : kA = e * kThree) :
    kummerDeterminant kTwo kThree kM kA = 0 := by
  rw [kummerDeterminant, hM, hA]
  ring

/-- A nonzero determinant excludes simultaneous realization with one residue
exponent. -/
theorem sameResidue_obstruction
    {R : Type*} [CommRing R]
    (kTwo kThree kM kA : R)
    (hdet : kummerDeterminant kTwo kThree kM kA ≠ 0) :
    ¬ ∃ e : R, kM = e * kTwo ∧ kA = e * kThree := by
  rintro ⟨e, hM, hA⟩
  exact hdet (kummerDeterminant_eq_zero_of_sameResidue
    kTwo kThree kM kA e hM hA)

/-- Valuation-level denominator retention.

Here `dTwo,dThree` are the original denominator valuations and
`nTwo,nThree` are the numerator valuations.  Natural subtraction is exactly
the reduced-denominator valuation.  If one numerator valuation is zero, the
larger of the two surviving valuations is at least the smaller original
denominator valuation.
-/
theorem denominatorRetention_of_one_numerator_uncancelled
    (dTwo dThree nTwo nThree : ℕ)
    (huncancelled : nTwo = 0 ∨ nThree = 0) :
    min dTwo dThree ≤ max (dTwo - nTwo) (dThree - nThree) := by
  omega

end MixedGapKummerFinite
end LeanProofs.TwoBaseIntegerExponent
