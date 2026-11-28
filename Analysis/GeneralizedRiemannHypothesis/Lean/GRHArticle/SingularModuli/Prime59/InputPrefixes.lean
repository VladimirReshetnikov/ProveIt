import GRHArticle.SingularModuli.Prime59.WitnessComputation
import GRHArticle.SingularModuli.IntegerListCheckpoint
import GRHArticle.SingularModuli.HeckeWeightedCoefficientBound
import GRHArticle.SingularModuli.HeckeChunkedPrefixCertificate

/-!
# Coefficient witnesses for the level-59 diagonal

The two lists are generated at elaboration time. Subsequent modules check
their coefficients against the formal modular series.
-/

namespace GRHArticle.SingularModuli.Prime59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The length needed for the modular-series prefixes. -/
def invariantPrecision : ℕ := 6963

/-- The degree bound of the signed diagonal, plus one. -/
def diagonalPrecision : ℕ := 119

def discriminantBlocks : List (List ℤ) :=
  integer_blocks_checkpoint% (polynomialDigitChunks (discriminantWitness invariantPrecision))

def discriminant : List ℤ := discriminantBlocks.flatten

def invariantBlocks : List (List ℤ) :=
  integer_blocks_checkpoint%
    (polynomialDigitChunks (invariantWitness invariantPrecision discriminant))

def invariant : List ℤ := invariantBlocks.flatten

def invariantNatural : List ℕ := invariant.map Int.toNat

def shortInvariant : List ℤ := invariant.take diagonalPrecision

/-- The dyadic upper-bound exponent for the nonnegative invariant prefix. -/
def dyadicExponent : ℕ := 82

theorem invariant_length : invariant.length = invariantPrecision := by decide +kernel

theorem discriminant_length : discriminant.length = invariantPrecision := by decide +kernel

end GRHArticle.SingularModuli.Prime59
