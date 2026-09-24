import Surreal.Foundations.OmnificBinomialRoots
import Surreal.Surcomplex.AngleRoots
import Surreal.Surcomplex.NormalFormDegree
import Surreal.Surcomplex.GaussianNormalizationEmbedding

/-!
# All roots of omega^g + 1 are outside the Gaussian omnific ring

The root nonexistence and expansion clauses of `osq:nm:thm:invisible`,
`osq:nm:eq:rootexpansion` and `osq:nm:rem:rootinN`. Divide any root by
the constructed positive real root and use the existing classification
of actual roots of unity. Each root is an ordinary complex root of unity
times that real root, with a nonzero coefficient at g/m-g.
The universal small-target homomorphism assertion is separate.
-/

universe u
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- Multiplication by an ordinary complex constant scales every growth coefficient. -/
theorem growthCoeff_ofComplex_mul (c : ℂ) (z : Surcomplex.{u}) (a : SignSequence.{u}) :
    growthCoeff (ofComplex c * z) a = c * growthCoeff z a := by
  rw [growthCoeff, rawNormalForm_mul, rawNormalForm_ofComplex,
    _root_.HahnSeries.coeff_single_zero_mul]
  rfl

/-- Actual Gaussian omnific integers have zero coefficient at every negative growth exponent. -/
theorem gaussianOmnific_growthCoeff_neg (z : GaussianOmnificInteger.{u})
    (a : SignSequence.{u}) (ha : a < 0) : growthCoeff (gaussianOmnificToSurcomplex z) a = 0 := by
  rw [growthCoeff, coeff_rawNormalForm]
  apply Complex.ext
  · exact (SignSequence.mem_nonnegativeSupportSubring_iff _).mp z.val.property.1 a ha
  · exact (SignSequence.mem_nonnegativeSupportSubring_iff _).mp z.val.property.2 a ha

/-- Every surcomplex root is an ordinary root-of-unity multiple of the explicit real root. -/
theorem binomial_root_iff (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) (hm : m ≠ 0)
    (z : Surcomplex.{u}) :
    z ^ m = ofReal (SignSequence.omegaPower g) + 1 ↔
      ∃ c : ℂ, c ^ m = 1 ∧ z = ofComplex c * ofReal (SignSequence.omnificBinomialRoot g hg m) := by
  have hr : ofReal (SignSequence.omnificBinomialRoot g hg m) ≠ (0 : Surcomplex.{u}) :=
    (map_ne_zero_iff ofReal ofReal_injective).mpr (SignSequence.omnificBinomialRoot_pos g hg m).ne'
  have hp : ofReal (SignSequence.omnificBinomialRoot g hg m) ^ m =
      ofReal (SignSequence.omegaPower g) + 1 := by
    rw [← map_pow, SignSequence.omnificBinomialRoot_pow g hg m hm, map_add, map_one]
  constructor
  · intro hz
    have hd : (z / ofReal (SignSequence.omnificBinomialRoot g hg m)) ^ m = 1 := by
      rw [div_pow, hz, ← hp, div_self (pow_ne_zero m hr)]
    obtain ⟨c, hc, he⟩ := (pow_eq_one_iff_exists_complex m (Nat.pos_of_ne_zero hm) _).mp hd
    exact ⟨c, hc, (div_eq_iff hr).mp he.symm⟩
  · rintro ⟨c, hc, rfl⟩
    rw [mul_pow, ← map_pow, hc, map_one, one_mul, hp]

/-- Every coefficient in the displayed complex root expansion is the scaled rational coefficient. -/
theorem binomial_root_coeff (g : SignSequence.{u}) (hg : 0 < g) (m n : ℕ) (c : ℂ) :
    growthCoeff (ofComplex c * ofReal (SignSequence.omnificBinomialRoot g hg m))
      (g / (m : SignSequence) + (n : SignSequence) * (-g)) =
        c * ((Ring.choose (1 / (m : ℚ)) n : ℚ) : ℂ) := by
  rw [growthCoeff_ofComplex_mul, growthCoeff_ofReal, SignSequence.omnificBinomialRoot_coeff]
  simp only [Complex.ofReal_ratCast]

/-- The second coefficient in every displayed root expansion is precisely c/m. -/
theorem binomial_root_second_term (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) (c : ℂ) :
    growthCoeff (ofComplex c * ofReal (SignSequence.omnificBinomialRoot g hg m))
      (g / (m : SignSequence) - g) = c / (m : ℂ) := by
  rw [growthCoeff_ofComplex_mul, growthCoeff_ofReal, SignSequence.omnificBinomialRoot_second_term]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast, mul_one_div]

/-- No Gaussian omnific integer solves T^m = omega^g + 1 at any positive scale and m ≥ 2. -/
theorem gaussianOmnific_no_root_omegaPower_add_one (g : SignSequence.{u}) (hg : 0 < g)
    (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∃ a : GaussianOmnificInteger.{u},
      gaussianOmnificToSurcomplex a ^ m = ofReal (SignSequence.omegaPower g) + 1 := by
  rintro ⟨a, ha⟩
  have hm0 : m ≠ 0 := by omega
  obtain ⟨c, hc, he⟩ := (binomial_root_iff g hg m hm0 _).mp ha
  have hc0 : c ≠ 0 := by
    intro h
    simp only [h, zero_pow hm0, zero_ne_one] at hc
  have hz := gaussianOmnific_growthCoeff_neg a _
    (SignSequence.omnificBinomialRoot_second_exponent_neg g hg m hm)
  rw [he, binomial_root_second_term] at hz
  exact (div_ne_zero hc0 (Nat.cast_ne_zero.mpr hm0)) hz

/-- Every actual root is nevertheless integral over the Gaussian omnific ring. -/
theorem gaussianOmnific_binomial_root_isIntegral (g : SignSequence.{u}) (hg : 0 < g)
    (m : ℕ) (hm : m ≠ 0) (z : Surcomplex.{u})
    (hz : z ^ m = ofReal (SignSequence.omegaPower g) + 1) : IsIntegral GaussianOmnificInteger z := by
  apply IsIntegral.of_pow (Nat.pos_of_ne_zero hm)
  rw [hz]
  apply IsIntegral.add _ isIntegral_one
  apply gaussianOmnific_isIntegral_ofReal
  exact isIntegral_algebraMap (x := SignSequence.omnificMonomial g hg)

end
end Surreal.Surcomplex
