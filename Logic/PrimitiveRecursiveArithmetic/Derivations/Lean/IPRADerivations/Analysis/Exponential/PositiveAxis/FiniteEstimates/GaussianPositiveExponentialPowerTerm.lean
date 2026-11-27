import IPRADerivations.Analysis.Exponential.PositiveAxis.FiniteEstimates.GaussianPositiveExponentialTermBound
import IPRADerivations.Analysis.FiniteOperations.FiniteProducts.GaussianPositiveScalarProductBound
import IPRADerivations.Analysis.Euler.Integration.Incomplete.IntegerValues.GaussianEulerIncompleteFactorialPolynomial
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmName

/-!
# The actual factorial-term comparison for logarithmic lower tails

At every nonnegative Gaussian rational input, the included j-th term of
the original finite exponential bounds its j-th power after multiplication
by j!. The norm comparison uses the actual normalized arithmetic and its
positive real order. In particular it applies to the genuine nonnegative
harmonic logarithm observations above one. No exponential output bound or
completed logarithmic power majorant is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveExponentialPowerTerm

open_ipra
open GaussianPositiveRealArithmetic (positive positive_power positive_natural)
open GaussianRationalHorner (qmul canonical)
open GaussianRationalReciprocal (power bounded_product bound_congr)
open GaussianRationalNaturalScale (naturalPoint natScale natScale_as_product natScale_canonical)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianScalarExponentialDiagonal (coefficient)
open GaussianRationalMetric (bounded)
open RationalArgmin (rationalLE rationalLE_congr)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem factorial_power_order (q j K : PTm n) (hq : Γ ⊢[PRAAx] positive q)
    (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx]
    rationalLE (fstT (power q j)) (fstT (natScale (fact j) (scalarSum q K))) := by
  let F := naturalPoint (fact j)
  have multiplied := RationalArithmetic.multiply_monotone (fstT F) _ _
    (positive_natural (fact j)).andE₂
    (GaussianPositiveExponentialTermBound.original_term_le q j K hq hj)
  have left := (congrFst (natScale_as_product (Γ := Γ) (fact j) (coefficient q j))).eqTrans
    (GaussianPositiveExponentialProduct.real_product F (coefficient q j)
      (GaussianPositiveExponentialProduct.positive_coefficient q j hq).andE₁)
  have right := (congrFst (natScale_as_product (Γ := Γ) (fact j) (scalarSum q K))).eqTrans
    (GaussianPositiveExponentialProduct.real_product F (scalarSum q K)
      (GaussianPositiveExponentialProduct.positive_scalar_sum q K hq).andE₁)
  have cancel := congrFst (GaussianEulerIncompleteFactorialPolynomial.factorial_term_cancellation (Γ := Γ) j (power q j)
    (GaussianRationalReciprocal.power_canonical q j))
  exact rationalLE_congr (left.eqSymm.eqTrans cancel) right.eqSymm multiplied

/-- The finite factorial sum remains the original scalarSum, at the
given cutoff K. Its norm bound is transported with the exact factor j!. -/
theorem finite_power_bound (q j K A B : PTm n) (hq : Γ ⊢[PRAAx] positive q)
    (hj : Γ ⊢[PRAAx] le j K) (hB : Γ ⊢[PRAAx] le one B)
    (hs : Γ ⊢[PRAAx] bounded (scalarSum q K) A B) : Γ ⊢[PRAAx]
    bounded (power q j) (fact j*A) B := by
  let u := power q j
  let v := natScale (fact j) (scalarSum q K)
  have vc : Γ ⊢[PRAAx] canonical v := natScale_canonical _ _
  have vp : Γ ⊢[PRAAx] positive v :=
    GaussianPositiveRealArithmetic.positive_congr (natScale_as_product _ _).eqSymm
      (GaussianPositiveRealArithmetic.positive_multiply _ _ (positive_natural _)
        (GaussianPositiveExponentialProduct.positive_scalar_sum q K hq))
  have product := bounded_product (naturalPoint (fact j)) (scalarSum q K) (fact j) one A B
    (le_refl one) hB (GaussianNamedNaturalScale.natural_point_bound _) hs
  have vb : Γ ⊢[PRAAx] bounded v (fact j*A) B :=
    bound_congr (natScale_as_product _ _).eqSymm (.eqRefl _) (one_mul _) product
  have oneV := GaussianPolynomialDeterminantTerms.one_mul_canonical v vc
  have original := GaussianPositiveScalarProductBound.product_bound_monotone
    GaussianRationalSyntheticDivision.qone u v (fact j*A) B hB
    (GaussianRationalReciprocal.power_canonical q j) vc (positive_power q j hq) vp.andE₁
    (factorial_power_order q j K hq hj) (bound_congr oneV.eqSymm (.eqRefl _) (.eqRefl _) vb)
  exact bound_congr (GaussianPolynomialDeterminantTerms.one_mul_canonical u
    (GaussianRationalReciprocal.power_canonical q j)) (.eqRefl _) (.eqRefl _) original

theorem harmonic_sample_positive (p a b : PTm n) (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    positive (GaussianHarmonicLogarithmName.sample p a b) := by
  let Q := GammaEulerConstantName.mesh (GaussianHarmonicLogarithmName.clock p)
  have sign := GaussianRationalL1.nonnegative_of_lower _ (RationalHarmonicInterval.interval a b Q)
    (GaussianRationalSyntheticBounds.natCode_nonnegative ConciseIPRA.PTm.zero)
    (GaussianPositiveRationalLogarithmSign.interval_nonnegative a b Q h)
  exact GaussianPositiveRealArithmetic.positive_congr (GaussianHarmonicLogarithmName.sample_at p a b).eqSymm
    (GaussianPositiveRealArithmetic.positive_embed _ sign)

theorem harmonic_logarithm_factorial_term (p a b j K : PTm n) (h : Γ ⊢[PRAAx] le b a)
    (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx]
    rationalLE (fstT (power (GaussianHarmonicLogarithmName.sample p a b) j))
      (fstT (natScale (fact j) (scalarSum (GaussianHarmonicLogarithmName.sample p a b) K))) :=
  factorial_power_order _ j K (harmonic_sample_positive p a b h) hj

theorem actual_positive_finite_exponential_factorial_power_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((positive (var 0) ⋏ le (var 1) (var 2)) ⟶ le one (var 4) ⟶
      bounded (scalarSum (var 0) (var 2)) (var 3) (var 4) ⟶
      bounded (power (var 0) (var 1)) (fact (var 1)*var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (finite_power_bound _ _ _ _ _ hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0))))

theorem actual_harmonic_logarithm_factorial_term_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le (var 2) (var 1) ⋏ le (var 3) (var 4)) ⟶
      rationalLE (fstT (power (GaussianHarmonicLogarithmName.sample (var 0) (var 1) (var 2)) (var 3)))
        (fstT (natScale (fact (var 3))
          (scalarSum (GaussianHarmonicLogarithmName.sample (var 0) (var 1) (var 2)) (var 4))))) :=
  closeUniv 5 (.impI (harmonic_logarithm_factorial_term _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPositiveExponentialPowerTerm
