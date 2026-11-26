import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialTermBound
import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialDiskMajorant
import IPRADerivations.Analysis.Exponential.FiniteSeries.BinomialExponentialGap
import IPRADerivations.Combinatorics.BinomialIdentities

/-!
# The actual positive exponential at an integer dominates the dyadic power

For every included binomial term at an internal natural argument R,
`fact(j) * choose(R,j) ≤ R^j`. The cleared numerator of the original
finite factorial sum preserves the resulting lower bound under its own
recurrence. The full binomial sum gives `2^R`, and all later finite
cutoffs preserve that bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNaturalExponentialDyadicBound

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (bBody inst2_b binom_zero')
open GaussianExponentialDiskMajorant (numerator numerator_zero numerator_succ real_majorant_represents)
open GaussianRationalPolynomialExponential (scalarSum scalarBody factorial_positive)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalHorner (ofGaussian canonical_unique represents_congr)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_represents radius_numerator_norm)
open GaussianRationalLowerBounds (lower lower_from_representation lower_congr)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open Products (fact)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def binomialPrefix (R K : PTm n) : PTm n := ap2 (sumF bBody) (succ K) R
def prefixLower (R K : PTm n) : Fm PTm n :=
  le K R ⟶ le (fact (succ K)*binomialPrefix R K) (numerator R K)

ipra_subst binomialPrefix
ipra_subst prefixLower [fact]

theorem prefix_zero (R : PTm n) : Γ ⊢[PRAAx] binomialPrefix R zero ≐ one := by
  unfold binomialPrefix
  refine (sum_succ' bBody zero R).eqTrans ?_
  rw [inst2_b]
  exact (congrAdd (sum_zero _ _) (binom_zero' R)).eqTrans (zero_add _)

theorem prefix_succ (R K : PTm n) : Γ ⊢[PRAAx]
    binomialPrefix R (succ K) ≐ binomialPrefix R K+binom R (succ K) := by
  simpa only [binomialPrefix, inst2_b] using sum_succ' (Γ := Γ) bBody (succ K) R

theorem cleared_term (R j : PTm n) (hj : Γ ⊢[PRAAx] le j R) :
    Γ ⊢[PRAAx] le (fact j*binom R j) (pw R j) :=
  le_congr (Combinatorics.FallingFactorial.ff_binom hj) (.eqRefl _) (BinomialExponentialGap.ff_le_pw R j)

private theorem lower_step (R K : PTm n) (hj : Γ ⊢[PRAAx] le (succ K) R)
    (old : Γ ⊢[PRAAx] le (fact (succ K)*binomialPrefix R K) (numerator R K)) :
    Γ ⊢[PRAAx] le (fact (succ (succ K))*binomialPrefix R (succ K)) (numerator R (succ K)) := by
  have full := mul_le_mul_right (succ (succ K)) (add_le_add₂ old (cleared_term R (succ K) hj))
  have ff := natEq (fact_succ (Γ := Γ) (succ K) zero)
  have bp := natEq (prefix_succ (Γ := Γ) R K)
  exact le_congr (by
    apply deriveNat
    ipra_simps
    rw [ff, bp]
    ring) (numerator_succ R K).eqSymm full

theorem original_prefix_bound (R K : PTm n) (hK : Γ ⊢[PRAAx] le K R) :
    Γ ⊢[PRAAx] le (fact (succ K)*binomialPrefix R K) (numerator R K) := by
  have law : Γ ⊢[PRAAx] .all (prefixLower (Syn.shift R) (var 0)) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_prefixLower]
    · refine .impI ?_
      have e : (le zero R :: Γ) ⊢[PRAAx] fact (succ (zero : PTm n)) ≐ one :=
        (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl _)).eqTrans (one_mul _))
      exact le_congr ((congrMul e (prefix_zero R)).eqTrans (one_mul _)).eqSymm (numerator_zero R).eqSymm (le_refl one)
    · refine .impI (lower_step _ _ Prf.hyp0 ?_)
      exact .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
  have atK : Γ ⊢[PRAAx] prefixLower R K := by
    simpa only [subst_prefixLower, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using law.allE K
  exact .impE atK hK

theorem natural_scalar_partial_lower (R : PTm n) :
    Γ ⊢[PRAAx] rationalLE (natCode (unit R)) (fstT (scalarSum (naturalPoint R) R)) := by
  have h := original_prefix_bound (Γ := Γ) R R (le_refl R)
  have full : Γ ⊢[PRAAx] binomialPrefix R R ≐ unit R := by
    simpa [binomialPrefix, unit] using
      LeanProofs.IPRA.inst (Γ := Γ) Combinatorics.BinomialIdentities.binom_sum_open (![R] : Fin 1 → PTm n)
  have lower : Γ ⊢[PRAAx] le (fact (succ R)*unit R) (numerator R R*one) :=
    le_congr (congrMul (.eqRefl _) full) (by ipra_ring) h
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ one (fact (succ R)) (le_refl one)
    (factorial_positive _) (natCode_represents _) (real_majorant_represents R R) lower

theorem original_natural_scalar_dyadic_lower (R K : PTm n) (h : Γ ⊢[PRAAx] le R K) :
    Γ ⊢[PRAAx] lower (scalarSum (naturalPoint R) K) (unit R) one := by
  let q := scalarSum (naturalPoint R) K
  let D := fact (succ K)
  let N := numerator R K
  have mono := GaussianPositiveExponentialTermBound.prefix_real_mono (naturalPoint R) (succ R) (succ K)
    (GaussianPositiveRealArithmetic.positive_natural R) ((succ_monus_succ R K).eqTrans h)
  have comparison := RationalArgmin.transitive (natural_scalar_partial_lower R) mono
  have hrep := real_majorant_represents (Γ := Γ) R K
  have cleared : Γ ⊢[PRAAx] le (D*unit R) (N*one) :=
    GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ (natCode_represents _) hrep comparison
  have positive := GaussianPositiveExponentialProduct.positive_scalar_sum (Γ := Γ) (naturalPoint R) K
    (GaussianPositiveRealArithmetic.positive_natural R)
  have eq := (GaussianTranslatedNonconstant.recode_eq q (GaussianRationalFiniteSum.sum_canonical scalarBody (succ K)
    (naturalPoint R))).eqSymm.eqTrans (RationalGaussianEmbedding.axis_roundtrip q positive.andE₁)
  have rep := represents_congr eq.eqSymm (GaussianRootAlgebra.equal_refl (radiusNumerator N)) (.eqRefl D)
    (RationalGaussianEmbedding.embed_from_representation (fstT q) (ZT.ofNat N) D hrep)
  apply lower_from_representation _ _ _ _ _ (factorial_positive _) (le_refl one) rep
  exact le_congr (by ipra_ring)
    ((by ipra_ring : Γ ⊢[PRAAx] (N*one)*(N*one) ≐ one*one*(N*N)).eqTrans
      (congrMul (.eqRefl _) (radius_numerator_norm N).eqSymm)) (sq_le_sq cleared)

theorem original_finite_natural_exponential_dyadic_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 0) (var 1) ⟶ lower (scalarSum (naturalPoint (var 0)) (var 1)) (unit (var 0)) one) :=
  closeUniv 2 (.impI (original_natural_scalar_dyadic_lower _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNaturalExponentialDyadicBound
