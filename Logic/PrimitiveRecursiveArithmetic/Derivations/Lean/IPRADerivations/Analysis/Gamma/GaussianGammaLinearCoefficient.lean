import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaCoefficientNorm
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaCanonicalExponent
import IPRADerivations.Analysis.Exponential.GaussianFiniteExponentialWeightedNorm
import IPRADerivations.Analysis.Exponential.GaussianPositiveExponentialMajorant

/-!
# The actual original Gamma linear coefficient and its stored monomial

The unchanged original gamma sample and harmonic rational form the
coefficient gamma_q-H_N. Its absolute coefficient norm is at most N+1.
An actual two-entry coefficient buffer evaluates to that coefficient
times the original query and has weighted mass at radius R at most
R(N+1). The sample precision is independent of the evaluation point.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaLinearCoefficient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul evaluate qzero)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalReciprocal (power)
open GaussianRationalPolynomialBuffers (appendZero)
open GaussianRationalMonicReduction (singleton)
open GaussianRationalPolynomialDilation (dilated weightedNorm)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianRationalL1 (qL1)
open GaussianCoefficientL1 (prefixNorm)
open GaussianGammaCanonicalExponent (harmonic harmonicPoint harmonic_represents)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalArgmin (rationalLE)
open RationalGaussianEmbedding (embed)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (q N : PTm n) : PTm n := qsub (embed (GammaEulerConstantName.gammaSample q zero)) (harmonicPoint N)
def monomial (a : PTm n) : PTm n := appendZero (singleton a)
def polynomial (q N : PTm n) : PTm n := monomial (coefficient q N)
@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (q N : PTm n) :
    Syn.subst σ (coefficient q N) = coefficient (Syn.subst σ q) (Syn.subst σ N) := by simp [coefficient]
@[simp] theorem subst_monomial {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (monomial a) = monomial (Syn.subst σ a) := by simp [monomial]
@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (q N : PTm n) :
    Syn.subst σ (polynomial q N) = polynomial (Syn.subst σ q) (Syn.subst σ N) := by simp [polynomial]

theorem gamma_norm (q : PTm n) : Γ ⊢[PRAAx]
    rationalLE (qL1 (embed (GammaEulerConstantName.gammaSample q zero))) (natCode one) := by
  have range := GammaEulerConstantName.gamma_sample_range (Γ := Γ) q zero
  have sign := GaussianRationalL1.nonnegative_of_lower _ _ (GaussianRationalSyntheticBounds.natCode_nonnegative zero) range.andE₁
  exact RationalArgmin.rationalLE_congr
    (GaussianGammaZetaCoefficientNorm.nonnegative_embed_norm _ sign (GammaEulerConstantName.gamma_sample_canonical q zero)).eqSymm
    (.eqRefl _) range.andE₂

theorem harmonic_norm (N : PTm n) : Γ ⊢[PRAAx] rationalLE (qL1 (harmonicPoint N)) (natCode N) := by
  have hF := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) N
  have sign := GaussianRationalL1.nonnegative_of_representation _ _ _ hF (harmonic_represents N)
  have scalar := GaussianRationalMetric.comparison_of_cleared _ _ _ _ (Products.fact N) one hF (le_refl one)
    (harmonic_represents N) (natCode_represents N)
    (le_congr (by ipra_ring) (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.FactorialError.S_le N (Products.fact N)))
  exact RationalArgmin.rationalLE_congr
    (GaussianGammaZetaCoefficientNorm.nonnegative_embed_norm _ sign (GaussianGammaCanonicalExponent.harmonic_canonical N)).eqSymm
      (.eqRefl _) scalar

theorem coefficient_norm (q N : PTm n) : Γ ⊢[PRAAx] rationalLE (qL1 (coefficient q N)) (natCode (succ N)) := by
  have first := GaussianRationalL1Algebra.qL1_sub (Γ := Γ)
    (embed (GammaEulerConstantName.gammaSample q zero)) (harmonicPoint N)
  have second := GaussianRationalSyntheticBounds.add_monotone (Γ := Γ) _ _ _ _ (gamma_norm q) (harmonic_norm N)
  have budget := (GaussianRationalSyntheticBounds.natCode_add (Γ := Γ) one N).eqTrans
    (GaussianPositiveExponentialMajorant.natCode_congr (show Γ ⊢[PRAAx] one+N ≐ succ N by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) budget (RationalArgmin.transitive first second)

theorem monomial_length (a : PTm n) : Γ ⊢[PRAAx] length (monomial a) ≐ two :=
  (GaussianRationalPolynomialBuffers.append_length _).eqTrans (congrSucc (GaussianRationalMonicReduction.singleton_length a))
theorem monomial_leading (a : PTm n) : Γ ⊢[PRAAx] entry (monomial a) zero ≐ a := by
  have len := GaussianRationalMonicReduction.singleton_length (Γ := Γ) a
  exact (GaussianRationalPolynomialBuffers.append_lookup _ zero (zero_le _)).eqTrans
    ((GaussianRationalLinearProduct.padded_inside _ _ zero (le_congr (.eqRefl one) len.eqSymm (le_refl one))).eqTrans
      (GaussianRationalMonicReduction.singleton_lookup a))
theorem monomial_constant (a : PTm n) : Γ ⊢[PRAAx] entry (monomial a) one ≐ qzero := by
  have len := GaussianRationalMonicReduction.singleton_length (Γ := Γ) a
  exact (GaussianRationalPolynomialBuffers.append_lookup _ one
    (le_congr (.eqRefl _) len.eqSymm (le_refl one))).eqTrans
      (GaussianRationalLinearProduct.padded_outside _ _ one (le_congr len.eqSymm (.eqRefl _) (le_refl one)))
theorem monomial_evaluation (a z : PTm n) : Γ ⊢[PRAAx] evaluate (monomial a) z ≐ qmul a z :=
  (GaussianRationalPolynomialBuffers.append_evaluation _ z).eqTrans
    ((qmul_congr (GaussianRationalMonicReduction.singleton_evaluation a z) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticCoefficientValues.qmul_recode_left a z))

theorem monomial_mass (a R : PTm n) : Γ ⊢[PRAAx]
    weightedNorm (monomial a) one (radiusPoint R one) ≐ qL1 (qmul a (power (radiusPoint R one) one)) := by
  let C := dilated (monomial a) one (radiusPoint R one)
  have leading : Γ ⊢[PRAAx] entry C zero ≐ qmul a (power (radiusPoint R one) one) :=
    (GaussianRationalPolynomialDilation.dilated_lookup _ _ _ _ (zero_le one)).eqTrans
      (qmul_congr (monomial_leading a) (congrAp2 GaussianRationalReciprocal.powerF (monus_zero one) (.eqRefl _)))
  have constant : Γ ⊢[PRAAx] entry C one ≐ qzero :=
    (GaussianRationalPolynomialDilation.dilated_lookup _ _ _ _ (le_refl one)).eqTrans
      ((qmul_congr (monomial_constant a) (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _))
  have last : Γ ⊢[PRAAx] GaussianCoefficientL1.coefficientNorm C ≐ prefixNorm C one :=
    (GaussianRationalLinearProduct.norm_length C (succ one)
      (GaussianRationalPolynomialDilation.dilated_length (monomial a) one (radiusPoint R one))).eqTrans
      ((GaussianCoefficientL1.prefix_succ _ one).eqTrans
        ((RationalAlgebra.add_congr (.eqRefl _)
          ((GaussianCoefficientL1.qL1_congr constant).eqTrans GaussianRationalLinearProduct.qzero_norm)).eqTrans
            (GaussianRationalLinearProduct.scalar_add_zero _ (RationalFiniteSum.sum_well_formed _ _ _))))
  exact last.eqTrans ((GaussianCoefficientL1.prefix_succ _ zero).eqTrans
    ((RationalAlgebra.add_congr ((GaussianCoefficientL1.prefix_zero C).eqTrans GaussianRationalLinearProduct.scalar_zero_code.eqSymm)
      (GaussianCoefficientL1.qL1_congr leading)).eqTrans
        (GaussianRationalLinearProduct.scalar_zero_add _ (GaussianRationalL1.qL1_guard _))))

theorem monomial_weighted_bound (a R : PTm n) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (monomial a) one (radiusPoint R one))
      (RationalArithmetic.multiply (qL1 a) (natCode R)) := by
  have radius := (GaussianFiniteLogarithmWeightedNorm.radius_power_norm (Γ := Γ) R one one (le_refl one)).eqTrans
    (RationalNonnegativePowers.fraction_congr (pw_one R) (pw_one one))
  exact RationalArgmin.rationalLE_congr (monomial_mass a R).eqSymm
    (RationalAlgebra.multiply_congr (.eqRefl _) radius) (GaussianRationalL1Algebra.qL1_multiply a _)

theorem polynomial_weighted_bound (q N R : PTm n) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (polynomial q N) one (radiusPoint R one)) (natCode (R*succ N)) := by
  have scale := GaussianFiniteExponentialWeightedNorm.multiply_bounds (Γ := Γ)
    (qL1 (coefficient q N)) (natCode R) (natCode (succ N)) (natCode R)
    (GaussianRationalSyntheticBounds.natCode_nonnegative R) (GaussianRationalSyntheticBounds.natCode_nonnegative _)
    (coefficient_norm q N) (RationalArgmin.reflexive _)
  have budget := (GaussianRationalSyntheticBounds.natCode_multiply (Γ := Γ) (succ N) R).eqTrans
    (GaussianPositiveExponentialMajorant.natCode_congr (show Γ ⊢[PRAAx] succ N*R ≐ R*succ N by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) budget
    (RationalArgmin.transitive (monomial_weighted_bound (coefficient q N) R) scale)

theorem original_linear_polynomial_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (polynomial (var 0) (var 1)) (var 2) ≐ qmul (coefficient (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (monomial_evaluation _ _)
theorem original_linear_polynomial_weighted_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rationalLE (weightedNorm (polynomial (var 0) (var 1)) one (radiusPoint (var 2) one)) (natCode (var 2*succ (var 1)))) :=
  closeUniv 3 (polynomial_weighted_bound _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaLinearCoefficient
