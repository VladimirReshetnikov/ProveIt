import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerHeadPolynomial
import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaExponentCoefficientPolynomial
import IPRADerivations.Analysis.Polynomials.GaussianWeightedPolynomialTail
import IPRADerivations.Analysis.Gamma.GaussianGammaC9Bound

/-!
# The original finite Gamma coefficient construction and C19 majorant

Actual coefficient convolution multiplies the original Euler polynomial
head by the actual factorial-weighted exponential coefficient buffer of
the original sampled gamma/harmonic/zeta exponent. Its weighted absolute
coefficient mass is bounded by the SAME original M_R, uniformly in the
coefficient sample precision and both numerical Taylor cutoffs. The
actual low-degree polynomial has the exact finite C19 geometric tail.
Infinite coefficient consistency and the limiting original P identity
are separate obligations, not premises or conclusions of this module.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteCoefficientPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul evaluate ofGaussian)
open GaussianRationalPolynomialDilation (weightedNorm)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianRationalSyntheticBounds (natCode)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalPowerExpansion (partialSum)
open GaussianGammaC9Bound (majorant)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def totalDegree (R L K : PTm n) : PTm n := succ (two*R)+K*degree L
def polynomial (q R L K : PTm n) : PTm n := GaussianRationalPolynomialProduct.product
  (GaussianGammaEulerHeadPolynomial.polynomial (two*R))
  (GaussianGammaExponentCoefficientPolynomial.exponential q R L K) (succ (two*R)) (K*degree L)
@[simp] theorem subst_totalDegree {m : ℕ} (σ : Fin n → PTm m) (R L K : PTm n) :
    Syn.subst σ (totalDegree R L K) = totalDegree (Syn.subst σ R) (Syn.subst σ L) (Syn.subst σ K) := by simp [totalDegree]
@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (q R L K : PTm n) :
    Syn.subst σ (polynomial q R L K) = polynomial (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ L) (Syn.subst σ K) := by simp [polynomial]

theorem exponential_length (q R L K : PTm n) : Γ ⊢[PRAAx]
    length (GaussianGammaExponentCoefficientPolynomial.exponential q R L K) ≐ succ (K*degree L) :=
  GaussianRationalPolynomialExponential.polynomial_length _ _ _
theorem polynomial_length (q R L K : PTm n) : Γ ⊢[PRAAx] length (polynomial q R L K) ≐ succ (totalDegree R L K) :=
  GaussianRationalPolynomialProduct.product_length _ _ _ _

theorem original_finite_evaluation (q z B R L K : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    evaluate (polynomial q R L K) (ofGaussian z B) ≐
      qmul (GaussianGammaEulerHead.head z B (two*R))
        (GaussianRationalPolynomialExponential.scalarSum
          (qadd (qmul (GaussianGammaLinearCoefficient.coefficient q (two*R)) (ofGaussian z B))
            (GaussianRationalFiniteSum.sum GaussianGammaZetaDegreeName.coefficientBody (succ L)
              (GaussianGammaZetaDegreeName.coefficientData q z B (two*R)))) K) :=
  (GaussianRationalPolynomialProduct.product_evaluation _ _ _ _ _
    (GaussianGammaEulerHeadPolynomial.polynomial_length _) (exponential_length q R L K)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr
        (GaussianGammaEulerHeadPolynomial.original_head_evaluation z B (two*R) hB)
        (GaussianGammaExponentCoefficientPolynomial.original_exponential_evaluation q z B R L K))

/-- The original M_R controls actual absolute coefficient mass, and not
only the norm of an evaluated polynomial. -/
theorem original_coefficient_mass (q R L K : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (polynomial q R L K) (totalDegree R L K) (radiusPoint R one)) (natCode (majorant R)) := by
  have first := GaussianRationalPolynomialDilation.weighted_product_bound (Γ := Γ)
    (GaussianGammaEulerHeadPolynomial.polynomial (two*R))
    (GaussianGammaExponentCoefficientPolynomial.exponential q R L K) (succ (two*R)) (K*degree L) (radiusPoint R one)
    (GaussianGammaEulerHeadPolynomial.polynomial_length _) (exponential_length q R L K)
  have second := GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _
    (GaussianFiniteExponentialWeightedNorm.weighted_nonnegative _ _ _)
    (GaussianRationalSyntheticBounds.natCode_nonnegative _)
    (GaussianGammaEulerHeadPolynomial.original_head_coefficient_mass R (two*R))
    (GaussianGammaExponentCoefficientPolynomial.exponential_coefficient_mass q R L K hR)
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    (GaussianRationalSyntheticBounds.natCode_multiply _ _) (RationalArgmin.transitive first second)

theorem original_finite_C19_tail (q R L K d w : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hd : Γ ⊢[PRAAx] le d (totalDegree R L K)) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (polynomial q R L K) (qmul (radiusPoint R one) w))
      (partialSum (polynomial q R L K) (totalDegree R L K) (qmul (radiusPoint R one) w) (succ d))
      (majorant R) (pw two (succ d)) :=
  GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _)
    (show Γ ⊢[PRAAx] one*pw two (succ d) ≐ pw two (succ d) by ipra_ring)
    (GaussianWeightedPolynomialTail.weighted_coefficient_tail _ _ _ _ _ _ _
      (polynomial_length q R L K) hd (le_refl one) (original_coefficient_mass q R L K hR) hw)

/-- Constructing on the larger source disk gives exactly the M_(2R)
numerator and 2^(-d-1) rate printed in original C19. -/
theorem original_two_radius_C19_tail (q R L K d w : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hd : Γ ⊢[PRAAx] le d (totalDegree (two*R) L K)) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (polynomial q (two*R) L K) (qmul (radiusPoint (two*R) one) w))
      (partialSum (polynomial q (two*R) L K) (totalDegree (two*R) L K) (qmul (radiusPoint (two*R) one) w) (succ d))
      (majorant (two*R)) (pw two (succ d)) :=
  original_finite_C19_tail q (two*R) L K d w
    (GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R hR) hd hw

def polynomialF : PR 4 := PTm.toPR (polynomial (var 0) (var 1) (var 2) (var 3))
theorem polynomial_program (q R L K : PTm n) : Γ ⊢[PRAAx]
    PTm.app polynomialF ![q,R,L,K] ≐ polynomial q R L K := by
  simpa [polynomialF] using toPR_eq (Γ := Γ) (polynomial (var 0) (var 1) (var 2) (var 3) : PTm 4) ![q,R,L,K]

theorem original_finite_Gamma_coefficient_mass_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ rationalLE
      (weightedNorm (polynomial (var 0) (var 1) (var 2) (var 3)) (totalDegree (var 1) (var 2) (var 3)) (radiusPoint (var 1) one))
      (natCode (majorant (var 1)))) :=
  closeUniv 4 (.impI (original_coefficient_mass _ _ _ _ Prf.hyp0))

theorem original_finite_Gamma_two_radius_C19_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ (le (var 4) (totalDegree (two*var 1) (var 2) (var 3)) ⟶
      (bounded (var 5) one two ⟶
        distanceBounded
          (evaluate (polynomial (var 0) (two*var 1) (var 2) (var 3)) (qmul (radiusPoint (two*var 1) one) (var 5)))
          (partialSum (polynomial (var 0) (two*var 1) (var 2) (var 3)) (totalDegree (two*var 1) (var 2) (var 3))
            (qmul (radiusPoint (two*var 1) one) (var 5)) (succ (var 4)))
          (majorant (two*var 1)) (pw two (succ (var 4)))))) :=
  closeUniv 6 (.impI (.impI (.impI (original_two_radius_C19_tail _ _ _ _ _ _
    Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem original_finite_Gamma_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app polynomialF ![var 0,var 1,var 2,var 3] ≐ polynomial (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (polynomial_program _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteCoefficientPolynomial
