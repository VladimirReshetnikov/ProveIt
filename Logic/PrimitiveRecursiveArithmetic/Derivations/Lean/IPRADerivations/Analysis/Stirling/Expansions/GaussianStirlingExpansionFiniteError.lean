import IPRADerivations.Analysis.Stirling.Expansions.GaussianStirlingExpansionCoefficients
import IPRADerivations.Analysis.Polynomials.Taylor.GaussianShrinkingPolynomialTail
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReference

/-!
# Finite truncation error of the Stirling exponential polynomial

Evaluate the actual Bernoulli log polynomial at y=b/a. The order-m
exponential Taylor polynomial in that value is exactly a polynomial
in y of degree m². Its computed coefficient norm gives a rational
upper bound on the error from keeping only the first m+1 coefficients.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingExpansionFiniteError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale normSq oneCode)
open GaussianCoefficientL1 (coefficientNorm)
open GaussianRationalHorner (evaluate ofGaussian ofGaussian_represents)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalPowerExpansion (partialSum)
open GaussianStirlingExpansionCoefficients (logTable expTable log_table_length)
open RationalArgmin (rationalLE)
open RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.PTm (num)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def query (a b : PTm n) : PTm n := ofGaussian (scale b oneCode) a
def logPolynomial (m : ℕ) (a b : PTm n) : PTm n := evaluate (logTable m) (query a b)
def finiteTaylor (m : ℕ) (a b : PTm n) : PTm n := scalarSum (logPolynomial m a b) (num m)
def approximation (m : ℕ) (a b : PTm n) : PTm n :=
  partialSum (expTable m) (num m*num m) (query a b) (succ (num m))

def errorNumerator (m : ℕ) (b : PTm n) : PTm n :=
  (numeratorOf (coefficientNorm (expTable m))).pos * pw b (succ (num m))
def errorDenominator (m : ℕ) (a : PTm n) : PTm n :=
  denominatorOf (coefficientNorm (expTable m)) * pw a (succ (num m))

theorem query_bound (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] bounded (query a b) b a := by
  refine GaussianRationalMetric.bounded_of_cleared _ (scale b oneCode) a b a ha ha
    (ofGaussian_represents _ _ ha) ?_
  exact le_congr (congrMul (.eqRefl _) (GaussianGammaGaussReference.scaled_one_norm b)).eqSymm
    (mul_comm (a*a) (b*b)) (le_refl _)

theorem norm_upper (c : PTm n) : Γ ⊢[PRAAx]
    rationalLE c (GaussianEuclideanDistanceName.fraction (numeratorOf c).pos (denominatorOf c)) := by
  let D := denominatorOf c
  let Z := numeratorOf c
  have hD : Γ ⊢[PRAAx] le one D := RationalArgmin.denominator_positive c
  apply RationalArithmetic.order_of_representations _ _ Z (ZT.ofNat Z.pos) D D
    (RationalRepresentations.represents_self c) (GaussianEuclideanDistanceName.fraction_represents _ _ hD) hD hD
  apply zle_of_toZ (Z.neg*D)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  ipra_simps
  ring

theorem exp_table_length (m : ℕ) : Γ ⊢[PRAAx] length (expTable m : PTm n) ≐ succ (num m*num m) :=
  GaussianRationalPolynomialExponential.polynomial_length _ _ _

private theorem degree_le (m : ℕ) : Γ ⊢[PRAAx] le (num m) (num m*num m) := by
  have h : m ≤ m*m := by
    cases m with
    | zero => simp
    | succ m => exact Nat.le_mul_of_pos_right _ (Nat.succ_pos m)
  exact le_congr (.eqRefl _) (by apply deriveNat; ipra_simps; push_cast; ring)
    (RationalPhiSharpQuintic.numeral_le _ _ h)

theorem finite_error (m : ℕ) (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hab : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] distanceBounded (finiteTaylor m a b) (approximation m a b)
      (errorNumerator m b) (errorDenominator m a) := by
  have h := GaussianShrinkingPolynomialTail.finite_coefficient_tail (expTable m) (num m*num m)
    (num m) (query a b) _ _ b a (exp_table_length m) (degree_le m)
    (RationalArgmin.denominator_positive _) ha hab (norm_upper (coefficientNorm (expTable m))) (query_bound a b ha)
  exact GaussianRationalDistanceOrder.distance_congr
    (GaussianRationalPolynomialExponential.polynomial_evaluation _ _ _ _ (log_table_length m))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) h

theorem actual_Stirling_finite_polynomial_error_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 0) ⟶ le (var 1) (var 0) ⟶ distanceBounded
        (finiteTaylor m (var 0) (var 1)) (approximation m (var 0) (var 1))
        (errorNumerator m (var 1)) (errorDenominator m (var 0))) :=
  closeUniv 2 (.impI (.impI (finite_error m _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingExpansionFiniteError
