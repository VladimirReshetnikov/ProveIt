import IPRADerivations.Analysis.GaussianStirlingExpansionFiniteError
import IPRADerivations.Analysis.GaussianNamedConstantExponentialSmallTail

/-!
# Error for exponentiating the actual finite Stirling log polynomial

The original Bernoulli log polynomial vanishes at zero, so its value
at y=b/a is at most H y for an explicit coefficient-norm numerator H.
For y small enough, combine the original named exponential's Taylor
tail with the exact finite polynomial truncation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingExpansionExponentialError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientL1 (coefficientNorm)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianRadiusExponentialName (sample)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalPowerExpansion (partialSum prefix_succ prefix_zero)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_left qzero_add qzero_canonical)
open GaussianStirlingExpansionCoefficients (logTable expTable log_table_length log_table_zero)
open GaussianStirlingExpansionFiniteError (query logPolynomial approximation finiteTaylor query_bound norm_upper
  errorNumerator errorDenominator finite_error)
open RationalSupMetric (numeratorOf denominatorOf)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def logBudget (m : ℕ) : PTm n := (numeratorOf (coefficientNorm (logTable m))).pos
def TaylorBudget (m : ℕ) : PTm n := two*pw (logBudget m) (succ (num m))+(numeratorOf (coefficientNorm (expTable m))).pos

private theorem constant_term_zero (m : ℕ) (z : PTm n) :
    Γ ⊢[PRAAx] partialSum (logTable m) (num m) z one ≐ qzero := by
  have h : Γ ⊢[PRAAx] GaussianOffDominantTerms.term (logTable m) (num m) z zero ≐ qzero := by
    have e : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.coefficient (logTable m) (num m) zero ≐ qzero :=
      (LeanProofs.IPRA.Foundations.SequenceComposition.entry_congr (.eqRefl _) (monus_zero _)).eqTrans
        (log_table_zero m)
    exact (qmul_congr e (.eqRefl _)).eqTrans (qmul_zero_left _)
  exact (prefix_succ _ _ _ _ (zero_le _)).eqTrans
    ((qadd_congr (prefix_zero _ _ _) h).eqTrans (qzero_add _ qzero_canonical))

theorem log_polynomial_bound (m : ℕ) (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] bounded (logPolynomial m a b) (logBudget m*b) a := by
  let V := coefficientNorm (logTable m : PTm n)
  let D := denominatorOf V
  let H := logBudget (n := n) m
  have dp := RationalArgmin.denominator_positive (Γ := Γ) V
  have h := GaussianShrinkingPolynomialTail.finite_coefficient_tail (logTable m) (num m) zero (query a b)
    (numeratorOf V).pos D b a (log_table_length m) (zero_le _) dp ha hab (norm_upper V) (query_bound a b ha)
  have d : Γ ⊢[PRAAx] le one (D*a) := positive_product _ _ dp ha
  have raw : Γ ⊢[PRAAx] distanceBounded (logPolynomial m a b) qzero (H*b) (D*a) :=
    distance_congr (.eqRefl _) (constant_term_zero m (query a b))
      (congrMul (.eqRefl _) (pw_one b)) (congrMul (.eqRefl _) (pw_one a)) h
  have cleared := (GaussianReconstructionRoots.distance_zero_iff _ _ _ d).andE₁.impE raw
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ d ha
    (by ipra_le 𝔞 (H*b*a)*sl dp) cleared

def expansionNumerator (m : ℕ) (p a b : PTm n) : PTm n :=
  TaylorBudget m*pw b (succ (num m))*unit p+two*pw a (succ (num m))
def expansionDenominator (m : ℕ) (p a : PTm n) : PTm n := pw a (succ (num m))*unit p

theorem exponential_error (m : ℕ) (p a b : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hab : Γ ⊢[PRAAx] le b a) (hsmall : Γ ⊢[PRAAx] le (two*(logBudget m*b)) a) :
    Γ ⊢[PRAAx] distanceBounded (sample constantF one p (logPolynomial m a b))
      (approximation m a b) (expansionNumerator m p a b) (expansionDenominator m p a) := by
  let d := succ (num m : PTm n)
  let D := pw a d
  let U := unit p
  let H := logBudget (n := n) m
  let Q := denominatorOf (coefficientNorm (expTable m : PTm n))
  let P := errorNumerator m b
  have hD : Γ ⊢[PRAAx] le one D := GaussianFactorBudget.power_positive a d ha
  have hU := unit_positive (Γ := Γ) p
  have hQ : Γ ⊢[PRAAx] le one Q := RationalArgmin.denominator_positive _
  have hP := log_polynomial_bound m a b ha hab
  have half := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ ha RationalAlgebra.two_positive
    (le_congr (mul_comm _ _) (one_mul a).eqSymm hsmall) hP
  have t := GaussianNamedConstantExponentialSmallTail.constant_error (logPolynomial m a b) (num m) p (H*b) a ha hP half
  have e : Γ ⊢[PRAAx] distanceBounded (finiteTaylor m a b) (approximation m a b) P D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hQ hD) hD
      (by change Γ ⊢[PRAAx] le (P*D) (P*(Q*D)); ipra_le 𝔞 P*𝔞 D*sl hQ) (finite_error m a b ha hab)
  have DU : Γ ⊢[PRAAx] le one (D*U) := positive_product _ _ hD hU
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ DU hD t e
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ DU hD) DU ?_ joined
  have fac := natEq (LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor.pw_mul_base (Γ := Γ) H b d)
  apply le_of_eq_add (d := zero)
  apply deriveNat
  dsimp only [expansionNumerator,expansionDenominator,GaussianNamedConstantExponentialSmallTail.errorNumerator,
    GaussianNamedConstantExponentialSmallTail.errorDenominator,TaylorBudget,P,errorNumerator]
  ipra_simps
  rw [fac]
  ring

theorem actual_Stirling_log_polynomial_exponential_error_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 1) ⟶ le (var 2) (var 1) ⟶ le (two*(logBudget m*var 2)) (var 1) ⟶
        distanceBounded (sample constantF one (var 0) (logPolynomial m (var 1) (var 2)))
          (approximation m (var 1) (var 2)) (expansionNumerator m (var 0) (var 1) (var 2))
            (expansionDenominator m (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (.impI (exponential_error m _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianStirlingExpansionExponentialError
