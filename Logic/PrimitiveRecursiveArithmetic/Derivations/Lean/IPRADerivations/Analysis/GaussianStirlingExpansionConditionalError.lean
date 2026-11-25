import IPRADerivations.Analysis.GaussianStirlingExpansionExponentialError
import IPRADerivations.Analysis.GaussianStirlingMultiplicative
import IPRADerivations.Analysis.GaussianNamedRateTransport

/-!
# Error transport from a logarithmic Stirling truncation to the native quotient

A logarithmic error coefficient C gives a uniform exponential disk and
an explicit error coefficient for the fixed-order polynomial in 1/x.
The output uses the actual normalized Gamma quotient, the computed
Stirling coefficients, and the original name's observation clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingExpansionConditionalError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianNameBounds (U)
open GaussianNameEquivalence (cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianStirlingExpansionExponentialError (logBudget TaylorBudget expansionNumerator expansionDenominator
  exponential_error log_polynomial_bound)
open GaussianStirlingExpansionFiniteError (logPolynomial approximation)
open GaussianStirlingMultiplicative (quotientF quotientData expRemainderF expRemainderData multiplicative_formula)
open GaussianStirlingMultiplicativeAlgebra (remainderF remainderData remainder_regular)
open GaussianStirlingNames (source)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "expF" => GaussianRadiusExponentialName.nameF
local notation "expData" => GaussianRadiusExponentialName.data
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def logRate (m : ℕ) (a b x C : PTm n) : Fm PTm n :=
  independentRate remainderF constantF (remainderData a b x) (logPolynomial m a b)
    (C*pw b (succ (num m))) (pw a (succ (num m)))

def radius (m : ℕ) (C : PTm n) : PTm n := logBudget m+C+two
def budget (m : ℕ) (C : PTm n) : PTm n := factor (radius m C)*C+TaylorBudget m
def numerator (m : ℕ) (p a b C : PTm n) : PTm n :=
  budget m C*pw b (succ (num m))*unit p+num 4*pw a (succ (num m))

private theorem from_constant_at (F : PR 2) (x q H A D C p : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (hA : Γ ⊢[PRAAx] le A (C*D))
    (h : Γ ⊢[PRAAx] independentRate F constantF x q A D) (hq : Γ ⊢[PRAAx] bounded q H one) :
    Γ ⊢[PRAAx] bounded (ap2 F p x) (H+C+two) one := by
  have Upos := unit_positive (Γ := Γ) p
  have base := distance_congr (.eqRefl _) (constant_at p q) (.eqRefl _) (.eqRefl _)
    (diagonal_rate F constantF x q A D p hd h)
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 F p x) q (C+two) one :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hd Upos) (le_refl one)
      (by ipra_le 𝔞 (unit p)*sl hA+2*𝔞 D*sl Upos) base
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) near hq)

private theorem from_constant (F : PR 2) (x q H A D C : PTm n) (reg : Γ ⊢[PRAAx] pointCN F x)
    (hd : Γ ⊢[PRAAx] le one D) (hA : Γ ⊢[PRAAx] le A (C*D))
    (h : Γ ⊢[PRAAx] independentRate F constantF x q A D) (hq : Γ ⊢[PRAAx] bounded q H one) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input F (H+C+two) x := by
  refine .andI reg (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] independentRate F constantF (sh x) (sh q) (sh A) (sh D) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift
  have hp : Γ.map Fm.shift ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,one] using hd.shift
  have hr : Γ.map Fm.shift ⊢[PRAAx] le (sh A) (sh C*sh D) := by simpa [Fm.shift,Syn.shift,sh] using hA.shift
  have bq : Γ.map Fm.shift ⊢[PRAAx] bounded (sh q) (sh H) one := by simpa [Fm.shift,Syn.shift,sh,one] using hq.shift
  simpa [GaussianRadiusExponentialName.boundedSamples,Syn.shift,sh,two] using
    from_constant_at F (sh x) (sh q) (sh H) (sh A) (sh D) (sh C) (var 0) hp hr hs bq

theorem original_approximation (m : ℕ) (p a b x C : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hab : Γ ⊢[PRAAx] le b a) (hsmall : Γ ⊢[PRAAx] le (two*(logBudget m*b)) a)
    (h : Γ ⊢[PRAAx] logRate m a b x C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 quotientF p (quotientData a b x)) (approximation m a b)
      (numerator m p a b C) (expansionDenominator m p a) := by
  let d := succ (num m : PTm n)
  let D := pw a d
  let A := C*pw b d
  let H := logBudget (n := n) m
  let R := radius m C
  let X := remainderData a b x
  let Q := logPolynomial m a b
  have hp := unit_positive (Γ := Γ) p
  have hd : Γ ⊢[PRAAx] le one D := GaussianFactorBudget.power_positive a d hs.andE₁
  have hBound := log_polynomial_bound m a b hs.andE₁ hab
  have hQ : Γ ⊢[PRAAx] bounded Q H one := by
    apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hs.andE₁ (le_refl one) ?_ hBound
    ipra_le 𝔞 H*sl hab
  have inp : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input remainderF R X :=
    from_constant _ _ Q H A D C (remainder_regular a b x hs) hd
      (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right C (pw_le_pw d hab))) h hQ
  have hQ' : Γ ⊢[PRAAx] bounded Q R one := by
    apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) ?_ hQ
    unfold R radius
    ipra_le 𝔞 C+2
  have hQ₁ : Γ ⊢[PRAAx] bounded Q one one := by
    apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hs.andE₁ (le_refl one) ?_ hBound
    have j : Γ ⊢[PRAAx] le (H*b) a :=
      le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right (H*b) (H*b))) hsmall
    exact le_congr (by ipra_ring) (one_mul _).eqSymm j
  have inQ := GaussianSignedNameExponentialOrder.constant_input Q R hQ'
  have inOne := GaussianSignedNameExponentialOrder.constant_input Q one hQ₁
  have rate := GaussianRadiusExponentialLipschitzRate.independent_rate remainderF constantF R X Q A D
    (.andI hd (.andI inp (.andI inQ h)))
  have old := GaussianExponentialRadiusIndependence.same_input_cross remainderF (U remainderF X) R X
    (exponential_input _ _ (remainder_regular a b x hs)) inp
  have l := cross_trans quotientF expRemainderF expRemainderF (quotientData a b x) (expRemainderData a b x)
    (expData R X) (cross_symm _ _ _ _ (multiplicative_formula a b x hs)) old
  have r := GaussianExponentialRadiusIndependence.same_input_cross constantF one R Q inOne inQ
  have transport := GaussianNamedRateTransport.transport expRemainderF (expF constantF) quotientF (expF constantF)
    (expData R X) (expData R Q) (quotientData a b x) (expData one Q) (factor R*A) D hd rate l r
  have first := diagonal_rate _ _ _ _ _ _ p hd transport
  have second := exponential_error m p a b hs.andE₁ hab hsmall
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp [numerator,budget,expansionNumerator,A,D,R]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (positive_product _ _ hd hp) first second)

theorem actual_Stirling_multiplicative_approximation_from_log_error_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 1) (var 2) ⟶ le (var 2) (var 1) ⟶ le (two*(logBudget m*var 2)) (var 1) ⟶
        logRate m (var 1) (var 2) (var 3) (var 4) ⟶
        distanceBounded (ap2 quotientF (var 0) (quotientData (var 1) (var 2) (var 3)))
          (approximation m (var 1) (var 2)) (numerator m (var 0) (var 1) (var 2) (var 4))
            (expansionDenominator m (var 0) (var 1))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (original_approximation m _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianStirlingExpansionConditionalError
