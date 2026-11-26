import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.GaussianBinetArctangentPoleLaplace

/-!
# Finite two-exponential cosine transform

Cosine times the complex damping is evaluated as the half sum of the
actual Laplace exponentials at `z-it` and `z+it`. Both panel sums share
the same cutoff and time mesh. Their exact reciprocal average is the
integrand of the original arctangent quadrature.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentCosineLaplace

open_ipra
open GaussianBinetArctangentResolvent (pole reciprocal_average)
open GaussianBinetArctangentPoleLaplace (pole_integral_error)
open GaussianBinetExponentialIntegral (uniformCost)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product qadd qmul ofGaussian_represents)
open GaussianRationalMetric (bounded bounded_iff distanceBounded)
open GaussianRationalReciprocal (bounded_product bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "LV" => GaussianBinetExponentialIntegralGrid.value

def mean (a b : PTm n) : PTm n := qmul (fraction one two) (qadd a b)

def error (p R U K T L : PTm n) : PTm n :=
  K*uniformCost (R+U) T*unit L+K*num 5*unit p

def value (p X Y D sign A B R U L N : PTm n) : PTm n :=
  let T := D*L
  mean (LV (p+N) (GaussianRationalMetric.qnegative (pole false X Y D sign A B)) ((R+U)*T) T N)
    (LV (p+N) (GaussianRationalMetric.qnegative (pole true X Y D sign A B)) ((R+U)*T) T N)

ipra_subst mean [one, two]

ipra_subst error [uniformCost, LeanProofs.IPRA.PTm.subst_num, two]

ipra_subst value

private theorem half_bound : Γ ⊢[PRAAx] bounded (fraction one two : PTm n) one two := by
  let a := (ComplexLogarithmRemainder.scale one ComplexLogarithmRemainder.oneCode : PTm n)
  have ht := le_succ_self (Γ := Γ) one
  have e : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq a ≐ one*one :=
    (ComplexLogarithmRemainder.normSq_scale _ _).eqTrans ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  exact (bounded_iff _ _ _ _ _ ht ht (ofGaussian_represents a two ht)).iffMpr
    (le_congr (congrMul (.eqRefl (two*two)) e.eqSymm) (by ipra_ring) (le_refl ((two*two)*(one*one))))

theorem mean_distance (a b c d F H : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (h₁ : Γ ⊢[PRAAx] distanceBounded a c F H) (h₂ : Γ ⊢[PRAAx] distanceBounded b d F H) :
    Γ ⊢[PRAAx] distanceBounded (mean a b) (mean c d) F H := by
  have ht := le_succ_self (Γ := Γ) one
  have summed := GaussianNameArithmetic.sum_distance a c b d F F H hH h₁ h₂
  have scaled := bounded_product (fraction one two) _ one two (F+F) H ht hH half_bound summed
  have difference := bound_congr (GaussianRationalRoundedPower.multiplication_difference (fraction one two) _ _).eqSymm
    (.eqRefl _) (.eqRefl _) scaled
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ht hH) hH
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) difference

theorem finite_error (p X Y D sign A B R U K L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (hU : Γ ⊢[PRAAx] le A (U*B)) (hm : Γ ⊢[PRAAx] le D (K*X)) (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+U)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (value p X Y D sign A B R U L N)
      (GaussianBinetArctangentResolvent.value X Y D sign A B) (error p R U K (D*L) L) (unit p*unit L) := by
  have pErr := pole_integral_error false p X Y D sign A B R U K L N hz hB hU hm hL hN hpN
  have mErr := pole_integral_error true p X Y D sign A B R U K L N hz hB hU hm hL hN hpN
  exact distance_congr (.eqRefl _) (reciprocal_average X Y D sign A B hz.andE₁ hB).eqSymm (.eqRefl _) (.eqRefl _)
    (mean_distance _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive L)) pErr mErr)

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentCosineLaplace
