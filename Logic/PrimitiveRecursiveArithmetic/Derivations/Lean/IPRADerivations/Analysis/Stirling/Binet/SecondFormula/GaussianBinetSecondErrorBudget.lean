import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineKernels.GaussianBinetSineKernelFrequency
import IPRADerivations.Analysis.Stirling.Binet.Kernel.FrequencyGrids.GaussianBinetKernelFrequencyRadius
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceFrequencySuffix

/-!
# Common dyadic bounds for the finite second Binet comparisons
-/

set_option autoImplicit false
set_option maxHeartbeats 560000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondErrorBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetSineKernelFrequency (angularCost)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

theorem fit (a b A B C p : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (budget : Γ ⊢[PRAAx] le (A*unit p) (C*B)) (e : Γ ⊢[PRAAx] distanceBounded a b A B) :
    Γ ⊢[PRAAx] distanceBounded a b C (unit p) :=
  distance_radius_mono _ _ _ _ _ _ hB (unit_positive p) budget e

theorem double_distance (a b A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (e : Γ ⊢[PRAAx] distanceBounded a b A B) :
    Γ ⊢[PRAAx] distanceBounded (qmul (fraction two one) a) (qmul (fraction two one) b) (two*A) B :=
  GaussianApproximateInverseDistance.multiply_distance (GaussianRationalNaturalScale.naturalPoint two) a b
    two A B hB (GaussianNamedNaturalScale.natural_point_bound two) e

theorem angular_budget (p s I E S T : PTm n)
    (observation : Γ ⊢[PRAAx] le (((I*S)*angularCost I E S T)*unit p) (unit s))
    (tail : Γ ⊢[PRAAx] le (num 160*E*I*S*unit p) (unit T)) :
    Γ ⊢[PRAAx] le ((I*(S*(angularCost I E S T*unit T+num 160*E*unit s)))*unit p)
      (two*(unit s*unit T)) := by
  ipra_le 𝔞(unit T)*sl observation+𝔞(unit s)*sl tail

theorem kernel_budget (p r q I S : PTm n)
    (tail : Γ ⊢[PRAAx] le (two*S*unit p) I)
    (kernel : Γ ⊢[PRAAx] le ((num 7*S)*unit p) (unit r))
    (observation : Γ ⊢[PRAAx] le ((num 11*S)*unit p) (unit q)) :
    Γ ⊢[PRAAx] le ((S*GaussianBinetKernelFrequencyRadius.errorNumerator r q I)*unit p)
      (num 3*GaussianBinetKernelFrozenIndependent.errorDenominator r q I) := by
  unfold GaussianBinetKernelFrequencyRadius.errorNumerator GaussianBinetKernelFrozenIndependent.dampedNumerator
    GaussianBinetKernelFrozenIndependent.errorDenominator
  ipra_le 𝔞(unit r*unit q)*sl tail+𝔞(I*unit q)*sl kernel+𝔞(I*unit r)*sl observation

theorem laplace_budget (p X D L E : PTm n)
    (hX : Γ ⊢[PRAAx] le one X) (far : Γ ⊢[PRAAx] le (D*unit p) (unit L))
    (near : Γ ⊢[PRAAx] le (unit p) E) :
    Γ ⊢[PRAAx] le (GaussianBinetLaplaceFrequencySuffix.errorNumerator p p X D L E*unit p)
      (num 10*GaussianBinetLaplaceFrequencySuffix.errorDenominator p p X L E) := by
  let C := GaussianBinetLaplaceFrequencySuffix.tailDenominator X L
  let U := unit p
  have pCX : Γ ⊢[PRAAx] le one (num 12*X) :=
    positive_product _ _ (by ipra_le 11) hX
  have far' : Γ ⊢[PRAAx] le (D*U) C :=
    le_trans far (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit L) pCX))
  have near' : Γ ⊢[PRAAx] le U (two*E) := by
    ipra_le 𝔞(E)+sl near
  change Γ ⊢[PRAAx] le (((D*U*U+C*(U+U)+num 6*C*U)*(two*E)+C*U*U)*U)
    (num 10*((C*U*U)*(two*E)))
  ipra_le 𝔞(U*U*(two*E))*sl far'+𝔞(C*U*U)*sl near'

end LeanProofs.IPRA.Analysis.GaussianBinetSecondErrorBudget
