import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.FixedHorizons.GaussianBinetFixedHorizonPositiveMargin
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineDampedRetiming

/-!
# Compare the actual transposed sine column with the frozen kernel row

The raw column uses the sine rectangle's clock. The antiderivative
uses its own precision and mesh clock. Retiming costs an explicit
dyadic error independent of the mesh size. The endpoint term depends
on the positive frequency margin rather than the coded denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineKernelCommonClock

open_ipra
open GaussianBinetExponentialIntegral (uniformCost)
open GaussianBinetFixedHorizonSine (error)
open GaussianBinetSineFrozenPiTerm (realNumerator realDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def value (r k i A B U T M : PTm n) : PTm n :=
  qmul (fraction two one)
    (GaussianBinetSineDampedQuadrature.value r (realNumerator k i) (realDenominator k) A B U T M)

def cost (I B G U T : PTm n) : PTm n :=
  num 88*T*B+num 4*G*uniformCost (num 10*I+U) T

theorem kernel_error (p r k i I A B G U T M : PTm n)
    (hi : Γ ⊢[PRAAx] le one i) (hI : Γ ⊢[PRAAx] le i I)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hG : Γ ⊢[PRAAx] le B (G*A)) (hU : Γ ⊢[PRAAx] le A (U*B))
    (hT : Γ ⊢[PRAAx] le T p) (hr : Γ ⊢[PRAAx] le p r)
    (hM : Γ ⊢[PRAAx] le ((num 10*I+U)*T) M) (hP : Γ ⊢[PRAAx] le (unit p) M) :
    Γ ⊢[PRAAx] distanceBounded (value r k i A B U T M) (GaussianBinetKernelRows.value k i A B)
      (cost I B G U T*unit T+num 40*G*unit p) (unit p*unit T) := by
  let R := num 10*I
  let P := unit p
  let V := unit T
  let Q := unit (p+M)
  let H := P*V
  let E := error p R U one T T
  let C := num 56*T*B*V+num 4*G*E
  let F := num 32*T*B*V
  let a := value r k i A B U T M
  let b := value (p+M) k i A B U T M
  let c := GaussianBinetKernelRows.value k i A B
  have hP' := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) T
  have hH := positive_product _ _ hP' hV
  have hQ := unit_positive (Γ := Γ) (p+M)
  have hD := (GaussianBinetFixedHorizonFrozenRows.uniform_source k i I hi hI).andE₁.andE₂
  have hN := le_trans hP' hP
  have order : Γ ⊢[PRAAx] le p (p+M) := le_add_right _ _
  have raw := GaussianBinetSineDampedRetiming.quadrature_distance r (p+M) p
    (realNumerator k i) (realDenominator k) A B U T M hD hA hB hN hU hr order
  have scaled := GaussianApproximateInverseDistance.multiply_distance (fraction two one) _ _ two _ P hP'
    (GaussianBinetLaplaceScalarMajorant.fraction_norm two one (le_refl one)) raw
  have first : Γ ⊢[PRAAx] distanceBounded a b F H := by
    apply distance_radius_mono _ _ _ _ _ _ hP' hH ?_ scaled
    exact le_of_eq_add (d := ConciseIPRA.PTm.zero) (by dsimp only [F,H]; ipra_ring)
  have analytic := GaussianBinetFixedHorizonPositiveMargin.common_horizon_kernel_error p k i I A B G U T M
      hi hI hA hB hG hU hT hM hP
  have last : Γ ⊢[PRAAx] distanceBounded b c C H := by
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hQ hH) hH ?_ analytic
    have later := GaussianExponentialReference.unit_monotone order
    dsimp only [C,H,P,V,E,R,Q]
    ipra_le 𝔞(num 56*T*B*(unit p*unit T)*unit T)*sl later
  have sum := distance_triangle_same a b c F C H hH first last
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [F,C,V,P,E,R,cost,error]; ipra_ring) (.eqRefl _) sum

end LeanProofs.IPRA.Analysis.GaussianBinetSineKernelCommonClock
