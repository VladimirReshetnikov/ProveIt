import IPRADerivations.Analysis.GaussianBinetSineKernelCommonClock
import IPRADerivations.Analysis.GaussianBinetSineStripCut

/-!
# Bound each original weighted column on the positive frequency grid

Use the original complex damping at the unchanged frequency and
rectangle clock. The same floor cut that removed its low-frequency
prefix supplies the physical margin for the real damped sine transform.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineKernelFrequency

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetOscillatoryColumns (damping)
open GaussianBinetSineKernelCommonClock (value cost)
open GaussianBinetSineStripCut (cutoff remaining_margin)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem damping_bound (p j X Y D sign R S N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] bounded (damping p X Y D sign S j N R) two one := by
  let r := p+N
  have time : Γ ⊢[PRAAx] le (S*j) (S*N) :=
    le_congr (mul_comm j S) (mul_comm N S) (mul_le_mul_right S hj)
  have radius := GaussianBinetLaplaceExponential.exponent_bound X Y D sign R S (S*j) N hz hN time
  exact GaussianBinetExponentialPanel.unit_bound r _ (R*S)
    (GaussianSignedNameExponentialOrder.constant_input _ _ radius)
    (GaussianBinetLaplaceExponential.exponent_nonpositive X Y D sign (S*j) N hz.andE₁.andE₂ hN)

theorem frequency_error (j p s k i I X Y D sign R S N T M E : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hi : Γ ⊢[PRAAx] le one i) (hI : Γ ⊢[PRAAx] le i I)
    (hS : Γ ⊢[PRAAx] le one S) (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hmin : Γ ⊢[PRAAx] le (two*(S*E)) N)
    (hj : Γ ⊢[PRAAx] le (cutoff N S E) j) (hmax : Γ ⊢[PRAAx] le j N)
    (hT : Γ ⊢[PRAAx] le T p) (hp : Γ ⊢[PRAAx] le p (s+N))
    (hM : Γ ⊢[PRAAx] le ((num 10*I+S)*T) M) (hP : Γ ⊢[PRAAx] le (unit p) M) :
    let d := damping s X Y D sign S j N R
    let G := two*E
    Γ ⊢[PRAAx] distanceBounded (qmul d (value (s+N) k i (S*j) N S T M))
      (qmul d (GaussianBinetKernelRows.value k i (S*j) N))
      (two*(cost I N G S T*unit T+num 40*G*unit p)) (unit p*unit T) := by
  let G := two*E
  let d := damping s X Y D sign S j N R
  have cut := remaining_margin j N S E hS hE hmin hj
  have freq := positive_product _ _ hS cut.andE₁
  have hi' : Γ ⊢[PRAAx] le N (G*(S*j)) := le_congr (.eqRefl _) (mul_comm _ _) cut.andE₂
  have hu : Γ ⊢[PRAAx] le (S*j) (S*N) :=
    le_congr (mul_comm j S) (mul_comm N S) (mul_le_mul_right S hmax)
  have rowRate := GaussianBinetSineKernelCommonClock.kernel_error p (s+N) k i I (S*j) N G S T M
    hi hI freq hN hi' hu hT hp hM hP
  exact GaussianApproximateInverseDistance.multiply_distance d _ _ two _ _ (positive_product _ _ (unit_positive p) (unit_positive T))
    (damping_bound s j X Y D sign R S N hz hN hmax) rowRate

local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def angularCost (I E S T : PTm n) : PTm n :=
  num 176*T+num 16*E*GaussianBinetExponentialIntegral.uniformCost (num 10*I+S) T

@[simp] theorem subst_angularCost {m : ℕ} (σ : Fin n → PTm m) (I E S T : PTm n) :
    Syn.subst σ (angularCost I E S T) =
      angularCost (Syn.subst σ I) (Syn.subst σ E) (Syn.subst σ S) (Syn.subst σ T) := by
  simp [angularCost,GaussianBinetExponentialIntegral.uniformCost,two]

theorem scheduled_frequency_error (j s k i I X Y D sign R S N T M E : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hi : Γ ⊢[PRAAx] le one i) (hI : Γ ⊢[PRAAx] le i I)
    (hS : Γ ⊢[PRAAx] le one S) (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hmin : Γ ⊢[PRAAx] le (two*(S*E)) N)
    (hj : Γ ⊢[PRAAx] le (cutoff N S E) j) (hmax : Γ ⊢[PRAAx] le j N)
    (hT : Γ ⊢[PRAAx] le T (s+N))
    (hM : Γ ⊢[PRAAx] le ((num 10*I+S)*T) M) (hP : Γ ⊢[PRAAx] le (unit (s+N)) M) :
    let d := damping s X Y D sign S j N R
    Γ ⊢[PRAAx] distanceBounded (qmul d (value (s+N) k i (S*j) N S T M))
      (qmul d (GaussianBinetKernelRows.value k i (S*j) N))
      (angularCost I E S T*unit T+num 160*E*unit s) (unit s*unit T) := by
  let r := s+N
  let W := unit s
  let P := unit r
  let V := unit T
  let C := GaussianBinetExponentialIntegral.uniformCost (num 10*I+S) T
  have hN' : Γ ⊢[PRAAx] le N (unit N) :=
    le_trans (le_succ_self N) (RationalClosure.succ_le_two_pow N)
  have hn : Γ ⊢[PRAAx] le (N*W) P :=
    le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (pw_add two s N).eqSymm) (mul_le_mul_right W hN')
  have hs : Γ ⊢[PRAAx] le W P := GaussianExponentialReference.unit_monotone (le_add_right s N)
  have raw := frequency_error j r s k i I X Y D sign R S N T M E hz hi hI hS hN hE
    hmin hj hmax hT (le_refl r) hM hP
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive r) (unit_positive T))
    (positive_product _ _ (unit_positive s) (unit_positive T)) ?_ raw
  dsimp only [cost,angularCost,r]
  ipra_le 𝔞(num 176*T*unit T*unit T)*sl hn+𝔞(num 16*E*C*unit T*unit T)*sl hs

end LeanProofs.IPRA.Analysis.GaussianBinetSineKernelFrequency
