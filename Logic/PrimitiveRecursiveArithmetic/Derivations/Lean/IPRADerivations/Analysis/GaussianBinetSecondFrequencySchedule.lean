import IPRADerivations.Analysis.GaussianBinetSecondEarlySchedule
import IPRADerivations.Analysis.GaussianBinetSineKernelFrequency
import IPRADerivations.Analysis.GaussianBinetLaplaceFrequencySuffix

/-!
# Independent frequency clocks for the second Binet formula

Increase the angular radius after choosing the physical frequency and
time horizons. This lets the angular grid refine the original first
Binet integral and pay the accumulated rounding error while preserving
the geometric cutoff and the positive interval being sampled.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondFrequencySchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentSineUniform
  (clock clock_budget count count_dominates cutoff cutoff_positive roundingCost)
open GaussianBinetExponentialIntegral (uniformCost)
open GaussianBinetLaplaceFrequencySuffix (meshBudget)
open GaussianBinetLaplaceOrderedPrefixes (width)
open GaussianBinetSecondEarlySchedule
  (angularAccuracy angular_count_at_least index seed seed_bounds stripDenominator timeHorizon)
open GaussianBinetSineKernelFrequency (angularCost)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def kernelClock (p S : PTm n) : PTm n := exponent (num 7*S) p

def laplaceClock (p D L : PTm n) : PTm n :=
  GaussianCompactRiemannName.precision p (width D L)+exponent (num 11*(D*L)) p

def extraRadius (p q I E D R T K : PTm n) : PTm n :=
  let L := cutoff q T K
  let S := D*L
  meshBudget p R D L+kernelClock p S+T+(I*S)*angularCost I E S T

def radius (p q I E D R T K : PTm n) : PTm n := R+extraRadius p q I E D R T K

theorem kernel_clock_budget (p S : PTm n) :
    Γ ⊢[PRAAx] le ((num 7*S)*unit p) (unit (kernelClock p S)) := query_budget _ _

theorem laplace_clock_budget (p D L : PTm n) :
    Γ ⊢[PRAAx] le (GaussianCompactRiemannName.precision p (width D L)) (laplaceClock p D L) ⋏
      le ((num 11*(D*L))*unit p) (unit (laplaceClock p D L)) :=
  .andI (le_add_right _ _) (le_trans (query_budget _ _)
    (GaussianExponentialReference.unit_monotone (le_add_left _ _)))

theorem count_budgets (p q I E X Y D sign R T K : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) :
    let L := cutoff q T K
    let A := radius p q I E D R T K
    let N := count q D A T K
    Γ ⊢[PRAAx] source X Y D sign A ⋏ (le (meshBudget p R D L) N ⋏
      (le (kernelClock p (D*L)) (clock q D A T K+N) ⋏ le T (clock q D A T K+N))) := by
  let L := cutoff q T K
  let S := D*L
  let A := radius p q I E D R T K
  let N := count q D A T K
  let s := clock q D A T K
  let H := extraRadius p q I E D R T K
  have grow := angular_count_at_least q X Y D sign R T K H h
  have more : Γ ⊢[PRAAx] le H (s+N) := le_trans grow.andE₂ (le_add_left N s)
  have mesh : Γ ⊢[PRAAx] le (meshBudget p R D L) H :=
    le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have kernel : Γ ⊢[PRAAx] le (kernelClock p S) H :=
    le_trans (le_add_left _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have time : Γ ⊢[PRAAx] le T H := le_trans (le_add_left _ _) (le_add_right _ _)
  exact .andI grow.andE₁ (.andI (le_trans mesh grow.andE₂)
    (.andI (le_trans kernel more) (le_trans time more)))

theorem angular_rounding_budget (p q I E D R T K : PTm n)
    (hp : Γ ⊢[PRAAx] le p q) (hD : Γ ⊢[PRAAx] le one D)
    (hT : Γ ⊢[PRAAx] le one T) (hK : Γ ⊢[PRAAx] le one K) :
    let S := D*cutoff q T K
    let A := radius p q I E D R T K
    Γ ⊢[PRAAx] le (((I*S)*angularCost I E S T)*unit p) (unit (clock q D A T K)) := by
  let S := D*cutoff q T K
  let C := (I*S)*angularCost I E S T
  let A := radius p q I E D R T K
  let J := (A+T)*S
  have hS : Γ ⊢[PRAAx] le one S := positive_product _ _ hD (cutoff_positive q T K)
  have cA : Γ ⊢[PRAAx] le C A := le_trans (le_add_left _ _) (le_add_left _ _)
  have aJ : Γ ⊢[PRAAx] le A J := le_congr (by ipra_ring) (.eqRefl J)
    (le_mul_mono (le_add_right A T) hS)
  have hJ : Γ ⊢[PRAAx] le one J := positive_product _ _ (le_trans hT (le_add_left T A)) hS
  have jcost : Γ ⊢[PRAAx] le J (uniformCost (A+T) S) := by
    change Γ ⊢[PRAAx] le J (num 10+two*(J*J)+two)
    ipra_le 12+𝔞(J)+2*𝔞(J)*sl hJ
  have widen : Γ ⊢[PRAAx] le (uniformCost (A+T) S) (T*K*uniformCost (A+T) S) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right _ (positive_product _ _ hT hK))
  have first : Γ ⊢[PRAAx] le (T*K*uniformCost (A+T) S) (roundingCost q D A T K S) :=
    le_trans (le_add_right _ _) (le_add_right _ _)
  exact le_trans (le_mul_mono (le_trans cA (le_trans aJ (le_trans jcost (le_trans widen first))))
    (GaussianExponentialReference.unit_monotone hp)) (clock_budget q D A T K)

theorem early_precision (p D K : PTm n) :
    Γ ⊢[PRAAx] le p (angularAccuracy p D K) ⋏ le (unit p) (stripDenominator p D K) := by
  let v := index p D K
  have pv : Γ ⊢[PRAAx] le p v := le_trans (le_add_right p (seed D K)) (le_add_right _ _)
  have eight : Γ ⊢[PRAAx] le v (num 8*v) := by ipra_le 7*𝔞(v)
  exact .andI (le_trans pv (le_trans eight (le_succ_self _)))
    (GaussianExponentialReference.unit_monotone (le_trans pv eight))

theorem far_time_budget (p D K : PTm n) :
    Γ ⊢[PRAAx] le ((two*K)*unit p) (timeHorizon p D K) := by
  let v := seed D K
  have limit : Γ ⊢[PRAAx] le (two*K) v := by
    have seed := (seed_bounds (Γ := Γ) D K).andE₁
    change Γ ⊢[PRAAx] le (two*K) (GaussianBinetSecondEarlySchedule.seed D K)
    ipra_le 64+6*𝔞(K)+sl seed
  have exp : Γ ⊢[PRAAx] le v (unit v) :=
    le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow _)
  have power : Γ ⊢[PRAAx] unit p*unit v ≐ unit (p+v) := (pw_add two p v).eqSymm
  have major := le_mul_mono (le_refl (unit p)) (le_trans limit exp)
  exact le_trans (le_congr (mul_comm _ _) power major)
    (GaussianExponentialReference.unit_monotone (le_add_right (p+v) (num 4)))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondFrequencySchedule
