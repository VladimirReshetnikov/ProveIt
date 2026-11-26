import IPRADerivations.Analysis.GaussianGammaZetaDirichletParameterRate
import IPRADerivations.Analysis.GaussianGammaZetaDirichletUniformBound
import IPRADerivations.Analysis.GaussianGammaZetaDirichletProduct
import IPRADerivations.Analysis.GaussianEulerIntegralUpperBound
import IPRADerivations.Analysis.GaussianGammaHalfPlaneInputContinuity
import IPRADerivations.Analysis.GaussianEulerNamedPowerScalingPowerFrozen

/-!
# Effective parameter continuity of the original Gamma–Dirichlet product

The fixed disk and real-part margin bound both factors. A common output
precision pays for multiplication, and the two underlying input demands
give a single clock for the unchanged rational product.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletProductParameterRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerIntegralGammaIdentification (source)
open GaussianEulerIntegralUpperTransfer (paperConstant)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaZetaDirichletProduct (actualGammaData)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (bounded distanceBounded)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Z" => GaussianGammaZetaDirichletCofinal.nameF
local notation "zd" => GaussianGammaZetaDirichletCofinal.data
local notation "P" => GaussianGammaZetaDirichletProduct.nameF
local notation "pd" => GaussianGammaZetaDirichletProduct.data
local notation "zetaCap" => GaussianGammaZetaDirichletUniformBound.cap
local notation "zetaDemand" => GaussianGammaZetaDirichletParameterRate.demand
local notation "gammaDemand" => GaussianGammaHalfPlaneInputContinuity.modulus

def gammaCap (R A : PTm n) : PTm n := paperConstant A (R+one)+one

def pay (s R A : PTm n) : PTm n := exponent (gammaCap R A+zetaCap A) s

def demand (s R A : PTm n) : PTm n :=
  zetaDemand (pay s R A) R A+gammaDemand (pay s R A) (R+one) A

@[simp] theorem subst_gammaCap {m : ℕ} (σ : Fin n → PTm m) (R A : PTm n) :
    Syn.subst σ (gammaCap R A) = gammaCap (Syn.subst σ R) (Syn.subst σ A) := by
  simp [gammaCap,one]

@[simp] theorem subst_demand {m : ℕ} (σ : Fin n → PTm m) (s R A : PTm n) :
    Syn.subst σ (demand s R A) = demand (Syn.subst σ s) (Syn.subst σ R) (Syn.subst σ A) := by
  simp [demand,pay,one]

private theorem gamma_bound (p z R B A : PTm n) (hz : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] bounded (ap2 gammaF p (actualGammaData z R B A)) (gammaCap R A) one := by
  have h := GaussianGammaZetaDirichletPowerOrder.shifted_source z R B A hz
  have b := GaussianEulerIntegralUpperBound.original_gamma_bound p (shifted z B) (R+one) B A h
  exact bounded_radius_mono _ _ _ _ _ (unit_positive p) (le_refl one)
    (by unfold gammaCap; ipra_le sl (unit_positive (Γ := Γ) p)) b

theorem gamma_samples (z R B A : PTm n) (hz : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] sampleBound gammaF (actualGammaData z R B A) (gammaCap R A) := by
  let sh (x : PTm n) := Syn.shift x
  have h : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) := by
    simpa [Fm.shift,Syn.shift,sh] using hz.shift
  refine .allI ?_
  simpa only [sampleBound,GaussianGammaZetaDirichletProduct.subst_actualGammaData,subst_gammaCap,Syn.shift,sh] using
    gamma_bound (var 0) (sh z) (sh R) (sh B) (sh A) h

theorem gamma_rate (s z w R B D A : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B A) (hw : Γ ⊢[PRAAx] source w R D A)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (gammaDemand s (R+one) A))) :
    Γ ⊢[PRAAx] independentRate gammaF gammaF (actualGammaData z R B A) (actualGammaData w R D A) one (unit s) := by
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have l : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift.shift
  have r : Δ ⊢[PRAAx] source (sh w) (sh R) (sh D) (sh A) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hw.shift.shift
  have hd : Δ ⊢[PRAAx] distanceBounded (ofGaussian (sh z) (sh B)) (ofGaussian (sh w) (sh D))
      one (unit (gammaDemand (sh s) (sh R+one) (sh A))) := by
    simpa [Fm.shift,Syn.shift,sh,Δ,one] using h.shift.shift
  have hs := GaussianGammaZetaParameterRates.shifted_distance (sh z) (sh w) (sh B) (sh D)
    one (unit (gammaDemand (sh s) (sh R+one) (sh A)))
    l.andE₁.andE₂.andE₁.andE₁ r.andE₁.andE₂.andE₁.andE₁ (unit_positive _) hd
  have left := GaussianGammaZetaDirichletPowerOrder.shifted_source (sh z) (sh R) (sh B) (sh A) l
  have right := GaussianGammaZetaDirichletPowerOrder.shifted_source (sh w) (sh R) (sh D) (sh A) r
  refine .allI (.allI ?_)
  simp only [GaussianGammaZetaDirichletProduct.subst_actualGammaData,
    GaussianCoefficientNameBounds.subst_unit,Syn.shift,one,PTm.subst_succ,PTm.subst_zero]
  simp only [actualGammaData]
  exact GaussianGammaHalfPlaneInputContinuity.original_gamma_observations (var 1) (var 0)
    (sh s) (shifted (sh z) (sh B)) (shifted (sh w) (sh D)) (sh R+one) (sh B) (sh D) (sh A) left right hs

private theorem lower_clock (x y k m : PTm n) (hm : Γ ⊢[PRAAx] le m k)
    (h : Γ ⊢[PRAAx] distanceBounded x y one (unit k)) :
    Γ ⊢[PRAAx] distanceBounded x y one (unit m) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive k) (unit_positive m)
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm (GaussianExponentialReference.unit_monotone hm)) h

theorem original_demand_rate (s z w R B D A : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B A) (hw : Γ ⊢[PRAAx] source w R D A)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (demand s R A))) :
    Γ ⊢[PRAAx] independentRate P P (pd z R B A) (pd w R D A) one (unit s) := by
  let t := pay s R A
  let m := zetaDemand t R A
  let k := gammaDemand t (R+one) A
  let x := zd z R B A
  let y := zd w R D A
  let u := actualGammaData z R B A
  let v := actualGammaData w R D A
  have hZ := lower_clock (ofGaussian z B) (ofGaussian w D) (demand s R A) m (le_add_right m k) hd
  have hG := lower_clock (ofGaussian z B) (ofGaussian w D) (demand s R A) k (le_add_left k m) hd
  have hzs := GaussianGammaZetaDirichletPowerOrder.shifted_source z R B A hz
  have hws := GaussianGammaZetaDirichletPowerOrder.shifted_source w R D A hw
  have zeta := GaussianGammaZetaDirichletParameterRate.original_demand_rate t z w R B D A hz hw hZ
  have gamma := gamma_rate t z w R B D A hz hw hG
  have both := GaussianEulerNamedPowerScalingPowerFrozen.multiply_same_denominator Z gammaF Z gammaF
    x u y v one one (unit t) (gammaCap R A) (zetaCap A) (unit_positive t)
    (GaussianGammaZetaDirichletCofinal.regular z R B A hz)
    (GaussianEulerIntegralGammaIdentification.original_gamma_regular _ _ _ _ hzs)
    (GaussianGammaZetaDirichletCofinal.regular w R D A hw)
    (GaussianEulerIntegralGammaIdentification.original_gamma_regular _ _ _ _ hws)
    (gamma_samples z R B A hz) (GaussianGammaZetaDirichletUniformBound.samples w R D A hw) zeta gamma
  have target : Γ ⊢[PRAAx] le ((gammaCap R A+zetaCap A)*unit s) (unit t) := query_budget _ _
  exact GaussianNamedRateRadius.weaken P P (pd z R B A) (pd w R D A)
    (gammaCap R A*one+zetaCap A*one) (unit t) one (unit s) (unit_positive t) (unit_positive s)
    (le_congr (by ipra_ring) (one_mul _).eqSymm target) both

theorem actual_original_Gamma_Dirichlet_product_parameter_demand_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source (var 1) (var 3) (var 4) (var 6) ⟶ source (var 2) (var 3) (var 5) (var 6) ⟶
        distanceBounded (ofGaussian (var 1) (var 4)) (ofGaussian (var 2) (var 5)) one
          (unit (demand (var 0) (var 3) (var 6))) ⟶
        independentRate P P (pd (var 1) (var 3) (var 4) (var 6)) (pd (var 2) (var 3) (var 5) (var 6))
          one (unit (var 0))) :=
  closeUniv 7 (.impI (.impI (.impI (original_demand_rate _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletProductParameterRate
