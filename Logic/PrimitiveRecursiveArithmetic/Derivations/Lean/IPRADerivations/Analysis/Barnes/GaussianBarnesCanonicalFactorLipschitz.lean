import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalFactor
import IPRADerivations.Analysis.Gamma.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.Euler.GaussianEulerNamedPowerScalingPowerFrozen
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate

/-!
# A common-disk Lipschitz bound for the original Barnes factor

Dividing both Gaussian inputs by the positive index divides their
distance by the same index. This factor cancels the factor of the
index in the exact power difference estimate. The correction
polynomial and its original exponential can then be compared at
independent observation clocks through the original named product.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFactorLipschitz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale)
open GaussianBarnesCanonicalFactor (source base powerValue correction exponentRadius exponentialF exponentialData cap nameF data)
open GaussianEulerNamedPowerScalingPowerFrozen (constant_bound multiply_same_denominator)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian represents ofGaussian_represents represents_rescale represents_congr positive_product)
open GaussianRationalMetric (distanceBounded bounded bounded_difference_iff)
open GaussianRootAlgebra (equal_refl)
open GaussianRationalSyntheticDivision (qone)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def gain (R k : PTm n) : PTm n := (two*R+two)*cap R k

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R k : PTm n) :
    Syn.subst σ (gain R k) = gain (Syn.subst σ R) (Syn.subst σ k) := by simp [gain,two]

theorem gain_mono (R k l : PTm n) (h : Γ ⊢[PRAAx] le k l) :
    Γ ⊢[PRAAx] le (gain R k) (gain R l) := by
  have hp := GaussianFactorBudget.power_monotone_length (R+one) k l (le_add_left one R) h
  unfold gain cap
  ipra_le 𝔞(two*R+two)*𝔞(factor (exponentRadius R))*sl hp

theorem scaled_fraction_distance (z w B D k A N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A N) :
    Γ ⊢[PRAAx] distanceBounded (ofGaussian z (B*k)) (ofGaussian w (D*k)) A (N*k) := by
  let E := B*D
  let u := scale D z
  let v := scale B w
  have hE := positive_product B D hB hD
  have hEk := positive_product E k hE hk
  have hNk := positive_product N k hN hk
  have lu := represents_rescale (ofGaussian z B) z B D (ofGaussian_represents z B hB)
  have lv := represents_congr (.eqRefl _) (equal_refl v) (mul_comm D B)
    (represents_rescale (ofGaussian w D) w D B (ofGaussian_represents w D hD))
  have old := (bounded_difference_iff (ofGaussian z B) (ofGaussian w D) u v E A N hE hN lu lv).iffMp h
  have bk := positive_product B k hB hk
  have dk := positive_product D k hD hk
  have nu : Γ ⊢[PRAAx] represents (ofGaussian z (B*k)) u (E*k) :=
    represents_congr (.eqRefl _) (equal_refl u) (by dsimp only [E]; ipra_ring)
    (represents_rescale (ofGaussian z (B*k)) z (B*k) D (ofGaussian_represents z (B*k) bk))
  have nv : Γ ⊢[PRAAx] represents (ofGaussian w (D*k)) v (E*k) :=
    represents_congr (.eqRefl _) (equal_refl v) (by dsimp only [E]; ipra_ring)
    (represents_rescale (ofGaussian w (D*k)) w (D*k) B (ofGaussian_represents w (D*k) dk))
  apply (bounded_difference_iff _ _ u v (E*k) A (N*k) hEk hNk nu nv).iffMpr
  ipra_le 𝔞(k*k)*sl old

theorem power_distance (z w R B D k A N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B k) (hw : Γ ⊢[PRAAx] source w R D k)
    (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A N) :
    Γ ⊢[PRAAx] distanceBounded (powerValue z B k) (powerValue w D k) (pw (R+one) k*A) N := by
  let q := ofGaussian z (B*k)
  let r := ofGaussian w (D*k)
  let C := R+one
  have hk := hz.andE₂.andE₁
  have hNk := positive_product N k hN hk
  have scaled := scaled_fraction_distance z w B D k A N hz.andE₁ hw.andE₁ hk hN h
  have base_dist : Γ ⊢[PRAAx] distanceBounded (base z B k) (base w D k) A (N*k) :=
    distance_congr (.eqRefl _) (.eqRefl _) (zero_add A) (.eqRefl _)
      (GaussianNameArithmetic.sum_distance qone qone q r zero A (N*k) hNk
        (GaussianRationalPowerDifference.distance_refl_zero qone (N*k) hNk) scaled)
  have raw := GaussianRationalPowerDifference.power_distance_bound (base z B k) (base w D k) C A (N*k) k hNk
    (GaussianBarnesCanonicalFactor.base_bound z R B k hz) (GaussianBarnesCanonicalFactor.base_bound w R D k hw) base_dist
  have ep := (AnalyticNumberTheory.PNTStageStep.pos_of_one_le hk).eqSymm
  have grow := GaussianFactorBudget.power_monotone_length C (pred k) k (le_add_left one R)
    (le_congr (.eqRefl _) ep (le_succ_self (pred k)))
  refine distance_radius_mono _ _ _ _ _ _ hNk hN ?_ raw
  unfold GaussianRationalPowerDifference.budget
  ipra_le 𝔞(A*N*k)*sl grow

private theorem correction_fraction_bound (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (ofGaussian z (two*(B*k))) R one := by
  have order : Γ ⊢[PRAAx] le B (two*(B*k)) := by ipra_le 2*𝔞 B*sl h.andE₂.andE₁+𝔞 B
  have disk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*(two*(B*k))) :=
    ComplexLogarithmRemainder.bounded_mono h.andE₂.andE₂ (by ipra_le 𝔞 R*sl order)
  exact GaussianGammaEulerHead.fraction_disk z R (two*(B*k)) (le_trans h.andE₁ order) disk

theorem correction_distance (z w R B D k A N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B k) (hw : Γ ⊢[PRAAx] source w R D k)
    (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A N) :
    Γ ⊢[PRAAx] distanceBounded (correction z B k) (correction w D k) ((two*R+one)*A) N := by
  let a := ofGaussian z B
  let b := ofGaussian w D
  let u := ofGaussian z (two*(B*k))
  let v := ofGaussian w (two*(D*k))
  have hk := hz.andE₂.andE₁
  have h2 := positive_product two k (le_succ_self one) hk
  have shrink := scaled_fraction_distance z w B D (two*k) A N hz.andE₁ hw.andE₁ h2 hN h
  have ez := GaussianGammaEncodingRescaling.fraction_denominator_congr (Γ := Γ) z (B*(two*k)) (two*(B*k)) (by ipra_ring)
  have ew := GaussianGammaEncodingRescaling.fraction_denominator_congr (Γ := Γ) w (D*(two*k)) (two*(D*k)) (by ipra_ring)
  have dist : Γ ⊢[PRAAx] distanceBounded u v A N :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hN h2) hN (by ipra_le 𝔞(A*N)*sl h2)
      (distance_congr ez ew (.eqRefl _) (.eqRefl _) shrink)
  have prod := GaussianNameArithmetic.product_distance a b u v A A N R R hN h dist
    (correction_fraction_bound z R B k hz) (GaussianGammaEulerHead.fraction_disk w R D hw.andE₁ hw.andE₂.andE₂)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hN prod h)

private theorem exponential_sample_bound (p z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (ap2 exponentialF p (exponentialData z R B k)) (factor (exponentRadius R)) one := by
  let S := exponentRadius R
  let x := correction z B k
  have ht := GaussianBarnesCanonicalFactor.exponential_input z R B k h
  have qb := GaussianRadiusExponentialName.query_bound constantF S x p ht
  have e := GaussianPositiveExponentialMajorant.disk_bound (GaussianRadiusExponentialName.query constantF S p x) S
    (GaussianRadiusExponentialName.index S p) qb
  exact GaussianRationalReciprocal.bound_congr (GaussianRadiusExponentialName.sample_at constantF S p x).eqSymm (.eqRefl _) (.eqRefl _) e

private theorem exponential_bound (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound exponentialF (exponentialData z R B k) (factor (exponentRadius R)) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh k) := by
    simpa only [Fm.shift,Syn.shift,sh,GaussianBarnesCanonicalFactor.subst_source] using h.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,sh,GaussianBarnesCanonicalFactor.subst_exponentialData,
    GaussianRadiusExponentialLipschitzRate.subst_factor,exponentRadius,PTm.subst_add,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    exponential_sample_bound (var 0) (sh z) (sh R) (sh B) (sh k) hs

theorem independent_rate (z w R B D k A N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B k) (hw : Γ ⊢[PRAAx] source w R D k)
    (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A N) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data z R B k) (data w R D k) (gain R k*A) N := by
  let X := powerValue z B k
  let Y := powerValue w D k
  let P := pw (R+one) k
  let E := exponentRadius R
  let C := factor E
  let S := (two*R+one)*A
  let d := exponentialData z R B k
  let e := exponentialData w R D k
  have hzE := GaussianBarnesCanonicalFactor.exponential_input z R B k hz
  have hwE := GaussianBarnesCanonicalFactor.exponential_input w R D k hw
  have hP := GaussianNamedAddRate.constant_rate X Y (P*A) N hN (power_distance z w R B D k A N hz hw hN h)
  have hC := GaussianNamedAddRate.constant_rate (correction z B k) (correction w D k) S N hN
    (correction_distance z w R B D k A N hz hw hN h)
  have ERate := GaussianRadiusExponentialLipschitzRate.independent_rate constantF constantF E
    (correction z B k) (correction w D k) S N (.andI hN (.andI hzE (.andI hwE hC)))
  have wBound := GaussianRationalPowerDifference.bounded_power_integer (base w D k) (R+one) k
    (GaussianBarnesCanonicalFactor.base_bound w R D k hw)
  have raw := multiply_same_denominator constantF exponentialF constantF exponentialF X d Y e
    (P*A) (C*S) N C P hN (constant_regular X) (GaussianRadiusExponentialName.name_regular _ _ _ hzE)
    (constant_regular Y) (GaussianRadiusExponentialName.name_regular _ _ _ hwE)
    (exponential_bound z R B k hz) (constant_bound Y P wBound) hP ERate
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (by dsimp only [P,C,S,E,gain,cap]; ipra_ring) (.eqRefl _) raw

theorem actual_Barnes_factor_common_disk_lipschitz_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 0) (var 2) (var 3) (var 5) ⟶ source (var 1) (var 2) (var 4) (var 5) ⟶
        le one (var 7) ⟶ distanceBounded (ofGaussian (var 0) (var 3)) (ofGaussian (var 1) (var 4)) (var 6) (var 7) ⟶
        independentRate nameF nameF (data (var 0) (var 2) (var 3) (var 5)) (data (var 1) (var 2) (var 4) (var 5))
          (gain (var 2) (var 5)*var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (independent_rate _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFactorLipschitz
