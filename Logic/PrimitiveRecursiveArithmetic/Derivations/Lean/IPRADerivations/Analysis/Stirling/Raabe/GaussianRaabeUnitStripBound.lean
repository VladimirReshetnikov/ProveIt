import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeStirlingRemainder
import IPRADerivations.Analysis.Logarithm.GaussianCompactLogarithmBounds
import IPRADerivations.Analysis.Euler.GaussianEulerExponentCompactBounds

/-!
# Uniform bounds of the actual real log-Gamma samples on [1,2]

The physical strip bounds the elementary term independently of its
rational encoding. A later internal observation pays the finite
Stirling error, and regularity then returns to the requested clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeUnitStripBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianPositiveRationalLogarithm (fraction sample)
open GaussianRaabeStirlingCell (elementary)
open GaussianRaabeStirlingRemainder (model constantSample)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bounded_product bounded_difference bound_congr)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def constantCost (w : PTm n) : PTm n :=
  GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData w)
def cost (w : PTm n) : PTm n := num 91+constantCost w

@[simp] theorem subst_constantCost {m : ℕ} (σ : Fin n → PTm m) (w : PTm n) :
    Syn.subst σ (constantCost w) = constantCost (Syn.subst σ w) := by simp [constantCost]
@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (w : PTm n) :
    Syn.subst σ (cost w) = cost (Syn.subst σ w) := by simp [cost]

private theorem elementary_bound (p A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hDA : Γ ⊢[PRAAx] le D A) (hAD : Γ ⊢[PRAAx] le A (two*D)) :
    Γ ⊢[PRAAx] bounded (elementary p A D) (num 86) one := by
  let x := fraction A D
  let h : PTm n := GaussianRaabeStirlingCell.half
  have hA := le_trans hD hDA
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := RationalAlgebra.two_positive
  have xb := GaussianEulerExponentCompactBounds.fraction_bound A D two hD hAD
  have hb : Γ ⊢[PRAAx] bounded h one one :=
    GaussianEulerExponentCompactBounds.fraction_bound one two one h₂ (le_congr (.eqRefl _) (one_mul two).eqSymm h₂)
  have offset : Γ ⊢[PRAAx] bounded (qsub x h) (num 3) one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_difference x h two one one one (le_refl one) (le_refl one) xb hb)
  have logBound : Γ ⊢[PRAAx] bounded (sample p A D) (num 28) one :=
    bound_congr (.eqRefl _) (by unfold GaussianCompactLogarithmBounds.radius; ipra_ring) (.eqRefl _)
      (GaussianCompactLogarithmBounds.sample_bound p A D one two (le_refl one)
        (.andI (.andI hA hD) (.andI (le_congr (.eqRefl _) (one_mul A).eqSymm hDA) hAD)))
  have product : Γ ⊢[PRAAx] bounded (qmul (qsub x h) (sample p A D)) (num 84) one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) offset logBound)
  exact bound_congr (GaussianRaabeStirlingCell.elementary_at p A D).eqSymm (by ipra_ring) (by ipra_ring)
    (bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one) product xb)

private theorem model_bound (p A D w : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hDA : Γ ⊢[PRAAx] le D A) (hAD : Γ ⊢[PRAAx] le A (two*D)) :
    Γ ⊢[PRAAx] bounded (model p A D w) (num 86+constantCost w) one := by
  have hc : Γ ⊢[PRAAx] bounded (constantSample p w) (constantCost w) one :=
    GaussianNameBounds.sample_bound _ _ p (GaussianStirlingConstant.name_regular w)
  exact GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one)
    (elementary_bound p A D hD hDA hAD) hc

theorem sample_bound (p A D w : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hDA : Γ ⊢[PRAAx] le D A) (hAD : Γ ⊢[PRAAx] le A (two*D)) :
    Γ ⊢[PRAAx] bounded (ap2 logGammaF p (logGammaData A D)) (cost w) one := by
  let x := logGammaData A D
  let L := num 18+two*A
  let q := GaussianFastValueCut.exponent L zero
  let V := unit q
  let U := unit p
  have hA := le_trans hD hDA
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) q
  have paid : Γ ⊢[PRAAx] le L V := le_trans
    (le_congr (one_mul L) (mul_comm (unit zero) L) (mul_le_mul_right L (unit_positive zero)))
    (GaussianFastValueCut.query_budget L zero)
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 logGammaF p x) (ap2 logGammaF q x) two one :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hV) (le_refl one)
      (by ipra_le 𝔞(U)*sl hV+𝔞(V)*sl hU)
      (GaussianNameEquivalence.point_at _ _ p q (log_gamma_regular A D (.andI hA hD)))
  have second : Γ ⊢[PRAAx] distanceBounded (ap2 logGammaF q x) (model q A D w) (num 3) one :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hA hV) (le_refl one)
      (by dsimp only [L,V] at paid
          dsimp only [GaussianRaabeStirlingRemainder.numerator,GaussianRaabeStirlingRemainder.denominator]
          ipra_le 2*𝔞(unit q)*sl hDA+𝔞(A)*sl paid)
      (GaussianRaabeStirlingRemainder.sample_error q A D w hD hDA)
  have hnear := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ (le_refl one) first second
  exact bound_congr (.eqRefl _) (by unfold cost; ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one)
      hnear (model_bound q A D w hD hDA hAD))

theorem actual_real_log_Gamma_unit_strip_observation_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let p := var 0
       let A := var 1
       let D := var 2
       let w := var 3
       (le one D ⋏ (le D A ⋏ le A (two*D))) ⟶
         bounded (ap2 logGammaF p (logGammaData A D)) (cost w) one) :=
  closeUniv 4 (.impI (sample_bound _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeUnitStripBound
