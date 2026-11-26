import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeOriginSchedule
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeAtOne
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabePositiveComparison
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalInverseQuadraticAlgebra

/-!
# Cofinal quadrature for the Raabe endpoint

The truncated interval is [2⁻ʰ, 1]. Its translation into [1 + 2⁻ʰ, 2]
uses the same grid step as the full unit interval. The log-Gamma
recurrence and the truncated logarithm integral then identify the
cofinal value at the origin with the actual Stirling constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeOriginComparison

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRaabeOriginSchedule (cutoff mesh fullMesh clock)
open GaussianRaabeOriginStripAlignment (full shifted truncated logStrip width)
open GaussianRaabeStirlingRemainder (constantSample)
open GaussianRaabeUnitStripBound (cost)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical qadd qzero positive_product)
open GaussianRationalMetric (distanceBounded qnegative qnegative_canonical qsub)
open GaussianRationalSyntheticDivision (qone qone_canonical qsub_congr qadd_congr qzero_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def value (k w : PTm n) : PTm n :=
  truncated (clock k (cost w)) (cutoff k (cost w)) (mesh k (cost w))

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (k w : PTm n) :
    Syn.subst σ (value k w) = value (Syn.subst σ k) (Syn.subst σ w) := by
  have cut (k C : PTm n) :
      Syn.subst σ (cutoff k C) = cutoff (Syn.subst σ k) (Syn.subst σ C) := by
    change Syn.subst σ ((k+C+one)+(k+C+one)+num 8) =
      (Syn.subst σ k+Syn.subst σ C+one)+(Syn.subst σ k+Syn.subst σ C+one)+num 8
    simp [one]
  simp [value, GaussianRaabeOriginStripAlignment.truncated, GaussianRaabeOriginStripAlignment.mesh,
    width, clock, mesh, fullMesh, cut, one, two]

private theorem undo_logarithm (s t A U : PTm n) (ht : Γ ⊢[PRAAx] canonical t)
    (hU : Γ ⊢[PRAAx] le one U)
    (error : Γ ⊢[PRAAx] distanceBounded (qsub s t) (qnegative qone) A U) :
    Γ ⊢[PRAAx] distanceBounded t (qadd s qone) A U := by
  have neg : Γ ⊢[PRAAx] qsub qzero qone ≐ qnegative (qone : PTm n) :=
    qzero_add _ (qnegative_canonical qone)
  have shifted_difference : Γ ⊢[PRAAx] qsub (qsub s t) (qnegative qone) ≐
      qadd (qsub s t) qone :=
    (qsub_congr (.eqRefl _) neg.eqSymm).eqTrans
      (GaussianRationalInverseQuadraticAlgebra.subtract_zero_difference (qsub s t) qone)
  have sum_difference : Γ ⊢[PRAAx] qsub (qadd s qone) t ≐ qadd (qsub s t) qone :=
    (qsub_congr (.eqRefl _) (GaussianRationalLinearProduct.qadd_zero_right t ht).eqSymm).eqTrans
      ((GaussianNameArithmetic.sum_difference s t qone qzero).eqTrans
        (qadd_congr (.eqRefl _) (GaussianRationalReconstruction.qsub_zero_right qone qone_canonical)))
  exact distance_symmetric _ _ _ _ hU
    (GaussianRationalReciprocal.bound_congr (shifted_difference.eqTrans sum_difference.eqSymm)
      (.eqRefl _) (.eqRefl _) error)

theorem observation_error (k w : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (value k w) (constantSample (clock k (cost w)) w)
      (num 39) (unit k) := by
  let C := cost w
  let h := cutoff k C
  let E := unit h
  let K := mesh k C
  let N := fullMesh k C
  let p := clock k C
  let U := unit k
  let V := unit p
  let F := full p h K
  let S := shifted p h K
  let T := truncated p h K
  let L := logStrip p h K
  let c := constantSample p w
  let R := ap2 GaussianRaabeRightSide.nameF p (GaussianRaabeRightSide.data E E w)
  have hh : Γ ⊢[PRAAx] le two E := GaussianRaabeOriginSchedule.cutoff_positive k C
  have he : Γ ⊢[PRAAx] le one E := unit_positive h
  have hu : Γ ⊢[PRAAx] le one U := unit_positive k
  have hv : Γ ⊢[PRAAx] le one V := unit_positive p
  have ev : Γ ⊢[PRAAx] le one (E*V) := positive_product _ _ he hv
  have hK : Γ ⊢[PRAAx] le one K := (GaussianRaabeOriginSchedule.mesh_floors k C).andE₁
  have late : Γ ⊢[PRAAx] le U V :=
    GaussianExponentialReference.unit_monotone (GaussianRaabeCofinalSchedule.clockFor_later k N E E)
  have cut : Γ ⊢[PRAAx] le (C*U) E :=
    le_trans (mul_le_mul_right U (le_add_left C _)) (GaussianRaabeOriginSchedule.cutoff_budget k C)
  have width_le : Γ ⊢[PRAAx] le (width h) E :=
    le_congr (.eqRefl _) (GaussianRaabeOriginStripAlignment.total_width h).eqSymm (le_add_left _ _)
  have full_shifted : Γ ⊢[PRAAx] distanceBounded F S (num 3) U :=
    distance_radius_mono _ _ _ _ _ _ ev hu
      (by change Γ ⊢[PRAAx] le ((two*E+C*V)*U) (num 3*(E*V))
          ipra_le 2*𝔞(E)*sl late+𝔞(V)*sl cut)
      (GaussianRaabeOriginStripAlignment.shifted_to_full p h K w hK)
  have full_limit : Γ ⊢[PRAAx] distanceBounded F R (num 14) U :=
    GaussianRaabePositiveComparison.observation_for k N E E w (.andI he he)
      (GaussianRaabeOriginSchedule.mesh_floors k C).andE₂.andE₂.andE₁
  have endpoint : Γ ⊢[PRAAx] le (GaussianRaabeRightSide.cost E*U) V :=
    (GaussianRaabeCofinalSchedule.endpoint_budgets_for k N E E).andE₂
  have right_limit : Γ ⊢[PRAAx] distanceBounded R (qsub c qone) (num 11) U :=
    distance_radius_mono _ _ _ _ _ _ hv hu
      (by ipra_le sl endpoint+10*sl late)
      (GaussianRaabeAtOne.right_side_at_unit p E w he)
  have shifted_limit : Γ ⊢[PRAAx] distanceBounded S (qsub c qone) (num 28) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hu
        (distance_symmetric _ _ _ _ hu full_shifted)
        (distance_triangle_same _ _ _ _ _ _ hu full_limit right_limit))
  have shift_log : Γ ⊢[PRAAx] distanceBounded (qsub S T) L (num 8) U :=
    distance_radius_mono _ _ _ _ _ _ ev hu
      (by ipra_le 8*𝔞(U)*sl width_le+8*𝔞(E)*sl late)
      (GaussianRaabeOriginStripAlignment.shift_error p h K hh hK)
  have log_den : Γ ⊢[PRAAx] le one (GaussianRaabeOriginLogStrip.denominator p h K) :=
    positive_product _ _ (positive_product _ _
      (GaussianRaabeOriginStripAlignment.mesh_positive h K hh hK) he) hv
  have log_limit : Γ ⊢[PRAAx] distanceBounded L (qnegative qone) (num 3) U :=
    distance_radius_mono _ _ _ _ _ _ log_den hu
      (GaussianRaabeOriginSchedule.log_budget k C)
      (GaussianRaabeOriginLogStrip.quadrature_error p h K hh hK)
  have strip_limit : Γ ⊢[PRAAx] distanceBounded T (qadd S qone) (num 11) U :=
    undo_logarithm _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _) hu
      (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
        (distance_triangle_same _ _ _ _ _ _ hu shift_log log_limit))
  have c_canonical : Γ ⊢[PRAAx] canonical c := GaussianNameArithmetic.multiply_canonical _ _ _ _ _
  have cancel : Γ ⊢[PRAAx] qadd (qsub c qone) qone ≐ c :=
    (GaussianRationalLinearProduct.qadd_commutative (qsub c qone) qone).eqTrans
      (GaussianRationalLinearProduct.add_sub_right qone c c_canonical)
  have translated : Γ ⊢[PRAAx] distanceBounded (qadd S qone) c (num 28) U :=
    distance_congr (.eqRefl _) cancel (add_zero _) (.eqRefl _)
      (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hu shifted_limit
        (GaussianRationalPowerDifference.distance_refl_zero qone U hu))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu strip_limit translated)

end LeanProofs.IPRA.Analysis.GaussianRaabeOriginComparison
