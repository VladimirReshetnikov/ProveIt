import IPRADerivations.Analysis.Geometry.HalfAngles.GaussianRationalHalfAngleIteration
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerDifference
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder

/-!
# Powered recovery from actual repeated half-angles

The actual jth iterate, raised to 2^j, is within (2^j-1)/2^J of the
original point. The only numerical accuracy guard is the explicit grid
budget 400*2^J*2^J<=H. Each local square estimate is proved for the actual
half-angle constructor. Genuine quantifier-free induction accumulates
the powered errors. No local accuracy or global recovery law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalHalfAngleRecovery

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHalfAngleIteration (iterate)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF bound_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def error (j : PTm n) : PTm n := pred (unit j)
def recovered (q H j : PTm n) : PTm n := power (iterate q H j) (unit j)
def budget (H J : PTm n) : Fm PTm n := le ((num 400)*unit J*unit J) H
def law (q H J j : PTm n) : Fm PTm n := distanceBounded (recovered q H j) q (error j) (unit J)

ipra_subst error
ipra_subst recovered
ipra_subst budget
ipra_subst law

theorem unit_succ (j : PTm n) : Γ ⊢[PRAAx] unit (succ j) ≐ two*unit j :=
  (pw_succ two j).eqTrans (mul_comm _ _)

theorem error_zero : Γ ⊢[PRAAx] error (zero : PTm n) ≐ zero :=
  (congrPred (pw_zero two)).eqTrans (pred_succ zero)

theorem error_step (j : PTm n) : Γ ⊢[PRAAx] error (succ j) ≐ unit j+error j := by
  have shape := RationalIntegerNormalization.positive_form (unit_positive (Γ := Γ) j)
  have double : Γ ⊢[PRAAx] two*unit j ≐ unit j+unit j := by ipra_ring
  have e : Γ ⊢[PRAAx] unit (succ j) ≐ succ (unit j+error j) :=
    (unit_succ j).eqTrans (double.eqTrans
      ((congrAdd (.eqRefl (unit j)) shape).eqTrans (by unfold error; ipra_ring)))
  exact (congrPred e).eqTrans (pred_succ _)

theorem recovered_zero (q H : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx]
    recovered q H zero ≐ q :=
  (congrAp2 powerF (pw_zero two) (GaussianRationalHalfAngleIteration.iterate_zero q H)).eqTrans
    (GaussianRationalPowerAlgebra.power_one q hq)

theorem dyadic_power_square (q j : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx]
    power q (unit (succ j)) ≐ power (qmul q q) (unit j) :=
  (congrAp2 powerF (unit_succ j) (.eqRefl q)).eqTrans
    ((GaussianRationalPowerAlgebra.power_composition q two (unit j)).eqSymm.eqTrans
      (congrAp2 powerF (.eqRefl _) (GaussianRationalPowerAlgebra.power_two q hq)))

theorem recovered_succ (q H j : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    recovered q H (succ j) ≐ power
      (qmul (GaussianRationalHalfAngle.half (iterate q H j) H) (GaussianRationalHalfAngle.half (iterate q H j) H)) (unit j) :=
  (congrAp2 powerF (.eqRefl _) (GaussianRationalHalfAngleIteration.iterate_succ q H j)).eqTrans
    (dyadic_power_square _ j (GaussianRationalHalfAngle.half_canonical _ _ hH))

theorem recovery_zero (q H J : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] law q H J zero :=
  GaussianRationalDistanceOrder.distance_congr (recovered_zero q H hq).eqSymm (.eqRefl _) error_zero.eqSymm (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero q (unit J) (unit_positive J))

theorem recovery_step (q H J j : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hq : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit q)
    (hBudget : Γ ⊢[PRAAx] budget H J) (previous : Γ ⊢[PRAAx] law q H J j) : Γ ⊢[PRAAx]
    law q H J (succ j) := by
  let old := iterate q H j
  let h := GaussianRationalHalfAngle.half old H
  have oldUnit := GaussianRationalHalfAngleIteration.iterate_unit q H j hH hq
  have halfUnit := GaussianRationalHalfAngle.half_unit (Γ := Γ) old H hH
  have squareBound : Γ ⊢[PRAAx] bounded (qmul h h) one one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (GaussianRationalReciprocal.bounded_product h h one one one one (le_refl one) (le_refl one)
        (GaussianRationalPowerAlgebra.unit_bounded h halfUnit) (GaussianRationalPowerAlgebra.unit_bounded h halfUnit))
  have localError := GaussianRationalHalfAngle.half_square_accuracy_of_budget old H J hH oldUnit hBudget
  have powered := GaussianRationalPowerDifference.unit_disk_power_difference (qmul h h) old one (unit J) (unit j)
    (unit_positive J) squareBound (GaussianRationalPowerAlgebra.unit_bounded old oldUnit) localError
  have current : Γ ⊢[PRAAx] distanceBounded (recovered q H (succ j)) (recovered q H j) (unit j) (unit J) :=
    GaussianRationalDistanceOrder.distance_congr (recovered_succ q H j hH).eqSymm (.eqRefl _)
      (by ipra_ring) (.eqRefl _) powered
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (error_step j).eqSymm (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ (unit_positive J) current previous)

/-- All counts are internal, and the recovery invariant is derived by
the ordinary PRA quantifier-free induction rule. -/
theorem actual_recovery (q H J j : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hc : Γ ⊢[PRAAx] canonical q) (hu : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit q)
    (hBudget : Γ ⊢[PRAAx] budget H J) : Γ ⊢[PRAAx] law q H J j := by
  have Hshift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift H) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hH.shift
  have ushift : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalHalfAngle.unit (Syn.shift q) := by
    simpa only [Fm.shift,GaussianRationalHalfAngle.subst_unit,Syn.shift] using hu.shift
  have Bshift : Γ.map Fm.shift ⊢[PRAAx] budget (Syn.shift H) (Syn.shift J) := by
    simpa only [Fm.shift,subst_budget,Syn.shift] using hBudget.shift
  have all : Γ ⊢[PRAAx] .all (law (Syn.shift q) (Syn.shift H) (Syn.shift J) (var 0)) := by
    ipra_qfind (le_QF _ _) [subst_law]
    · exact recovery_zero q H J hc
    · exact recovery_step _ _ _ _ Hshift.wk ushift.wk Bshift.wk Prf.hyp0
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

def output (q H J j : PTm n) : PTm n :=
  pairT (recovered q H j) (pairT (iterate q H j) (pairT (error j) (unit J)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (q H J j : PTm n) : PTm n := PTm.app outputF ![q,H,J,j]

ipra_subst output
ipra_subst run

theorem program_at (q H J j : PTm n) : Γ ⊢[PRAAx] run q H J j ≐ output q H J j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![q,H,J,j]
theorem returned_recovered (q H J j : PTm n) : Γ ⊢[PRAAx] fstT (run q H J j) ≐ recovered q H j :=
  (program_at q H J j).fstE
theorem returned_iterate (q H J j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run q H J j)) ≐ iterate q H j :=
  (program_at q H J j).sndE.fstE
theorem returned_error (q H J j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run q H J j))) ≐ error j :=
  (program_at q H J j).sndE.sndE.fstE
theorem returned_denominator (q H J j : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run q H J j))) ≐ unit J :=
  (program_at q H J j).sndE.sndE.sndE

theorem returned_recovery (q H J j : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hc : Γ ⊢[PRAAx] canonical q) (hu : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit q)
    (hBudget : Γ ⊢[PRAAx] budget H J) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run q H J j)) q (error j) (unit J) :=
  GaussianRationalDistanceOrder.distance_congr (returned_recovered q H J j).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (actual_recovery q H J j hH hc hu hBudget)

theorem dyadic_recovery_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ canonical (var 0) ⟶ GaussianRationalHalfAngle.unit (var 0) ⟶
      budget (var 1) (var 2) ⟶ law (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (actual_recovery _ _ _ _ Prf.hyp0.wk.wk.wk
    Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem returned_dyadic_recovery_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ canonical (var 0) ⟶ GaussianRationalHalfAngle.unit (var 0) ⟶
      budget (var 1) (var 2) ⟶ distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3)))
        (var 0) (error (var 3)) (unit (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (returned_recovery _ _ _ _ Prf.hyp0.wk.wk.wk
    Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem dyadic_recovery_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) ⋏
      (fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ recovered (var 0) (var 1) (var 3) ⋏
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ iterate (var 0) (var 1) (var 3) ⋏
          (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ error (var 3) ⋏
            sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ unit (var 2))))) :=
  closeUniv 4 (.andI (program_at _ _ _ _) (.andI (returned_recovered _ _ _ _)
    (.andI (returned_iterate _ _ _ _) (.andI (returned_error _ _ _ _) (returned_denominator _ _ _ _)))))

end LeanProofs.IPRA.Analysis.GaussianRationalHalfAngleRecovery
