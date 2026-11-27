import IPRADerivations.Analysis.Geometry.HalfAngles.GaussianRationalHalfAngleRecovery
import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalDirectionClock
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalRoundedPower

/-!
# A computed rational root direction for an actual unit input

The entire half-angle count, grid and rounded power come from the
verified numerical clock. For k,q>=1 and an original canonical unit
point c, the actual output w is unit and w^k is within 1/(8q) of c.
No accuracy, prefix, successful search or clock budget is an input.
The initializer for arbitrary nonzero c is a separate construction.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalDirectionIteration

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (canonical positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power qone)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq qsub distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax (four)
open LeanProofs.IPRA.Analysis.GaussianRationalDirectionClock
  (sixteen eight steps period localIndex height roundedPower leftover)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def last (c k q : PTm n) : PTm n := GaussianRationalHalfAngleIteration.iterate c (height k q) (steps k q)
def direction (c k q : PTm n) : PTm n := power (last c k q) (roundedPower k q)
def denominator (q : PTm n) : PTm n := sixteen*q
def nearDenominator (k q : PTm n) : PTm n := sixteen*k*q

ipra_subst last
ipra_subst direction
ipra_subst denominator
ipra_subst nearDenominator

theorem four_le_sixteen : Γ ⊢[PRAAx] le (four : PTm n) sixteen :=
  le_congr ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))) (.eqRefl _)
    (GaussianBalancedRadiusArithmetic.unit_monotone two four
      (le_of_eq_add (d := two) (by unfold four; ipra_ring)))

theorem sixteen_double_eight : Γ ⊢[PRAAx] (sixteen : PTm n) ≐ two*eight :=
  (congrAp2 powF (by unfold four; ipra_ring) (.eqRefl two)).eqTrans
    ((pw_succ two (succ two)).eqTrans (mul_comm _ _))

theorem height_precision (k q : PTm n) : Γ ⊢[PRAAx]
    height k q ≐ GaussianRationalHalfAngle.precision (localIndex k q) :=
  congrAp2 powF (by unfold GaussianRationalDirectionClock.precision GaussianRationalDirectionClock.ten four; ipra_ring) (.eqRefl two)

theorem grid_budget (k q : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHalfAngleRecovery.budget (height k q) (localIndex k q) :=
  le_congr (.eqRefl _) (height_precision k q).eqSymm (GaussianRationalHalfAngle.precision_budget _)

theorem denominator_positive (q : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    le one (denominator q) := positive_product _ _ GaussianRationalDirectionClock.sixteen_positive hq

theorem near_denominator_positive (k q : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx] le one (nearDenominator k q) :=
  positive_product _ _ (positive_product _ _ GaussianRationalDirectionClock.sixteen_positive hk) hq

theorem last_unit (c k q : PTm n) (hc : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit c) : Γ ⊢[PRAAx]
    GaussianRationalHalfAngle.unit (last c k q) :=
  GaussianRationalHalfAngleIteration.iterate_unit _ _ _ (GaussianRationalDirectionClock.height_positive k q) hc

theorem direction_unit (c k q : PTm n) (hc : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit c) : Γ ⊢[PRAAx]
    GaussianRationalHalfAngle.unit (direction c k q) := GaussianRationalPowerAlgebra.unit_power _ _ (last_unit c k q hc)

/-- The exact contraction and the computed clock supply the local radius
needed for the final rounded power. No square-root choice is made. -/
theorem last_near_one (c k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hq : Γ ⊢[PRAAx] le one q)
    (hc : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit c) : Γ ⊢[PRAAx]
    distanceBounded (last c k q) qone one (nearDenominator k q) := by
  have distanceBound :=  GaussianRationalHalfAngleIteration.iterate_near_one c (height k q) (steps k q)
    (GaussianRationalDirectionClock.height_positive k q) hc
  have budget : Γ ⊢[PRAAx] le (four*(nearDenominator k q*nearDenominator k q)) (period k q) :=
    le_trans (mul_le_mul_right (nearDenominator k q*nearDenominator k q) (four_le_sixteen (Γ := Γ)))
      (le_congr (by unfold nearDenominator; ipra_ring) (.eqRefl _) (GaussianRationalDirectionClock.period_budget k q))
  exact RationalArgmin.transitive distanceBound
    (GaussianEuclideanDistanceName.fraction_order _ _ _ _ (GaussianRationalDirectionClock.period_positive k q)
      (positive_product _ _ (near_denominator_positive k q hk hq) (near_denominator_positive k q hk hq))
      (le_congr (by unfold four GaussianRationalCircleParametrization.four; ipra_ring)
        (by unfold GaussianRationalDirectionClock.period; ipra_ring) budget))

theorem rounded_close (c k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hq : Γ ⊢[PRAAx] le one q)
    (hc : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit c) : Γ ⊢[PRAAx]
    distanceBounded (power (direction c k q) k)
      (GaussianRationalHalfAngleRecovery.recovered c (height k q) (steps k q)) one (denominator q) := by
  have rounded := GaussianRationalRoundedPower.rounded_power_distance (last c k q) k (roundedPower k q)
    (leftover k q) (period k q) one (nearDenominator k q) (near_denominator_positive k q hk hq)
    (last_unit c k q hc) (last_near_one c k q hk hq hc)
    (Prf.andE₁ (GaussianRationalDirectionClock.division_spec k q hk))
  have remainder := le_of_lt (Prf.andE₂ (GaussianRationalDirectionClock.division_spec (Γ := Γ) k q hk))
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (near_denominator_positive k q hk hq) (denominator_positive q hq)
    (le_congr (by unfold denominator; ipra_ring) (by simp only [nearDenominator,denominator]; ipra_ring)
      (mul_le_mul_right (sixteen*q) remainder)) rounded

theorem recovered_close (c k q : PTm n) (hq : Γ ⊢[PRAAx] le one q)
    (hcanon : Γ ⊢[PRAAx] canonical c) (hc : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit c) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRationalHalfAngleRecovery.recovered c (height k q) (steps k q)) c one (denominator q) := by
  have recovered := GaussianRationalHalfAngleRecovery.actual_recovery c (height k q) (localIndex k q) (steps k q)
    (GaussianRationalDirectionClock.height_positive k q) hcanon hc (grid_budget k q)
  have errorBound : Γ ⊢[PRAAx] le (GaussianRationalHalfAngleRecovery.error (steps k q)) (period k q) :=
    le_of_eq_add (d := one) ((RationalIntegerNormalization.positive_form (GaussianRationalDirectionClock.period_positive k q)).eqTrans (by unfold GaussianRationalHalfAngleRecovery.error GaussianRationalDirectionClock.period; ipra_ring))
  have first := mul_le_mul_right (denominator q) errorBound
  have middle : Γ ⊢[PRAAx] le (period k q*denominator q) (sixteen*sixteen*q*period k q) :=
    le_congr (by unfold denominator; ipra_ring) (by ipra_ring)
      (mul_le_mul_right (sixteen*q*period k q) (GaussianRationalDirectionClock.sixteen_positive (Γ := Γ)))
  have total : Γ ⊢[PRAAx] le (GaussianRationalHalfAngleRecovery.error (steps k q)*denominator q) (unit (localIndex k q)) :=
    le_trans first (le_trans middle (GaussianRationalDirectionClock.local_error_budget k q))
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ (unit_positive _)
    (denominator_positive q hq) (le_congr (.eqRefl _) (by ipra_ring) total) recovered

/-- The actual finite algorithm satisfies the uniform unit-input root
direction estimate. The constructor's clock discharges every budget. -/
theorem direction_close (c k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hq : Γ ⊢[PRAAx] le one q)
    (hcanon : Γ ⊢[PRAAx] canonical c) (hc : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit c) : Γ ⊢[PRAAx]
    distanceBounded (power (direction c k q) k) c one (eight*q) := by
  have both := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ (denominator_positive q hq)
    (rounded_close c k q hk hq hc) (recovered_close c k q hq hcanon hc)
  have identity : Γ ⊢[PRAAx] (one+one)*(eight*q) ≐ one*denominator q :=
    (by ipra_ring : Γ ⊢[PRAAx] (one+one)*(eight*q) ≐ two*eight*q).eqTrans
      ((congrMul sixteen_double_eight.eqSymm (.eqRefl q)).eqTrans (by unfold denominator; ipra_ring))
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ (denominator_positive q hq)
    (positive_product _ _ (unit_positive (succ two)) hq)
    (le_congr (.eqRefl _) identity (le_refl _)) both

def certificate (c k q : PTm n) : Fm PTm n := canonical (direction c k q) ⋏
  (GaussianRationalHalfAngle.unit (direction c k q) ⋏ distanceBounded (power (direction c k q) k) c one (eight*q))
ipra_subst certificate

theorem direction_correct (c k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hq : Γ ⊢[PRAAx] le one q)
    (hcanon : Γ ⊢[PRAAx] canonical c) (hc : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit c) : Γ ⊢[PRAAx]
    certificate c k q := .andI (GaussianRationalReciprocal.power_canonical _ _)
      (.andI (direction_unit c k q hc) (direction_close c k q hk hq hcanon hc))

def output (c k q : PTm n) : PTm n := pairT (direction c k q)
  (pairT (power (direction c k q) k) (pairT (last c k q) (GaussianRationalDirectionClock.run k q)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (c k q : PTm n) : PTm n := ap3 outputF c k q

ipra_subst output
ipra_subst run

theorem program_at (c k q : PTm n) : Γ ⊢[PRAAx] run c k q ≐ output c k q := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![c,k,q]
theorem returned_direction (c k q : PTm n) : Γ ⊢[PRAAx] fstT (run c k q) ≐ direction c k q :=
  (program_at c k q).fstE
theorem returned_power (c k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run c k q)) ≐ power (direction c k q) k :=
  (program_at c k q).sndE.fstE
theorem returned_last (c k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run c k q))) ≐ last c k q :=
  (program_at c k q).sndE.sndE.fstE
theorem returned_clock (c k q : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run c k q))) ≐ GaussianRationalDirectionClock.run k q :=
  (program_at c k q).sndE.sndE.sndE

theorem returned_distance (c k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hq : Γ ⊢[PRAAx] le one q)
    (hcanon : Γ ⊢[PRAAx] canonical c) (hc : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit c) : Γ ⊢[PRAAx]
    distanceBounded (fstT (sndT (run c k q))) c one (eight*q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_power c k q).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (direction_close c k q hk hq hcanon hc)

theorem unit_input_direction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ canonical (var 0) ⟶ GaussianRationalHalfAngle.unit (var 0) ⟶
      certificate (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (direction_correct _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem returned_unit_direction_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ canonical (var 0) ⟶ GaussianRationalHalfAngle.unit (var 0) ⟶
      distanceBounded (fstT (sndT (run (var 0) (var 1) (var 2)))) (var 0) one (eight*var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (returned_distance _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem direction_iteration_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) ⋏
      (fstT (run (var 0) (var 1) (var 2)) ≐ direction (var 0) (var 1) (var 2) ⋏
        (fstT (sndT (run (var 0) (var 1) (var 2))) ≐ power (direction (var 0) (var 1) (var 2)) (var 1) ⋏
          (fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ last (var 0) (var 1) (var 2) ⋏
            sndT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ GaussianRationalDirectionClock.run (var 1) (var 2))))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_direction _ _ _)
    (.andI (returned_power _ _ _) (.andI (returned_last _ _ _) (returned_clock _ _ _)))))

end LeanProofs.IPRA.Analysis.GaussianRationalDirectionIteration
