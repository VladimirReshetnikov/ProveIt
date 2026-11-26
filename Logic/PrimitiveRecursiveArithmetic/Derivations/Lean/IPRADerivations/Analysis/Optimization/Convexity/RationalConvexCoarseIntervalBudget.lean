import IPRADerivations.Analysis.Optimization.Convexity.RationalOriginalConvexModulus

/-!
# The original interval upper endpoints lie below the two-sample budget

The existing budget is one plus the ceiling of the larger absolute
precision-zero midpoint. The original interval has width at most one,
so its precision-zero upper endpoint is below that same integer budget.
Nesting preserves this bound at every stage, without a sampling error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexCoarseIntervalBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters (midpoint)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open RationalValueBounds (upper upper_mono upper_order_right)
open RationalConvexEndpointBudget (coarseCeiling coarseBudget original_observation_bound order_of_upper M sample)
open RationalConvexSecantWeights (leftPoint rightPoint)
open RationalNestedIntervals (regular read center centerF center_at step_at nesting)
open GaussianRationalSyntheticBounds (natCode natCode_add)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem upper_of_coarse_midpoint (a b lo hi : PTm n)
    (hw : Γ ⊢[PRAAx] upper hi lo one one)
    (hc : Γ ⊢[PRAAx] rationalLE (midpoint lo hi) (natCode (coarseCeiling a b))) :
    Γ ⊢[PRAAx] rationalLE hi (natCode (coarseBudget a b)) := by
  have hhalf := RationalCubeInfimumName.midpoint_half_right lo hi one one hw
  have hfull := upper_mono hi (midpoint lo hi) one (two*one) one one
    (le_of_eq_add (d := one) (by ipra_ring)) hhalf (le_of_eq_add (d := one) (by ipra_ring))
  have h := order_of_upper hi (natCode (coarseCeiling a b)) one one (le_refl one)
    (upper_order_right _ _ _ _ _ hfull hc)
  have e : Γ ⊢[PRAAx] RationalArithmetic.add (natCode (coarseCeiling a b))
      (RationalCubeMidpoint.fraction one one) ≐ natCode (coarseBudget a b) := by
    exact (natCode_add _ _).eqTrans
      (GaussianRationalSyntheticBounds.natCode_congr (by unfold coarseBudget; ipra_ring))
  exact rationalLE_congr (.eqRefl _) e h

theorem interval_upper_at_budget (L U : PR 3) (q p x a b : PTm n)
    (hr : Γ ⊢[PRAAx] regular L U q x)
    (hc : Γ ⊢[PRAAx] rationalLE (center L U q zero x) (natCode (coarseCeiling a b))) :
    Γ ⊢[PRAAx] rationalLE (read U q p x) (natCode (coarseBudget a b)) := by
  have hw := (step_at L U q zero x hr).andE₂.andE₂.andE₂
  have hw' : Γ ⊢[PRAAx] upper (read U q zero x) (read L q zero x) one one :=
    RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (pw_zero two) hw
  have hz := upper_of_coarse_midpoint a b _ _ hw' hc
  exact transitive (nesting L U q zero p x hr (zero_le p)).andE₂ hz

theorem actual_two_upper_endpoint_bounds (L U : PR 3) (D P Q p x : PTm n)
    (ha : Γ ⊢[PRAAx] regular L U (leftPoint D P) x)
    (hb : Γ ⊢[PRAAx] regular L U (rightPoint D Q) x) :
    Γ ⊢[PRAAx] rationalLE (read U (leftPoint D P) p x) (natCode (M (centerF L U) D P Q x)) ⋏
      rationalLE (read U (rightPoint D Q) p x) (natCode (M (centerF L U) D P Q x)) := by
  let a := sample (centerF L U) (leftPoint D P) zero x
  let b := sample (centerF L U) (rightPoint D Q) zero x
  have h := original_observation_bound (Γ := Γ) a b
  have ca := rationalLE_congr (center_at L U (leftPoint D P) zero x) (.eqRefl _) h.andE₁
  have cb := rationalLE_congr (center_at L U (rightPoint D Q) zero x) (.eqRefl _) h.andE₂
  exact .andI (interval_upper_at_budget L U _ p x a b ha ca)
    (interval_upper_at_budget L U _ p x a b hb cb)

theorem actual_two_zero_upper_endpoint_bounds (L U : PR 3) (D P Q x : PTm n)
    (ha : Γ ⊢[PRAAx] regular L U (leftPoint D P) x)
    (hb : Γ ⊢[PRAAx] regular L U (rightPoint D Q) x) :
    Γ ⊢[PRAAx] rationalLE (read U (leftPoint D P) zero x) (natCode (M (centerF L U) D P Q x)) ⋏
      rationalLE (read U (rightPoint D Q) zero x) (natCode (M (centerF L U) D P Q x)) :=
  actual_two_upper_endpoint_bounds L U D P Q zero x ha hb

theorem original_two_upper_endpoint_bounds (L U : PR 3) (a b p x : PTm n)
    (hna : Γ ⊢[PRAAx] RationalConvexSecants.nonnegative a)
    (hnb : Γ ⊢[PRAAx] RationalConvexSecants.nonnegative b)
    (ha : Γ ⊢[PRAAx] regular L U (RationalOriginalConvexModulus.sourceLeft a) x)
    (hb : Γ ⊢[PRAAx] regular L U (RationalOriginalConvexModulus.sourceRight b) x) :
    Γ ⊢[PRAAx] rationalLE (read U (RationalOriginalConvexModulus.sourceLeft a) p x)
      (natCode (M (centerF L U) (RationalConvexArguments.endpointDen a b)
        (RationalConvexArguments.firstNumerator a b) (RationalConvexArguments.secondNumerator a b) x)) ⋏
      rationalLE (read U (RationalOriginalConvexModulus.sourceRight b) p x)
      (natCode (M (centerF L U) (RationalConvexArguments.endpointDen a b)
        (RationalConvexArguments.firstNumerator a b) (RationalConvexArguments.secondNumerator a b) x)) := by
  let D := RationalConvexArguments.endpointDen a b
  let P := RationalConvexArguments.firstNumerator a b
  let Q := RationalConvexArguments.secondNumerator a b
  let A := sample (centerF L U) (leftPoint D P) zero x
  let B := sample (centerF L U) (rightPoint D Q) zero x
  have e := RationalConvexArguments.original_endpoint_queries a b hna hnb
  have eA : Γ ⊢[PRAAx] A ≐ center L U (RationalOriginalConvexModulus.sourceLeft a) zero x :=
    (congrAp3 (centerF L U) e.andE₁ (.eqRefl _) (.eqRefl _)).eqTrans
      (center_at L U _ zero x)
  have eB : Γ ⊢[PRAAx] B ≐ center L U (RationalOriginalConvexModulus.sourceRight b) zero x :=
    (congrAp3 (centerF L U) e.andE₂ (.eqRefl _) (.eqRefl _)).eqTrans
      (center_at L U _ zero x)
  have h := original_observation_bound (Γ := Γ) A B
  exact .andI (interval_upper_at_budget L U _ p x A B ha (rationalLE_congr eA (.eqRefl _) h.andE₁))
    (interval_upper_at_budget L U _ p x A B hb (rationalLE_congr eB (.eqRefl _) h.andE₂))

theorem actual_two_upper_endpoint_bounds_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((regular L U (leftPoint (var 0) (var 1)) (var 4) ⋏
      regular L U (rightPoint (var 0) (var 2)) (var 4)) ⟶
      rationalLE (read U (leftPoint (var 0) (var 1)) (var 3) (var 4))
        (natCode (M (centerF L U) (var 0) (var 1) (var 2) (var 4))) ⋏
      rationalLE (read U (rightPoint (var 0) (var 2)) (var 3) (var 4))
        (natCode (M (centerF L U) (var 0) (var 1) (var 2) (var 4)))) :=
  closeUniv 5 (.impI (actual_two_upper_endpoint_bounds L U _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem original_two_upper_endpoint_bounds_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((RationalConvexSecants.nonnegative (var 0) ⋏ RationalConvexSecants.nonnegative (var 1)) ⟶
      (regular L U (RationalOriginalConvexModulus.sourceLeft (var 0)) (var 3) ⋏
        regular L U (RationalOriginalConvexModulus.sourceRight (var 1)) (var 3)) ⟶
      rationalLE (read U (RationalOriginalConvexModulus.sourceLeft (var 0)) (var 2) (var 3))
        (natCode (M (centerF L U) (RationalConvexArguments.endpointDen (var 0) (var 1))
          (RationalConvexArguments.firstNumerator (var 0) (var 1))
          (RationalConvexArguments.secondNumerator (var 0) (var 1)) (var 3))) ⋏
      rationalLE (read U (RationalOriginalConvexModulus.sourceRight (var 1)) (var 2) (var 3))
        (natCode (M (centerF L U) (RationalConvexArguments.endpointDen (var 0) (var 1))
          (RationalConvexArguments.firstNumerator (var 0) (var 1))
          (RationalConvexArguments.secondNumerator (var 0) (var 1)) (var 3)))) :=
  closeUniv 4 (.impI (.impI (original_two_upper_endpoint_bounds L U _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.RationalConvexCoarseIntervalBudget
