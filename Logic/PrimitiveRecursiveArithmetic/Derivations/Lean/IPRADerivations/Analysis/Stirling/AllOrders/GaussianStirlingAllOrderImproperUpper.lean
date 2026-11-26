import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderNamedUpperGap
import IPRADerivations.Analysis.Names.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Gamma.GaussianGammaRationalWendelBoundary
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsCaps

/-!
# The sharp upper bound for the original fixed-order improper integral

The positive finite covariance gap survives passage to the exact
weighted primitive and the original improper name. Canceling the
same named quantity on both sides gives the strict upper order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderImproperUpper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaRationalWendelBoundary (fraction_zero zero_data_cross)
open GaussianGammaStrongLogConvexityAlgebra (swap_first)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_negative zeroF zero_at zero_fast)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedStrictOrderDifference (add_left trans_weak)
open GaussianStirlingAllOrderImproperName (original_improper_cross)
open GaussianStirlingAllOrderNamedUpperGap
  (floorDenominator floorPoint floor_denominator_positive gapF gapData gap_regular named_gap_lower)
open GaussianStirlingAllOrderPanelPartsNames (nameF nameData name_regular weightedPrimitive)
open GaussianStirlingMultiplicativeBoundsCaps (strict_fractions)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open GaussianStirlingNames (source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "fraction" => GaussianPositiveRationalLogarithm.fraction

private theorem add_back (F : PR 2) (x c : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x) :
    Γ ⊢[PRAAx] crossEquivalent (addF F (GaussianNamedDifference.nameF constantF F)) constantF
      (addData x (GaussianNamedDifference.data c x)) c := by
  let H := negativeF F
  let y := negativeData x
  have hc := constant_regular (Γ := Γ) c
  have hy := negative_fast F x hf
  have e := swap_first F constantF H x c y hf hc hy
  have inv := cross_trans _ _ _ _ _ _ (add_negative F x hf) (zero_data_cross x c)
  have gone := add_cross constantF constantF (addF F H) zeroF c c (addData x y) c
    hc hc (add_fast _ _ _ _ hf hy) (zero_fast c) (cross_refl _ _ hc) inv
  exact cross_trans _ _ _ _ _ _ e (cross_trans _ _ _ _ _ _ gone (GaussianNameRingLaws.add_zero constantF c hc))

private theorem zero_agreement (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent zeroF constantF x (fraction zero one) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast _) (constant_regular _)
  refine .allI ?_
  simpa [Syn.shift,one] using ((zero_at (var 0) (Syn.shift x)).eqTrans
    ((fraction_zero (n := n+1) one (le_refl one)).eqSymm.eqTrans (constant_at (var 0) (fraction zero one)).eqSymm))

theorem recurrence_upper (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder (nameF m) constantF (nameData m A B x) (weightedPrimitive m A B) := by
  let F := nameF m
  let X := nameData m A B x
  let C := weightedPrimitive m A B
  let D := floorDenominator m A B
  let P := floorPoint m A B
  let Z := fraction (zero : PTm n) one
  let G := gapF m
  let Y := gapData m A B x
  have hD := floor_denominator_positive m A B hs.andE₁
  have rise : Γ ⊢[PRAAx] lt (D*zero) (one*one) := by
    change Γ ⊢[PRAAx] le (ConciseIPRA.PTm.succ (D*zero)) (one*one)
    ipra_le 0
  have zp : Γ ⊢[PRAAx] strictOrder constantF constantF Z P :=
    .andI (constant_order _ _ (fractions_order zero one one D (le_refl one) hD (by ipra_le 1)))
      (strict_fractions zero one one D (le_refl one) hD rise)
  have zg := trans_weak _ _ _ _ _ _ zp (named_gap_lower m A B x hs)
  have hr := gap_regular m A B x hs
  have hf := name_regular m A B x hs
  have adapted : Γ ⊢[PRAAx] strictOrder zeroF G X Y :=
    strict_transport _ _ _ _ _ _ _ _ (zero_agreement X) (cross_refl _ _ hr) zg
  have raised := add_left zeroF G F X Y X (zero_fast X) hr hf adapted
  exact strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianNameRingLaws.add_zero F X hf)) (add_back F X C hf) raised

theorem original_improper_upper (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder (GaussianStirlingAllOrderImproperName.nameF m) constantF
      (GaussianStirlingAllOrderImproperName.data m A B) (weightedPrimitive m A B) :=
  strict_transport _ _ _ _ _ _ _ _ (original_improper_cross m A B x hs)
    (cross_refl _ _ (constant_regular _)) (recurrence_upper m A B x hs)

theorem actual_all_order_periodic_improper_strict_upper_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) ⟶ strictOrder (GaussianStirlingAllOrderImproperName.nameF m) constantF
        (GaussianStirlingAllOrderImproperName.data m (var 0) (var 1)) (weightedPrimitive m (var 0) (var 1))) :=
  closeUniv 3 (.impI (original_improper_upper m _ _ (var 2) Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderImproperUpper
