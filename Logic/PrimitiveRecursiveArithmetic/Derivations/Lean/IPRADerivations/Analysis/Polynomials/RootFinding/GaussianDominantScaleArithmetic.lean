import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDominantSyntax

/-!
# Exact squared-score separation at successive descent scales

Shrinking the radius by four multiplies the degree-i squared-score
denominator by 16^i. The genuine maximum comparisons at two successive
scales therefore rule out an upward change of a positive winning index.
Every coefficient code, degree, radius exponent, scale and index is
numerical. No maximum, scan success or global dominance law is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantScaleArithmetic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax
  (four exponent score numerator denominator score_represents denominator_positive)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- This is the squared scaling factor 16^i, rather than 4^i. -/
theorem scale_factor (i : PTm n) : Γ ⊢[PRAAx]
    unit (four*i) ≐ pw (unit four) i :=
  (GaussianDescentClockArithmetic.power_composition two four i).eqSymm

/-- Literal independent-denominator change of the actual score. -/
theorem denominator_succ (C N E h i : PTm n) : Γ ⊢[PRAAx]
    denominator C N E (succ h) i ≐ denominator C N E h i*unit (four*i) := by
  have index : Γ ⊢[PRAAx] two*exponent E (succ h)*i ≐ two*exponent E h*i+four*i := by
    unfold exponent four
    ipra_ring
  exact (congrMul (.eqRefl _) ((congrAp2 powF index (.eqRefl two)).eqTrans (pw_add two _ _))).eqTrans
    (by unfold denominator GaussianBalancedRadiusValues.scaledDenominator unit; ipra_ring)

/-- Strict degree order yields strictly separated squared scale factors. -/
theorem scale_strict (k i : PTm n) (hki : Γ ⊢[PRAAx] lt k i) : Γ ⊢[PRAAx]
    lt (unit (four*k)) (unit (four*i)) := by
  have first : Γ ⊢[PRAAx] le (succ (four*k)) (four*succ k) :=
    le_of_eq_add (d := GaussianBalancedRadiusSyntax.three) (by
      unfold four GaussianBalancedRadiusSyntax.three
      ipra_ring)
  have second := le_mul_mono (le_refl four) hki
  exact GaussianBalancedRadiusArithmetic.unit_strict _ _ (le_trans first second)

/-- Two opposite cleared maximum comparisons cannot survive a strictly
faster denominator increase at the larger degree. Only the factors
actually cancelled are required to be positive. -/
theorem max_drop_contradiction (ai ak bi bk vi vk : PTm n)
    (hOld : Γ ⊢[PRAAx] le (ai*bk) (ak*bi))
    (hNew : Γ ⊢[PRAAx] le (ak*(bi*vi)) (ai*(bk*vk)))
    (hak : Γ ⊢[PRAAx] le one ak) (hbi : Γ ⊢[PRAAx] le one bi)
    (hv : Γ ⊢[PRAAx] lt vk vi) : Γ ⊢[PRAAx] Fm.bot := by
  have oldScaled := mul_le_mul_right vk hOld
  have chain : Γ ⊢[PRAAx] le (ak*(bi*vi)) ((ak*bi)*vk) :=
    le_trans hNew (le_congr (by ipra_ring) (.eqRefl _) oldScaled)
  have cancelled : Γ ⊢[PRAAx] le vi vk := RationalValueBounds.positive_cancel
    (positive_product ak bi hak hbi) (le_congr (by ipra_ring) (.eqRefl _) chain)
  exact le_lt_absurd Fm.bot cancelled hv

/-- A positive old winner at degree k strictly beats every higher degree
at the next actual scale. The comparisons concern the original rational
score codes; their independent decoded denominators are cleared by proof. -/
theorem score_drop (C N E j h i k : PTm n)
    (hOld : Γ ⊢[PRAAx] RationalArgmin.rationalLE (score C N E j h i) (score C N E j h k))
    (hki : Γ ⊢[PRAAx] lt k i)
    (hkpos : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N k)) : Γ ⊢[PRAAx]
    neg (RationalArgmin.rationalLE (score C N E j (succ h) k) (score C N E j (succ h) i)) := by
  refine .impI ?_
  let Δ := RationalArgmin.rationalLE (score C N E j (succ h) k) (score C N E j (succ h) i)::Γ
  have old := GaussianRationalMetric.comparison_to_cleared (Γ := Δ) _ _ _ _ _ _
    (score_represents (Γ := Γ) C N E j h i).wk (score_represents (Γ := Γ) C N E j h k).wk hOld.wk
  have new := GaussianRationalMetric.comparison_to_cleared (Γ := Δ) _ _ _ _ _ _
    (score_represents (Γ := Γ) C N E j (succ h) k).wk
    (score_represents (Γ := Γ) C N E j (succ h) i).wk Prf.hyp0
  have new' := le_congr
    (congrMul (denominator_succ (Γ := Γ) C N E h i).wk (.eqRefl _))
    (congrMul (.eqRefl _) (denominator_succ (Γ := Γ) C N E h k).wk) new
  exact max_drop_contradiction (numerator C N j i) (numerator C N j k)
    (denominator C N E h i) (denominator C N E h k) (unit (four*i)) (unit (four*k))
    (le_congr (by ipra_ring) (.eqRefl _) old)
    (le_congr (by ipra_ring) (.eqRefl _) new')
    (GaussianDominantSyntax.numerator_positive C N j k hkpos).wk
    (denominator_positive (Γ := Γ) C N E h i).wk (scale_strict k i hki).wk

theorem dominant_squared_scale_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (unit (four*var 0) ≐ pw (unit four) (var 0)) := closeUniv 1 (scale_factor _)

theorem dominant_denominator_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (denominator (var 0) (var 1) (var 2) (succ (var 3)) (var 4) ≐
      denominator (var 0) (var 1) (var 2) (var 3) (var 4)*unit (four*var 4)) :=
  closeUniv 5 (denominator_succ _ _ _ _ _)

theorem dominant_strict_scale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 0) (var 1) ⟶ lt (unit (four*var 0)) (unit (four*var 1))) :=
  closeUniv 2 (.impI (scale_strict _ _ Prf.hyp0))

theorem dominant_cleared_max_drop_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 0*var 3) (var 1*var 2) ⟶
      le (var 1*(var 2*var 4)) (var 0*(var 3*var 5)) ⟶
      le one (var 1) ⟶ le one (var 2) ⟶ lt (var 5) (var 4) ⟶ Fm.bot) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (max_drop_contradiction _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk
      Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem dominant_actual_score_drop_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (RationalArgmin.rationalLE
      (score (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      (score (var 0) (var 1) (var 2) (var 3) (var 4) (var 6)) ⟶
      lt (var 6) (var 5) ⟶ le one (GaussianBalancedRadiusSyntax.numerator (var 0) (var 1) (var 6)) ⟶
      neg (RationalArgmin.rationalLE
        (score (var 0) (var 1) (var 2) (var 3) (succ (var 4)) (var 6))
        (score (var 0) (var 1) (var 2) (var 3) (succ (var 4)) (var 5)))) :=
  closeUniv 7 (.impI (.impI (.impI (score_drop _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianDominantScaleArithmetic
