import IPRADerivations.Analysis.GaussianNamedEulerUnitTime
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsLog
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsOrder

/-!
# Widen a certified unit-interval margin

Increasing the margin denominator moves both rational barriers outward.
The original program and its data still satisfy the source judgment.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitTimeMargin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedEulerUnitTime (source source_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianUnitIntervalInputDecoding (lowerPoint upperPoint)
open RationalValueBounds (upper upper_congr upper_of_order upper_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "F" => GaussianEuclideanDistanceName.fraction

private theorem rational_order (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] le (a*d) (c*b)) : Γ ⊢[PRAAx] upper (F a b) (F c d) zero one :=
  upper_congr (fraction_real_part a b hb) (fraction_real_part c d hd) (.eqRefl _) (.eqRefl _)
    (upper_of_order (fstT (fraction a b)) (fstT (fraction c d)) zero one
      (fractions_order a b c d hb hd (le_congr (mul_comm _ _) (.eqRefl _) h)))

theorem observation_widen (q E D : PTm n) (hs : Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source q E)
    (hED : Γ ⊢[PRAAx] le E D) : Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source q D := by
  have hE := hs.andE₂.andE₁
  have hD := le_trans hE hED
  have lo : Γ ⊢[PRAAx] upper (lowerPoint D) (lowerPoint E) zero one :=
    rational_order one D one E hD hE (by ipra_le sl hED)
  have hi : Γ ⊢[PRAAx] upper (upperPoint E) (upperPoint D) zero one := by
    have e := natEq (eq_add_of_le hE)
    have d := natEq (eq_add_of_le hD)
    exact rational_order (monus E one) E (monus D one) D hE hD
      (by ipra_le sl hED with 𝔞(D)*e-𝔞(E)*d)
  have lower := upper_triangle (lowerPoint D) (lowerPoint E) (fstT q) zero one zero one lo hs.andE₂.andE₂.andE₁
  have upper' := upper_triangle (fstT q) (upperPoint E) (upperPoint D) zero one zero one hs.andE₂.andE₂.andE₂ hi
  exact .andI hs.andE₁ (.andI hD (.andI
    (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) lower)
    (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) upper')))

theorem widen (f : PR 2) (x E D : PTm n) (hs : Γ ⊢[PRAAx] source f x E) (hED : Γ ⊢[PRAAx] le E D) :
    Γ ⊢[PRAAx] source f x D := by
  refine .andI hs.andE₁ (.allI ?_)
  have src : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift E) := by
    simpa only [Fm.shift, GaussianNamedEulerUnitTime.subst_source, Syn.shift] using hs.shift
  have radius : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift E) (Syn.shift D) := by
    simpa only [Fm.shift, subst_le, Syn.shift] using hED.shift
  simpa only [GaussianNamedEulerUnitKernel.admissibleSamples, Syn.shift] using
    observation_widen (ap2 f (var 0) (Syn.shift x)) (Syn.shift E) (Syn.shift D)
      (source_at f (var 0) (Syn.shift x) (Syn.shift E) src) radius

theorem double (f : PR 2) (x E : PTm n) (hs : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx] source f x (two*E) :=
  widen f x E (two*E) hs (le_congr (.eqRefl _) (by ipra_ring) (le_add_right E E))

theorem actual_named_unit_interval_margin_widening_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((source f (var 0) (var 1) ⋏ le (var 1) (var 2)) ⟶ source f (var 0) (var 2)) :=
  closeUniv 3 (.impI (widen f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitTimeMargin
