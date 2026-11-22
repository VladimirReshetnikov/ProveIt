import IPRADerivations.Analysis.GaussianRationalLowerBounds
import IPRADerivations.Analysis.GaussianCoordinateRadius

/-!
# Exact lower bounds from finite Gaussian rational observations

A rational point within `A/B` of one has norm at least `1-A/B` for
`A≤B`. Dividing a product lower bound by a fractional bound on the
other factor preserves the exact fraction. Both results use the
original Gaussian norm and rational codes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalLowerPerturbation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalLowerBounds (lower lower_from_representation lower_to_cleared)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded bounded_difference_iff bounded_to_cleared)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRationalL1 (rawDen rawGaussian raw_represents raw_den_positive)
open GaussianRootAlgebra (sub re_sub re_scale re_one)
open ComplexLogarithmRemainder (re im normSq scale oneCode)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_tri)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem lower_near_unit (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (h : Γ ⊢[PRAAx] distanceBounded q qone A B) :
    Γ ⊢[PRAAx] lower q (monus B A) B := by
  let D := rawDen q
  let t := rawGaussian q
  let u := re t
  let v := re (sub (scale D oneCode) t)
  have hD := raw_den_positive (Γ := Γ) q
  have diff := (bounded_difference_iff qone q (scale D oneCode) t D A B hD hB
    (qone_represents_scaled D) (raw_represents q)).iffMp
      (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hB h)
  have coordinate : Γ ⊢[PRAAx] le (B*zabs v) (A*D) :=
    (GaussianCoordinateRadius.native_coordinates _ A B D diff).andE₁
  have d : ZT.toZ Γ (ZT.ofNat D) = ZT.toZ Γ u + ZT.toZ Γ v := by
    dsimp only [u,v]
    rw [ZT.toZ_ofNat,re_sub,re_scale,re_one]
    ring
  have sum : Γ ⊢[PRAAx] le D (zabs u+zabs v) :=
    le_congr (GaussianL1.abs_ofNat D) (.eqRefl _) (zabs_tri d)
  have scaleSum := le_mul_mono (le_refl B) sum
  have compare := le_trans (le_congr (.eqRefl _) (mul_add _ _ _) scaleSum)
    (add_le_add₂ (le_refl (B*zabs u)) coordinate)
  have step : Γ ⊢[PRAAx] le (D*monus B A) (B*zabs u) := by
    apply le_of_add_le_add_right (c := A*D)
    have e := natEq (eq_add_of_le hAB)
    exact le_congr (by
      apply deriveNat
      ipra_simps
      linear_combination 𝔞(D)*e) (.eqRefl _) compare
  have lowSq := le_mul_mono step step
  have uSq : Γ ⊢[PRAAx] le (zabs u*zabs u) (normSq t) :=
    le_congr (.eqRefl _) (GaussianCoordinateRadius.native_squared t).eqSymm (le_add_right _ _)
  exact lower_from_representation q t D (monus B A) B hD hB (raw_represents q)
    (le_trans (le_congr (by ipra_ring) (by ipra_ring) lowSq) (le_mul_mono (le_refl (B*B)) uSq))

theorem fractional_factor_lower (q r C D A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] lower (qmul q r) C D) (hr : Γ ⊢[PRAAx] bounded r A B) :
    Γ ⊢[PRAAx] lower q (C*B) (D*A) := by
  let E := rawDen q
  let F := rawDen r
  let u := rawGaussian q
  let v := rawGaussian r
  have e := raw_den_positive (Γ := Γ) q
  have f := raw_den_positive (Γ := Γ) r
  have mul := GaussianRationalHorner.qmul_represents q r u v E F e f (raw_represents q) (raw_represents r)
  have first := lower_to_cleared _ _ _ _ _ (positive_product E F e f) hD mul h
  have last := bounded_to_cleared r v F A B f hB (raw_represents r) hr
  have norm := natEq (ComplexLogarithmRemainder.normSq_mul (Γ := Γ) u v)
  have a : Γ ⊢[PRAAx] le ((F*F)*((C*B)*(C*B)*(E*E))) ((D*D*normSq u)*(B*B*normSq v)) := by
    apply le_congr (by ipra_ring) ?_ (mul_le_mul_right (B*B) first)
    apply deriveNat
    ipra_simps
    rw [norm]
    ring
  have b : Γ ⊢[PRAAx] le ((D*D*normSq u)*(B*B*normSq v)) ((F*F)*((D*A)*(D*A)*normSq u)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (D*D*normSq u) last)
  exact lower_from_representation q u E (C*B) (D*A) e (positive_product _ _ hD hA) (raw_represents q)
    (RationalValueBounds.positive_cancel (positive_product _ _ f f) (le_trans a b))

theorem original_rational_exact_lower_near_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ le (var 1) (var 2) ⟶ distanceBounded (var 0) qone (var 1) (var 2) ⟶
      lower (var 0) (monus (var 2) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (lower_near_unit _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_rational_fractional_factor_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 3) ⋏ (le one (var 4) ⋏ le one (var 5))) ⟶
      lower (qmul (var 0) (var 1)) (var 2) (var 3) ⟶ bounded (var 1) (var 4) (var 5) ⟶
      lower (var 0) ((var 2)*(var 5)) ((var 3)*(var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (fractional_factor_lower _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂.andE₁ hyp2.andE₂.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalLowerPerturbation
