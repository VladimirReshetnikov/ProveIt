import IPRADerivations.Analysis.Trigonometry.GaussianSineReflectionLower
import IPRADerivations.Analysis.Names.GaussianNameReciprocal

/-!
# Transport of finite named apartness certificates

The original apartness observation is taken two dyadic clocks after its
certificate index. The mixed-clock distance to an equivalent name at the
next certificate anchor is at most half the original lower bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedApartnessTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNameReciprocal (anchor apart)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalLowerBounds (lower lower_from_representation lower_to_cleared)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem original_bound_at_doubled_denominator (q h : PTm n)
    (hq : Γ ⊢[PRAAx] GaussianNameReciprocal.lower q (unit h)) :
    Γ ⊢[PRAAx] lower q (two*one) (unit (succ h)) := by
  let a := rawGaussian q
  let d := rawDen q
  have hd := raw_den_positive (Γ := Γ) q
  have clear := lower_to_cleared q a d one (unit h) hd (unit_positive h) (raw_represents q) hq
  have e := natEq (pw_succ (Γ := Γ) two h)
  refine lower_from_representation q a d (two*one) (unit (succ h)) hd (unit_positive (succ h)) (raw_represents q) ?_
  exact le_congr (by ipra_ring) (by unfold unit; apply deriveNat; ipra_simps; rw [e]; ring)
    (mul_le_mul_right (two*two) clear)

theorem transport (f g : PR 2) (h x y : PTm n)
    (ha : Γ ⊢[PRAAx] apart f h x) (eq : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] apart g (succ h) y := by
  let p := anchor h
  let q := anchor (succ h)
  let B := unit (succ h)
  let P := unit p
  let Q := unit q
  have rise : Γ ⊢[PRAAx] le P Q := by
    apply unit_monotone
    unfold p q GaussianNameReciprocal.anchor
    ipra_le 1
  have time : Γ ⊢[PRAAx] p ≐ succ (succ h) := by unfold p GaussianNameReciprocal.anchor; ipra_ring
  have pe : Γ ⊢[PRAAx] P ≐ two*B :=
    (congrAp2 powF time (.eqRefl two)).eqTrans ((pw_succ two (succ h)).eqTrans (mul_comm _ _))
  have e := natEq pe
  have pay : Γ ⊢[PRAAx] le ((P+Q)*B) (one*(P*Q)) := by
    ipra_le 𝔞(B)*sl rise using rw [e]; ring
  have hB := unit_positive (Γ := Γ) (succ h)
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g q y) one B :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) hB pay
      (cross_at f g x y p q eq)
  exact GaussianSineReflectionLower.lower_after_half_error _ _ one B hB
    (original_bound_at_doubled_denominator (ap2 f p x) h ha) near

theorem actual_named_apartness_transport_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((apart f (var 0) (var 1) ⋏ crossEquivalent f g (var 1) (var 2)) ⟶ apart g (succ (var 0)) (var 2)) :=
  closeUniv 3 (.impI (transport f g _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedApartnessTransport
