import IPRADerivations.Analysis.Euler.CompactExhaustion.Tails.GaussianEulerNamedUpperTail

/-!
# Original-cutoff upper-tail budget for the Cauchy comparison

The exact original tailCoefficient is twice the actual factorial
majorant. The original omitted_tail_budget therefore absorbs the
proved named upper tail, preserving precisely its requested ordinary
observation error. The unchanged original upperData program is retained.
This is the upper-tail component of the varying-cutoff comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUpperTailCauchyBudget

open_ipra
open GaussianGammaCompactCutoffSplit (source)
open GaussianEulerNamedUpperTail (point)
open GaussianGammaIntegralCutoffs (tailCoefficient height)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (positive_product qzero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (p k : PTm n) : PTm n := unit p+unit (k+num 6)
def denominator (p k : PTm n) : PTm n := unit (k+num 6)*unit p
ipra_subst numerator
ipra_subst denominator

theorem exact_tail_coefficient (R : PTm n) : Γ ⊢[PRAAx] tailCoefficient R ≐ two*majorant R :=
  (congrMul (pw_succ two R) (.eqRefl (Products.fact R))).eqTrans (by unfold majorant unit; ipra_ring)

theorem upper_tail_cutoff_budget (k A R : PTm n) : Γ ⊢[PRAAx]
    le ((two*majorant R)*unit (k+num 6)) (unit (height k A R)) := by
  have small := mul_le_mul_right (unit (k+num 6)) (le_add_left (Γ := Γ) (tailCoefficient R) A)
  have full := le_of_lt (GaussianGammaIntegralCutoffs.omitted_tail_budget (Γ := Γ) k A R)
  exact le_congr (congrMul (exact_tail_coefficient R) (.eqRefl _)) (.eqRefl _) (le_trans small full)

theorem denominator_positive (p k : PTm n) : Γ ⊢[PRAAx] le one (denominator p k) :=
  positive_product _ _ (unit_positive _) (unit_positive p)

/-- The requested original named observation is bounded by the actual
source cutoff error 2^-(k+6) plus its ordinary observation error 2^-p. -/
theorem original_upper_tail_cauchy_budget (p z R B k j A : PTm n) (h : Γ ⊢[PRAAx] source z R B k j A) : Γ ⊢[PRAAx]
    bounded (point p z R B k j A) (numerator p k) (denominator p k) := by
  have old := GaussianEulerNamedUpperTail.original_named_upper_tail p z R B k j A h
  have cleared := AnalyticNumberTheory.PhiLower.le_mul_mono (upper_tail_cutoff_budget (Γ := Γ) k A R) (le_refl (unit p*unit p))
  have radius : Γ ⊢[PRAAx]
      le ((two*majorant R*unit p+unit (height k A R))*denominator p k)
        (numerator p k*(unit (height k A R)*unit p)) :=
    le_congr (by unfold denominator; ipra_ring) (by unfold numerator; ipra_ring)
      (add_le_add_right (unit (height k A R)*unit (k+num 6)*unit p) cleared)
  exact bounded_radius_mono _ _ _ _ _ (GaussianEulerNamedUpperTail.denominator_positive p k A R) (denominator_positive p k) radius old

theorem original_upper_tail_distance_zero (p z R B k j A : PTm n) (h : Γ ⊢[PRAAx] source z R B k j A) : Γ ⊢[PRAAx]
    distanceBounded (point p z R B k j A) qzero (numerator p k) (denominator p k) :=
  (GaussianReconstructionRoots.distance_zero_iff _ _ _ (denominator_positive p k)).iffMpr (original_upper_tail_cauchy_budget p z R B k j A h)

def output (p z R B k j A : PTm n) : PTm n := pairT (point p z R B k j A)
  (pairT (numerator p k) (pairT (denominator p k) (tailCoefficient R)))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (p z R B k j A : PTm n) : PTm n := PTm.app outputF ![p,z,R,B,k,j,A]
ipra_subst output [tailCoefficient]
theorem program_at (p z R B k j A : PTm n) : Γ ⊢[PRAAx] run p z R B k j A ≐ output p z R B k j A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![p,z,R,B,k,j,A]
theorem returned_point (p z R B k j A : PTm n) : Γ ⊢[PRAAx] fstT (run p z R B k j A) ≐ point p z R B k j A :=
  (program_at p z R B k j A).fstE
theorem returned_tail (p z R B k j A : PTm n) : Γ ⊢[PRAAx] sndT (run p z R B k j A) ≐ pairT (numerator p k) (pairT (denominator p k) (tailCoefficient R)) :=
  (program_at p z R B k j A).sndE
theorem returned_numerator (p z R B k j A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p z R B k j A)) ≐ numerator p k :=
  (returned_tail p z R B k j A).fstE
theorem returned_last (p z R B k j A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p z R B k j A)) ≐ pairT (denominator p k) (tailCoefficient R) :=
  (returned_tail p z R B k j A).sndE
theorem returned_denominator (p z R B k j A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p z R B k j A))) ≐ denominator p k :=
  (returned_last p z R B k j A).fstE
theorem returned_coefficient (p z R B k j A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p z R B k j A))) ≐ tailCoefficient R :=
  (returned_last p z R B k j A).sndE
theorem returned_bound (p z R B k j A : PTm n) (h : Γ ⊢[PRAAx] source z R B k j A) : Γ ⊢[PRAAx]
    bounded (fstT (run p z R B k j A)) (fstT (sndT (run p z R B k j A))) (fstT (sndT (sndT (run p z R B k j A)))) :=
  GaussianRationalReciprocal.bound_congr (returned_point p z R B k j A).eqSymm (returned_numerator p z R B k j A).eqSymm
    (returned_denominator p z R B k j A).eqSymm (original_upper_tail_cauchy_budget p z R B k j A h)

theorem exact_original_tail_factorial_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (tailCoefficient (var 0) ≐ two*majorant (var 0)) := closeUniv 1 (exact_tail_coefficient _)
theorem original_upper_tail_source_cutoff_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le ((two*majorant (var 2))*unit (var 0+num 6)) (unit (height (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (upper_tail_cutoff_budget _ _ _)
theorem original_upper_tail_cauchy_component_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ bounded (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
      (numerator (var 0) (var 4)) (denominator (var 0) (var 4))) :=
  closeUniv 7 (.impI (original_upper_tail_cauchy_budget _ _ _ _ _ _ _ Prf.hyp0))
theorem original_upper_tail_distance_component_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ distanceBounded (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) qzero
      (numerator (var 0) (var 4)) (denominator (var 0) (var 4))) :=
  closeUniv 7 (.impI (original_upper_tail_distance_zero _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_upper_tail_cauchy_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at _ _ _ _ _ _ _)
theorem actual_returned_upper_tail_cauchy_component_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ bounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))
      (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))) :=
  closeUniv 7 (.impI (returned_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUpperTailCauchyBudget
