import IPRADerivations.Analysis.Euler.CompactExhaustion.Tails.GaussianEulerCompactUpperTail
import IPRADerivations.Analysis.Gamma.Integrals.CompactQuadrature.GaussianGammaCompactCutoffGeometry
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactModulus
import IPRADerivations.Analysis.Euler.Integration.Decay.CompactBounds.GaussianEulerDecayCompactAntiderivative

/-!
# Native budgets for actual upper-tail compact-name observations

The literal original finite upper-tail denominator is retained. Original
mesh and sample schedules give a computed precision-independent error
coefficient. The encoded upper interval also satisfies the genuine mesh
step guard. No bound on an output name is assumed here.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUpperTailNameBudget

open_ipra
open GaussianEulerHalfDecayTailBound (tailNumerator tailDenominator)
open GaussianEulerUpperTailScalar (budget)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactCutoffGeometry (upperWidth delta)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (mesh precision)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def halfCost (C : PTm n) : PTm n := num 3*C*C+C+num 20
def errorCost (R C : PTm n) : PTm n := C*budget R+majorant R*halfCost C
def finiteNumerator (p s N L C E R : PTm n) : PTm n :=
  (C*budget R)*tailDenominator p s N L E+(majorant R*tailNumerator p s N L C E)*(E*unit p)
def finiteDenominator (p s N L E : PTm n) : PTm n := (E*unit p)*tailDenominator p s N L E
ipra_subst halfCost
ipra_subst errorCost

theorem enlarged_mesh_lower (s N E : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le (unit s) N) : Γ ⊢[PRAAx]
    le (unit s) (two*E*E*N) := by
  have factor := positive_product (Γ := Γ) _ _ (positive_product _ _ (le_succ_self one) hE) hE
  exact le_trans hN (le_congr (one_mul N) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono factor (le_refl N)))

theorem enlarged_precision_lower (p s E : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hp : Γ ⊢[PRAAx] le (unit s) (unit p)) : Γ ⊢[PRAAx]
    le (unit s) (E*unit p) :=
  le_trans hp (le_congr (one_mul _) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono hE (le_refl (unit p))))

/-- Actual finite half-decay error is at most 2/2^L+halfCost(C)/2^s. -/
theorem half_budget (p s N L C E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le (unit s) N) (hp : Γ ⊢[PRAAx] le (unit s) (unit p)) : Γ ⊢[PRAAx]
    le (tailNumerator p s N L C E*(unit L*unit s))
      ((two*unit s+halfCost C*unit L)*tailDenominator p s N L E) := by
  have hn := enlarged_mesh_lower s N E hE hN
  have hu := enlarged_precision_lower p s E hE hp
  unfold tailNumerator tailDenominator halfCost GaussianNameRingLaws.three
  ipra_le (3*𝔞(C)*𝔞(C)*𝔞(unit p)*𝔞(unit s)*𝔞(unit L)*𝔞(unit L))*sl hn+
    (2*𝔞(C)*𝔞(E)*𝔞(N)*𝔞(unit s)*𝔞(unit L)*𝔞(unit L))*sl hu

/-- The original Euler finite bound is at most 2M/2^L+K/2^s,
with the actual internally computed K and all original denominators. -/
theorem finite_budget (p s N L C E R : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le (unit s) N) (hp : Γ ⊢[PRAAx] le (unit s) (unit p)) : Γ ⊢[PRAAx]
    le (finiteNumerator p s N L C E R*(unit L*unit s))
      ((two*majorant R*unit s+errorCost R C*unit L)*finiteDenominator p s N L E) := by
  have half := half_budget p s N L C E hE hN hp
  have hu := enlarged_precision_lower p s E hE hp
  unfold finiteNumerator finiteDenominator errorCost
  ipra_le (𝔞(C)*𝔞(budget R)*𝔞(tailDenominator p s N L E)*𝔞(unit L))*sl hu+
    (𝔞(majorant R)*𝔞(E)*𝔞(unit p))*sl half

theorem denominator_positive (p s N L E : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (finiteDenominator p s N L E) :=
  positive_product _ _ (positive_product _ _ hE (unit_positive p))
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _
      (positive_product _ _ (positive_product _ _ (le_succ_self one) hE) hE) hN) (unit_positive p)) (unit_positive s)) (unit_positive L))

theorem mesh_unit_lower (s L T : PTm n) : Γ ⊢[PRAAx] le (unit s) (mesh s L T) := by
  have later := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ) s (s+num 6) (le_add_right _ _)
  have factor := AnalyticNumberTheory.PhiLower.le_mul_mono (Γ := Γ) (le_refl (unit (s+num 6))) (le_add_right one (L*T*T))
  exact le_trans later (le_congr (by ipra_ring) (.eqRefl _) factor)

theorem precision_later (s T : PTm n) : Γ ⊢[PRAAx] le s (precision s T) :=
  le_trans (le_add_right s T) (le_add_right _ (num 6))
theorem precision_unit_lower (s T : PTm n) : Γ ⊢[PRAAx] le (unit s) (unit (precision s T)) :=
  GaussianExponentialReference.unit_monotone (precision_later s T)

theorem lipschitz_positive (R E T : PTm n) : Γ ⊢[PRAAx] le one (GaussianEulerCompactModulus.lipschitz R E T) :=
  positive_product _ _ (GaussianFactorBudget.power_positive (num 3) _ (le_of_eq_add (d := two) (by ipra_ring)))
    (le_congr (.eqRefl _) (add_comm _ _) (le_add_right one ((R+one)*E)))

theorem upper_width_bound (k j A R : PTm n) (h : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    le (upperWidth k j A R) (etaDen j A R*top j A R) := by
  have low : Γ ⊢[PRAAx] le (two*delta k j) (top j A R) :=
    le_congr (.eqRefl _) (GaussianGammaCompactCutoffGeometry.top_refinement k j A R h).eqSymm (le_add_left _ _)
  exact AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (etaDen j A R)) low

theorem original_mesh_step (s k j A R : PTm n) (h : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    le (upperWidth k j A R) ((two*etaDen j A R)*mesh s (GaussianEulerCompactModulus.lipschitz R (etaDen j A R) (top j A R)) (top j A R)) := by
  let E := etaDen j A R
  let L := GaussianEulerCompactModulus.lipschitz R E (top j A R)
  let N := mesh s L (top j A R)
  have old := GaussianEulerDecayCompactAntiderivative.mesh_covers_step s (upperWidth k j A R) E L (top j A R)
    (upper_width_bound k j A R h) (lipschitz_positive R E (top j A R))
  exact le_trans old (le_of_eq_add (d := E*N) (by ipra_ring))

def errorCostF : PR 2 := PTm.toPR (errorCost (var 0) (var 1))
theorem error_cost_at (R C : PTm n) : Γ ⊢[PRAAx] ap2 errorCostF R C ≐ errorCost R C := by
  simpa [errorCostF,ap2] using toPR_eq (Γ := Γ) (errorCost (var 0) (var 1) : PTm 2) ![R,C]

theorem actual_half_tail_cofinal_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 5) ⋏ (le (unit (var 1)) (var 2) ⋏ le (unit (var 1)) (unit (var 0)))) ⟶
      le (tailNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)*(unit (var 3)*unit (var 1)))
        ((two*unit (var 1)+halfCost (var 4)*unit (var 3))*tailDenominator (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (half_budget _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_Euler_tail_cofinal_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 5) ⋏ (le (unit (var 1)) (var 2) ⋏ le (unit (var 1)) (unit (var 0)))) ⟶
      le (finiteNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)*(unit (var 3)*unit (var 1)))
        ((two*majorant (var 6)*unit (var 1)+errorCost (var 6) (var 4)*unit (var 3))*finiteDenominator (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 7 (.impI (finite_budget _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem original_upper_interval_actual_mesh_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 1) (var 2) ⟶ le (upperWidth (var 1) (var 2) (var 3) (var 4))
      ((two*etaDen (var 2) (var 3) (var 4))*mesh (var 0)
        (GaussianEulerCompactModulus.lipschitz (var 4) (etaDen (var 2) (var 3) (var 4)) (top (var 2) (var 3) (var 4)))
        (top (var 2) (var 3) (var 4)))) := closeUniv 5 (.impI (original_mesh_step _ _ _ _ _ Prf.hyp0))
theorem actual_original_compact_schedules_cofinal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (unit (var 0)) (mesh (var 0) (var 1) (var 2)) ⋏ le (unit (var 0)) (unit (precision (var 0) (var 2)))) :=
  closeUniv 3 (.andI (mesh_unit_lower _ _ _) (precision_unit_lower _ _))
theorem actual_upper_tail_error_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 errorCostF (var 0) (var 1) ≐ errorCost (var 0) (var 1)) := closeUniv 2 (error_cost_at _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerUpperTailNameBudget
