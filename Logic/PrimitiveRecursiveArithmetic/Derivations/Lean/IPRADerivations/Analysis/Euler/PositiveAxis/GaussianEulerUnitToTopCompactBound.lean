import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitToTopBound
import IPRADerivations.Analysis.Euler.GaussianEulerCompactAdditivity

/-!
# Upper bound on the original compact Euler observation from one

Refine the actual compact sampler to a cell count divisible by its width
numerator. The factorial tail estimate holds on that finer grid. At the
requested compact observation the refinement error and the grid error fit
inside the single requested dyadic tolerance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitToTopCompactBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCompactAdditivity (intervalSource data nameF)
open GaussianEulerCompactModulus (lipschitz)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (mesh quadrature precision)
open GaussianEulerUnitToTopBound (minimumMesh minimumPrecision minimumReference)
open GaussianGammaIntegralCutoffs (tailCoefficient)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem original_refinement (p q H z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hH : Γ ⊢[PRAAx] le one H)
    (hp : Γ ⊢[PRAAx] le (precision q T) p) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF p (H*mesh q (lipschitz R E T) T) a C E (fixedData z B))
      (ap2 nameF q (data z R B a C E T)) (num 3) (unit (q+num 6)) := by
  let L := lipschitz R E T
  let M := mesh q L T
  let u := precision q T
  let S := unit (q+num 6)
  have input := GaussianEulerCompactAdditivity.compact_input z R B a C E T h
  have ha := input.andE₁
  have hE := input.andE₂.andE₁
  have hM := GaussianCompactRiemannName.mesh_positive (Γ := Γ) q L T
  have raw := GaussianCompactRiemannName.quadrature_refinement evaluatorF p u M H a C E L (fixedData z B)
    ha hE hM hH input.andE₂.andE₂.andE₂
  have base : Γ ⊢[PRAAx] le (S*T) (unit u) := GaussianCompactRiemannName.precision_lower q T
  have fine : Γ ⊢[PRAAx] le (S*T) (unit p) := le_trans base (GaussianExponentialReference.unit_monotone hp)
  have budget := GaussianCompactRiemannName.quadrature_budget C E L M (unit p) (unit u) S T
    input.andE₂.andE₂.andE₁ (GaussianCompactRiemannName.mesh_cost q L T) fine base
  have den := positive_product _ _ hE (denominator_positive (E*M) p u (positive_product _ _ hE hM))
  have compare : Γ ⊢[PRAAx] le ((C*rateNumerator (L*C) (E*M) p u)*S)
      (num 3*(E*rateDenominator (E*M) p u)) := budget
  exact distance_congr (.eqRefl _) (GaussianCompactRiemannName.name_at evaluatorF q a C E L T (fixedData z B)).eqSymm
    (.eqRefl _) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ den (unit_positive _) compare raw)

/-- Changing the containing top guard leaves the integration interval
fixed. The two actual samplers have a common fine mesh. -/
theorem original_guard_distance (p z R B a C E T U : PTm n)
    (hT : Γ ⊢[PRAAx] intervalSource z R B a C E T)
    (hU : Γ ⊢[PRAAx] intervalSource z R B a C E U) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a C E T)) (ap2 nameF p (data z R B a C E U))
      (num 6) (unit (p+num 6)) := by
  let M := mesh p (lipschitz R E T) T
  let N := mesh p (lipschitz R E U) U
  let q := precision p T+precision p U
  have toT := original_refinement q p N z R B a C E T hT
    (GaussianCompactRiemannName.mesh_positive _ _ _) (le_add_right _ _)
  have toU := original_refinement q p M z R B a C E U hU
    (GaussianCompactRiemannName.mesh_positive _ _ _) (le_add_left _ _)
  have same := GaussianCompactRiemannName.quadrature_index_congr (Γ := Γ) evaluatorF q (M*N) (N*M)
    a C E (fixedData z B) (LeanProofs.IPRA.mul_comm _ _)
  have den := unit_positive (Γ := Γ) (p+num 6)
  have joined := distance_triangle_same _ _ _ _ _ _ den (distance_symmetric _ _ _ _ den toT)
    (distance_congr same (.eqRefl _) (.eqRefl _) (.eqRefl _) toU)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) joined

theorem original_observation_bound (p z R B C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B E C E T) (hC : Γ ⊢[PRAAx] le one C) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (data z R B E C E T)) (tailCoefficient R*unit p+one) (unit p) := by
  let t := p+num 6
  let L := lipschitz R E T
  let M := mesh p L T
  let J := minimumMesh t R T
  let K := J*M
  let u := precision p T+minimumPrecision t R T
  let q := minimumReference t R
  let y := quadrature evaluatorF u (C*K) E C E (fixedData z B)
  have hM := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p L T
  have hJ : Γ ⊢[PRAAx] le one J := le_add_right _ _
  have left : Γ ⊢[PRAAx] J*one ≐ J := by ipra_ring
  have hK : Γ ⊢[PRAAx] le J K := le_congr left (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl J) hM)
  have base := GaussianEulerUnitToTopBound.original_grid_dyadic_bound t u q C E K T z R B
    (.andI h.andE₁.andE₁ h.andE₁.andE₂.andE₂) h.andE₂.andE₁ hC
    (le_trans (le_add_left C E) h.andE₂.andE₂) hK (le_add_left _ _) (le_refl q)
  have refineGrid := original_refinement u p (C*J) z R B E C E T h (positive_product _ _ hC hJ) (le_add_right _ _)
  have eq : Γ ⊢[PRAAx] quadrature evaluatorF u ((C*J)*M) E C E (fixedData z B) ≐ y :=
    GaussianCompactRiemannName.quadrature_index_congr _ _ _ _ _ _ _ _ (by dsimp only [K]; ipra_ring)
  have closeGrid := distance_symmetric _ _ _ _ (unit_positive t)
    (distance_congr eq (.eqRefl _) (.eqRefl _) (.eqRefl _) refineGrid)
  have joined := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (unit_positive t) (unit_positive t) closeGrid base
  have cost : Γ ⊢[PRAAx] le (num 4*unit p) (unit t) := by
    have four : Γ ⊢[PRAAx] le (num 4) (unit (num 6)) :=
      le_trans (le_of_eq_add (d := num 3) (by ipra_ring)) (RationalClosure.succ_le_two_pow (num 6))
    exact le_congr (.eqRefl _) ((pw_add two p (num 6)).eqTrans (LeanProofs.IPRA.mul_comm _ _)).eqSymm
      (mul_le_mul_right (unit p) four)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive t)) (unit_positive p) _ joined
  ipra_le 𝔞(unit t)*sl cost

theorem actual_original_Euler_upper_compact_observation_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((intervalSource (var 1) (var 2) (var 3) (var 5) (var 4) (var 5) (var 6) ⋏ le one (var 4)) ⟶
      bounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 5) (var 4) (var 5) (var 6)))
        (tailCoefficient (var 2)*unit (var 0)+one) (unit (var 0))) :=
  closeUniv 7 (.impI (original_observation_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitToTopCompactBound
