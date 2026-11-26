import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeCofinalSchedule
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeStirlingGridRemainder
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeLogPrimitiveRescale

/-!
# Cofinal comparison for the original positive-argument Raabe quadrature
-/

set_option autoImplicit false
set_option maxHeartbeats 930000

namespace LeanProofs.IPRA.Analysis.GaussianRaabePositiveComparison

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature)
open GaussianNameArithmetic (sum_distance)
open GaussianNamedDifference (difference_distance)
open GaussianPositiveRationalLogarithm (source)
open GaussianRaabeCofinalSchedule (clock clockFor count farStart count_positive far_admitted)
open GaussianRaabeLogPrimitiveCell (primitive)
open GaussianRaabeStirlingRemainder (constantSample)
open GaussianRaabeUnitGridRecurrence (logGammaEvaluator)
open GaussianRaabeUnitGridShift (deviation)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul_canonical positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def valueFor (h N A D : PTm n) : PTm n :=
  quadrature logGammaEvaluator (clockFor h N A D) N A D D zero

def value (h A D : PTm n) : PTm n := valueFor h (count h A D) A D

ipra_subst valueFor

ipra_subst value

private theorem fit (x y V B C h : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (budget : Γ ⊢[PRAAx] le (V*unit h) (C*B)) (e : Γ ⊢[PRAAx] distanceBounded x y V B) :
    Γ ⊢[PRAAx] distanceBounded x y C (unit h) :=
  distance_radius_mono _ _ _ _ _ _ hb (unit_positive h) budget e

private theorem origin_deviation (h N A D w : PTm n) (hs : Γ ⊢[PRAAx] source A D)
    (mesh : Γ ⊢[PRAAx] le (count h A D) N) :
    let p := clockFor h N A D
    Γ ⊢[PRAAx] distanceBounded (deviation p N A D) (constantSample p w) (num 12) (unit h) := by
  let p := clockFor h N A D
  let J := unit h
  let R := farStart h A D
  let near := deviation p N A D
  let far := deviation p N R D
  let prim := primitive p (R*N) (D*N)
  let g := quadrature logGammaEvaluator p N R D D zero
  let e := quadrature GaussianRaabeStirlingMesh.evaluator p N R D D zero
  let alt := qsub g e
  let c := constantSample p w
  have hN := le_trans (count_positive (Γ := Γ) h A D) mesh
  have hR := far_admitted (Γ := Γ) h A D
  have hr := le_trans hs.andE₂ hR
  have hp := unit_positive (Γ := Γ) p
  have hh := unit_positive (Γ := Γ) h
  have hDN := positive_product _ _ hs.andE₂ (positive_product _ _ hs.andE₁ hs.andE₁)
  have hShift : Γ ⊢[PRAAx] le one (GaussianRaabeUnitGridShift.denominator p N A D) :=
    positive_product _ _ (positive_product _ _ hDN hN) hp
  have shift : Γ ⊢[PRAAx] distanceBounded far near (num 3) (unit h) :=
    fit _ _ _ _ _ h hShift (GaussianRaabeCofinalSchedule.shift_budget_for h N A D mesh hs.andE₁ hs.andE₂)
      (GaussianRaabeUnitGridShift.shift_error p N A D J hN hs.andE₁ hs.andE₂)
  have hElement : Γ ⊢[PRAAx] le one (GaussianRaabeStirlingMesh.errorDenominator p N R D) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ hr hs.andE₂) hp)
      (positive_product _ _ RationalAlgebra.two_positive hN)
  have elem : Γ ⊢[PRAAx] distanceBounded e prim (num 6) (unit h) :=
    fit _ _ _ _ _ h hElement (GaussianRaabeCofinalSchedule.elementary_budget_for h N A D mesh hs.andE₂)
      (GaussianRaabeStirlingMesh.primitive_error p N R D hN hs.andE₂ hR)
  have first : Γ ⊢[PRAAx] distanceBounded far alt (num 6) (unit h) :=
    distance_congr (.eqRefl _) (.eqRefl _) (zero_add _ : Γ ⊢[PRAAx] zero+num 6 ≐ num 6) (.eqRefl _)
      (difference_distance g g prim e zero (num 6) (unit h) hh (distance_refl_zero g _ hh)
        (distance_symmetric _ _ _ _ hh elem))
  have second : Γ ⊢[PRAAx] distanceBounded alt c (num 3) (unit h) :=
    fit _ _ _ _ _ h (positive_product _ _ hr hp) (GaussianRaabeCofinalSchedule.remainder_budget_for h N A D)
      (GaussianRaabeStirlingGridRemainder.quadrature_error p N R D w hN hs.andE₂ hR)
  have rest := distance_triangle_same far alt c _ _ _ hh first second
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same near far c _ _ _ hh (distance_symmetric _ _ _ _ hh shift) rest)

theorem observation_for (h N A D w : PTm n) (hs : Γ ⊢[PRAAx] source A D)
    (mesh : Γ ⊢[PRAAx] le (count h A D) N) :
    Γ ⊢[PRAAx] distanceBounded (valueFor h N A D)
      (ap2 GaussianRaabeRightSide.nameF (clockFor h N A D) (GaussianRaabeRightSide.data A D w)) (num 14) (unit h) := by
  let p := clockFor h N A D
  let g := valueFor h N A D
  let d := deviation p N A D
  let c := constantSample p w
  let x := primitive p (A*N) (D*N)
  let y := primitive p A D
  let t := ap2 GaussianRaabeRightSide.nameF p (GaussianRaabeRightSide.data A D w)
  have hN := le_trans (count_positive (Γ := Γ) h A D) mesh
  have hu := unit_positive (Γ := Γ) p
  have hh := unit_positive (Γ := Γ) h
  have gCan : Γ ⊢[PRAAx] GaussianRationalHorner.canonical g := qmul_canonical _ _
  have left : Γ ⊢[PRAAx] qadd x d ≐ g := GaussianRationalLinearProduct.add_sub_right x g gCan
  have e₀ : Γ ⊢[PRAAx] distanceBounded g (qadd x c) (num 12) (unit h) :=
    distance_congr left (.eqRefl _) (zero_add _) (.eqRefl _)
      (sum_distance x x d c zero (num 12) (unit h) hh (distance_refl_zero _ _ hh) (origin_deviation h N A D w hs mesh))
  have budgets := GaussianRaabeCofinalSchedule.endpoint_budgets_for (Γ := Γ) h N A D
  have enlarge : Γ ⊢[PRAAx] le (unit p) (one*(D*unit p)) :=
    le_congr (one_mul _) (one_mul _).eqSymm (mul_le_mul_right (unit p) hs.andE₂)
  have rescale : Γ ⊢[PRAAx] distanceBounded x y one (unit h) :=
    fit _ _ _ _ _ h (positive_product _ _ hs.andE₂ hu) (le_trans budgets.andE₁ enlarge)
      (GaussianRaabeLogPrimitiveRescale.scaled_to_original p N A D hN hs)
  have e₁ : Γ ⊢[PRAAx] distanceBounded (qadd x c) (qadd y c) one (unit h) :=
    distance_congr (.eqRefl _) (.eqRefl _) (add_zero _) (.eqRefl _)
      (sum_distance x y c c one zero (unit h) hh rescale (distance_refl_zero _ _ hh))
  have e₂ : Γ ⊢[PRAAx] distanceBounded t (qadd y c) one (unit h) :=
    fit _ _ _ _ _ h hu (le_congr (.eqRefl _) (one_mul _).eqSymm budgets.andE₂)
      (GaussianRaabeRightSide.sample_error p A D w hs)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same g (qadd x c) t _ _ _ hh e₀
      (distance_triangle_same (qadd x c) (qadd y c) t _ _ _ hh e₁ (distance_symmetric _ _ _ _ hh e₂)))

theorem observation_error (h A D w : PTm n) (hs : Γ ⊢[PRAAx] source A D) :
    Γ ⊢[PRAAx] distanceBounded (value h A D)
      (ap2 GaussianRaabeRightSide.nameF (clock h A D) (GaussianRaabeRightSide.data A D w)) (num 14) (unit h) :=
  observation_for h (count h A D) A D w hs (le_refl _)

end LeanProofs.IPRA.Analysis.GaussianRaabePositiveComparison
