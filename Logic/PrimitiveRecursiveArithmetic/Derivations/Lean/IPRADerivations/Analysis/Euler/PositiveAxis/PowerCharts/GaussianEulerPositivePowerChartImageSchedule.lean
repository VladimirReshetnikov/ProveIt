import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartImageBudget
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingGridSchedule

/-!
# A source-derived count and clocks for the corrected image integral

A single higher precision is passed to the existing physical-grid
schedule. The count, both original clocks and the auxiliary lattice
clock then meet every corrected image error budget under the original
compact input hypotheses.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPowerScalingGridSchedule (count precision imagePrecision meshFactor mesh_factor_le_count)
open GaussianEulerPositivePowerChartImageBudget (meshBudget tiltBudget observationBudget rowBudget)
open GaussianEulerPositivePowerChartImageName (panelTop observation)
open GaussianEulerPositivePowerChartImage (query query_later)
open GaussianEulerPowerScalingCorrectedQuadrature (correctedSum)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "source" => GaussianEulerPowerScalingGridSchedule.source

def boost (R h Q S E T C : PTm n) : PTm n :=
  one+meshBudget R h Q S E T C+tiltBudget R h Q S E T+observationBudget Q S E T
def target (s R h Q S E T C : PTm n) : PTm n := exponent (boost R h Q S E T C) s
def latticeClock (s t Q S E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.precision s (panelTop Q S E T)+t

theorem target_later (s R h Q S E T C : PTm n) : Γ ⊢[PRAAx] le s (target s R h Q S E T C) :=
  le_add_right _ _

private theorem count_later (t z R B e f d h L Q S E T C : PTm n) :
    Γ ⊢[PRAAx] le (unit t) (count t z R B e f d h L Q S E T C) := by
  have base : Γ ⊢[PRAAx] le (unit t) (meshFactor t z R B e f d h L Q S E T C) := by
    unfold meshFactor
    exact le_of_eq_add (d := ((((Q+one)+one)*C)+LeanProofs.IPRA.PTm.num 3*
      GaussianEulerPowerScalingFiniteBudget.meshCost (GaussianEulerPowerScalingCell.scaleBound z B e f d h)
        (GaussianEulerPowerScalingCell.eulerBound (L*R) h Q S E T) (GaussianEulerPositivePowerChartJacobian.curvature Q S E T C))*unit t)
      (by ipra_ring)
  exact le_trans base (mesh_factor_le_count _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem scheduled_finite_source (t z R B A e f d h L Q S E T a C : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a C) :
    let N := count t z R B e f d h L Q S E T C
    let k := imagePrecision t z R B e f d h L Q S E T C N
    Γ ⊢[PRAAx] GaussianEulerPowerScalingFiniteSubstitution.source k z R B A e f d h L Q S E T a C N := by
  dsimp only
  let F := meshFactor t z R B e f d h L Q S E T C
  let N := count t z R B e f d h L Q S E T C
  let k := imagePrecision t z R B e f d h L Q S E T C N
  have hU := unit_positive (Γ := Γ) t
  have hF : Γ ⊢[PRAAx] le F N := mesh_factor_le_count _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hN : Γ ⊢[PRAAx] le one N := le_trans hU (count_later _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  have hrel : Γ ⊢[PRAAx] le (((Q+one)+one)*C) (a*N) := by
    have upper : Γ ⊢[PRAAx] le (((Q+one)+one)*C) F := by
      unfold F meshFactor
      ipra_le 𝔞(((Q+one)+one)*C)*sl hU+
        𝔞(unit t)+𝔞(LeanProofs.IPRA.PTm.num 3*GaussianEulerPowerScalingFiniteBudget.meshCost
          (GaussianEulerPowerScalingCell.scaleBound z B e f d h)
          (GaussianEulerPowerScalingCell.eulerBound (L*R) h Q S E T)
          (GaussianEulerPositivePowerChartJacobian.curvature Q S E T C)*unit t)
    exact le_trans (le_trans upper hF)
      (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right N hs.andE₂.andE₂.andE₂.andE₁))
  have ht : Γ ⊢[PRAAx] le (two*N) (unit k) := by
    unfold k imagePrecision
    refine le_trans ?_ (GaussianFastValueCut.query_budget _ _)
    exact le_trans (le_congr (one_mul (two*N)) (mul_comm (unit t) (two*N)) (mul_le_mul_right (two*N) hU))
      (mul_le_mul_right (unit t) (le_add_left _ _))
  exact .andI hs.andE₁ (.andI (.andI (.andI hs.andE₂.andE₁
    (.andI hs.andE₂.andE₂.andE₁ (.andI hs.andE₂.andE₂.andE₂.andE₁ (.andI hs.andE₂.andE₂.andE₂.andE₂ hN)))) hrel)
      (le_trans ht (unit_monotone (query_later k h Q E T))))

theorem scheduled_corrected_source (t z R B A e f d h L Q S E T a C : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a C) :
    let N := count t z R B e f d h L Q S E T C
    let k := imagePrecision t z R B e f d h L Q S E T C N
    Γ ⊢[PRAAx] GaussianEulerPowerScalingCorrectedQuadrature.source k z (L*R) B e f d h Q S E T a C N := by
  have scheduled := scheduled_finite_source t z R B A e f d h L Q S E T a C hs
  have atScale := GaussianEulerPowerScalingParameter.original_rescaled_source z R B A e f L Q hs.andE₁
  exact .andI atScale.andE₁.andE₂.andE₁ (.andI scheduled.andE₂.andE₁.andE₁ scheduled.andE₂.andE₂)

theorem scheduled_row_budget (s t z R B e f d h L Q S E T C : PTm n)
    (hl : Γ ⊢[PRAAx] le (target s (L*R) h Q S E T C) t) :
    let N := count t z R B e f d h L Q S E T C
    let p := precision t z R B e f d h L Q S E T C
    let k := imagePrecision t z R B e f d h L Q S E T C N
    let q := latticeClock s t Q S E T
    Γ ⊢[PRAAx] rowBudget s p q k (L*R) h Q S E T C N := by
  dsimp only
  let R' := L*R
  let N := count t z R B e f d h L Q S E T C
  let p := precision t z R B e f d h L Q S E T C
  let k := imagePrecision t z R B e f d h L Q S E T C N
  let q := latticeClock s t Q S E T
  let F := boost R' h Q S E T C
  let V := unit s
  have base : Γ ⊢[PRAAx] le (F*V) (unit t) :=
    le_trans (GaussianFastValueCut.query_budget _ _) (unit_monotone hl)
  have meshBase : Γ ⊢[PRAAx] le (meshBudget R' h Q S E T C) F := by
    unfold F boost
    ipra_le 1+𝔞(tiltBudget R' h Q S E T)+𝔞(observationBudget Q S E T)
  have chartBase : Γ ⊢[PRAAx] le (tiltBudget R' h Q S E T) F := by
    unfold F boost
    ipra_le 1+𝔞(meshBudget R' h Q S E T C)+𝔞(observationBudget Q S E T)
  have sampleBase : Γ ⊢[PRAAx] le (observationBudget Q S E T) F := le_add_left _ _
  have meshLater : Γ ⊢[PRAAx] le (unit t) N := count_later _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have pLater : Γ ⊢[PRAAx] le t p := le_trans (le_of_eq_add
    (d := T+LeanProofs.IPRA.PTm.num 6) (by unfold GaussianCompactRiemannName.precision; ipra_ring)) (le_add_right _ _)
  have kLater : Γ ⊢[PRAAx] le t k := le_add_right _ _
  have qLater : Γ ⊢[PRAAx] le t q := le_add_left _ _
  exact .andI (le_trans (le_trans (mul_le_mul_right V meshBase) base) meshLater)
    (.andI (le_trans (le_trans (mul_le_mul_right V chartBase) base) (unit_monotone (le_trans kLater (query_later k h Q E T))))
      (.andI (le_trans (le_trans (mul_le_mul_right V sampleBase) base) (unit_monotone pLater))
        (le_trans (le_trans (mul_le_mul_right V sampleBase) base) (unit_monotone qLater))))

def distanceAt (s t z R B e f d h L Q S E T a C : PTm n) : Fm PTm n :=
  let N := count t z R B e f d h L Q S E T C
  let p := precision t z R B e f d h L Q S E T C
  let k := imagePrecision t z R B e f d h L Q S E T C N
  distanceBounded (observation s k z (L*R) B e f d h Q S E T a C N) (correctedSum p k z B e f d h Q S E T a C N)
    two (unit s)

theorem original_later_scheduled_ordinary_image (s t z R B A e f d h L Q S E T a C : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a C)
    (hl : Γ ⊢[PRAAx] le (target s (L*R) h Q S E T C) t) :
    Γ ⊢[PRAAx] distanceAt s t z R B e f d h L Q S E T a C := by
  let N := count t z R B e f d h L Q S E T C
  let p := precision t z R B e f d h L Q S E T C
  let k := imagePrecision t z R B e f d h L Q S E T C N
  let q := latticeClock s t Q S E T
  exact GaussianEulerPositivePowerChartImageBudget.original_dyadic_named_quadrature s p q k z (L*R) B e f d h Q S E T a C N
    (scheduled_corrected_source t z R B A e f d h L Q S E T a C hs) (le_add_right _ _)
    (scheduled_row_budget s t z R B e f d h L Q S E T C hl)

def distance (s z R B e f d h L Q S E T a C : PTm n) : Fm PTm n :=
  distanceAt s (target s (L*R) h Q S E T C) z R B e f d h L Q S E T a C

theorem original_scheduled_ordinary_image (s z R B A e f d h L Q S E T a C : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a C) :
    Γ ⊢[PRAAx] distance s z R B e f d h L Q S E T a C :=
  original_later_scheduled_ordinary_image s _ z R B A e f d h L Q S E T a C hs (le_refl _)

theorem actual_original_later_scheduled_ordinary_image_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 17
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
      (var 12) (var 13) (var 14) (var 15) (var 16) ⋏
        le (target (var 0) (var 10*var 3) (var 9) (var 11) (var 12) (var 13) (var 14) (var 16)) (var 1)) ⟶
      distanceAt (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
        (var 12) (var 13) (var 14) (var 15) (var 16)) :=
  closeUniv 17 (.impI (original_later_scheduled_ordinary_image _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_scheduled_ordinary_image_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
      (var 11) (var 12) (var 13) (var 14) (var 15) ⟶
      distance (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
        (var 11) (var 12) (var 13) (var 14) (var 15)) :=
  closeUniv 16 (.impI (original_scheduled_ordinary_image _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageSchedule
