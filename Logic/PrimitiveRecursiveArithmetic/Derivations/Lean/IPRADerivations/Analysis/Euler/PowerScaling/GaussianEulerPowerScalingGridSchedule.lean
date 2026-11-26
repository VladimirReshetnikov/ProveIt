import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingFiniteBudget
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence

/-!
# A numerical accuracy schedule for the finite power substitution

The mesh controls the quadratic Jacobian remainder. Two computed
queries control the source and image observation errors and keep the
corrected image nodes in their certified compact interval.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingGridSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPowerScalingFiniteBudget (meshCost chartCost observationCost)
open GaussianEulerPowerScalingCell (scaleBound scaleSample eulerBound)
open GaussianEulerPowerScalingFrozenIntegrand (factorBound)
open GaussianEulerPowerChartFrozenKernel (cost)
open GaussianEulerPositivePowerChartImage (query)
open GaussianEulerPositivePowerChartJacobian (curvature)
open GaussianEulerPositivePowerChart (lipschitz)
open GaussianEulerPowerScalingCorrectedQuadrature (gain correctedSum)
open GaussianEulerPowerScalingCompactName (evaluatorF fixedData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCompactRiemannName (quadrature)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B A e f d h L Q S E T a C : PTm n) : Fm PTm n :=
  GaussianEulerPowerScalingParameter.source z R B A e f L Q ⋏
    (GaussianEulerPositivePowerChart.parameters e f d h Q S ⋏ (le one E ⋏ (le one a ⋏ le (a+C) (T*E))))
def meshFactor (s z R B e f d h L Q S E T C : PTm n) : PTm n :=
  (one+(((Q+one)+one)*C)+num 3*meshCost (scaleBound z B e f d h) (eulerBound (L*R) h Q S E T)
    (curvature Q S E T C))*unit s
def count (s z R B e f d h L Q S E T C : PTm n) : PTm n :=
  meshFactor s z R B e f d h L Q S E T C*
    GaussianCompactRiemannName.mesh s (GaussianEulerPowerScalingCompactRate.lipschitz R Q S E T) T
def sourcePrecision (s z R B e f d h L Q S E T C : PTm n) : PTm n :=
  GaussianFastValueCut.exponent
    (num 3*observationCost Q C (scaleBound z B e f d h) (eulerBound (L*R) h Q S E T) (lipschitz Q S E T)) s
def precision (s z R B e f d h L Q S E T C : PTm n) : PTm n :=
  GaussianCompactRiemannName.precision s T+sourcePrecision s z R B e f d h L Q S E T C
def imagePrecision (s z R B e f d h L Q S E T C N : PTm n) : PTm n :=
  GaussianFastValueCut.exponent
    (num 3*chartCost N Q C (factorBound z B e f d h E*cost (L*R) h Q S E T)
      (scaleBound z B e f d h) (eulerBound (L*R) h Q S E T) (lipschitz Q S E T) (gain (L*R) h Q S E T N)+two*N) s

def comparison (s z R B e f d h L Q S E T a C : PTm n) : Fm PTm n :=
  let N := count s z R B e f d h L Q S E T C
  let p := precision s z R B e f d h L Q S E T C
  let k := imagePrecision s z R B e f d h L Q S E T C N
  distanceBounded
    (qmul (fraction e f) (quadrature evaluatorF p N a C E (fixedData z B e f d h S)))
    (qmul (scaleSample p z B e f d h) (correctedSum p k z B e f d h Q S E T a C N)) one (unit s)

theorem mesh_factor_positive (s z R B e f d h L Q S E T C : PTm n) :
    Γ ⊢[PRAAx] le one (meshFactor s z R B e f d h L Q S E T C) := by
  unfold meshFactor
  ipra_le sl (unit_positive s)+
    𝔞((((Q+one)+one)*C)+num 3*meshCost (scaleBound z B e f d h) (eulerBound (L*R) h Q S E T) (curvature Q S E T C))*𝔞(unit s)

theorem mesh_factor_le_count (s z R B e f d h L Q S E T C : PTm n) :
    Γ ⊢[PRAAx] le (meshFactor s z R B e f d h L Q S E T C) (count s z R B e f d h L Q S E T C) := by
  unfold count
  ipra_le 𝔞(meshFactor s z R B e f d h L Q S E T C)*sl
    (GaussianCompactRiemannName.mesh_positive s (GaussianEulerPowerScalingCompactRate.lipschitz R Q S E T) T)

theorem original_scheduled_distance (s z R B A e f d h L Q S E T a C : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a C) :
    Γ ⊢[PRAAx] comparison s z R B e f d h L Q S E T a C := by
  unfold comparison
  let N := count s z R B e f d h L Q S E T C
  let p := precision s z R B e f d h L Q S E T C
  let k := imagePrecision s z R B e f d h L Q S E T C N
  let V := curvature Q S E T C
  let M := scaleBound z B e f d h
  let J := eulerBound (L*R) h Q S E T
  let H := lipschitz Q S E T
  let G := gain (L*R) h Q S E T N
  let A₀ := factorBound z B e f d h E*cost (L*R) h Q S E T
  let Pcost := observationCost Q C M J H
  let Kcost := chartCost N Q C A₀ M J H G
  let F := meshFactor s z R B e f d h L Q S E T C
  have hsUnit := unit_positive (Γ := Γ) s
  have hF : Γ ⊢[PRAAx] le F N := mesh_factor_le_count _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hN : Γ ⊢[PRAAx] le one N := le_trans (mesh_factor_positive _ _ _ _ _ _ _ _ _ _ _ _ _ _) hF
  have step : Γ ⊢[PRAAx] le (((Q+one)+one)*C) (a*N) := by
    have upper : Γ ⊢[PRAAx] le (((Q+one)+one)*C) F := by
      unfold F meshFactor
      ipra_le 𝔞(((Q+one)+one)*C)*sl hsUnit+𝔞(unit s)+𝔞(num 3*meshCost M J V*unit s)
    exact le_trans (le_trans upper hF) (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right N hs.andE₂.andE₂.andE₂.andE₁))
  have hk : Γ ⊢[PRAAx] le ((num 3*Kcost+two*N)*unit s) (unit k) := GaussianFastValueCut.query_budget _ _
  have tilt : Γ ⊢[PRAAx] le (two*N) (unit (query k h Q E T)) := by
    have before : Γ ⊢[PRAAx] le (two*N) ((num 3*Kcost+two*N)*unit s) := by
      ipra_le 𝔞(two*N)*sl hsUnit+𝔞(num 3*Kcost*unit s)
    exact le_trans (le_trans before hk) (GaussianExponentialReference.unit_monotone
      (GaussianEulerPositivePowerChartImage.query_later k h Q E T))
  have current : Γ ⊢[PRAAx] GaussianEulerPowerScalingFiniteSubstitution.source k z R B A e f d h L Q S E T a C N :=
    .andI hs.andE₁ (.andI (.andI (.andI hs.andE₂.andE₁
      (.andI hs.andE₂.andE₂.andE₁ (.andI hs.andE₂.andE₂.andE₂.andE₁ (.andI hs.andE₂.andE₂.andE₂.andE₂ hN)))) step) tilt)
  have hm₀ : Γ ⊢[PRAAx] le (num 3*meshCost M J V*unit s) F := by
    unfold F meshFactor
    ipra_le 𝔞((one+(((Q+one)+one)*C))*unit s)
  have hm := le_trans hm₀ hF
  have base := GaussianFastValueCut.query_budget (Γ := Γ) (num 3*Pcost) s
  have hp : Γ ⊢[PRAAx] le (num 3*Pcost*unit s) (unit p) :=
    le_trans base (GaussianExponentialReference.unit_monotone (le_add_left _ _))
  have hkc : Γ ⊢[PRAAx] le (num 3*Kcost*unit s) (unit k) :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right _ (two*N*unit s))) hk
  have clear := GaussianEulerPowerScalingFiniteBudget.separated_radius_budget N (unit p) (unit k)
    Q C A₀ M J V H G (unit s) hm hkc hp
  have hDen : Γ ⊢[PRAAx] le one (GaussianEulerPowerScalingFiniteBudget.separatedDenominator N (unit p) (unit k)) :=
    positive_product _ _ (positive_product _ _ hN (unit_positive p)) (unit_positive k)
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ one (unit s)
    hDen hsUnit
    (le_congr (.eqRefl _) (by ipra_ring) clear)
    (GaussianEulerPowerScalingFiniteBudget.original_separated_budget p k z R B A e f d h L Q S E T a C N current)

def namedComparison (s z R B e f d h L Q S E T a C : PTm n) : Fm PTm n :=
  let N := count s z R B e f d h L Q S E T C
  let p := precision s z R B e f d h L Q S E T C
  let k := imagePrecision s z R B e f d h L Q S E T C N
  distanceBounded
    (qmul (fraction e f) (ap2 GaussianEulerPowerScalingCompactName.nameF s
      (GaussianEulerPowerScalingCompactName.data z R B e f d h Q S a C E T)))
    (qmul (scaleSample p z B e f d h) (correctedSum p k z B e f d h Q S E T a C N)) (Q+one) (unit s)

theorem original_scheduled_name_distance (s z R B A e f d h L Q S E T a C : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S E T a C) :
    Γ ⊢[PRAAx] namedComparison s z R B e f d h L Q S E T a C := by
  let x := fixedData z B e f d h S
  let H := GaussianEulerPowerScalingCompactRate.lipschitz R Q S E T
  let M := meshFactor s z R B e f d h L Q S E T C
  let p := precision s z R B e f d h L Q S E T C
  have cert := hs.andE₁.andE₁.andE₁.andE₂.andE₁
  have hE := hs.andE₂.andE₂.andE₁
  have he := hs.andE₂.andE₂.andE₂.andE₁
  have upper := le_congr (.eqRefl _) (mul_comm T E) hs.andE₂.andE₂.andE₂.andE₂
  have src : Γ ⊢[PRAAx] GaussianEulerPowerScalingCompactName.source z R B e f d h Q S a C E T :=
    .andI (.andI (.andI cert.andE₁ (.andI hE cert.andE₂)) (.andI he upper)) hs.andE₂.andE₁
  have compact := GaussianEulerPowerScalingCompactName.compact_input _ _ _ _ _ _ _ _ _ _ _ _ _ src
  have refineGrid := GaussianCompactMeshIndependence.arbitrary_refinement evaluatorF s p M a C E H T x compact
    (mesh_factor_positive _ _ _ _ _ _ _ _ _ _ _ _ _ _) (le_add_right _ _)
  have hL := unit_positive (Γ := Γ) (s+num 6)
  have later := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ one (unit s) hL (unit_positive s)
    (le_congr (.eqRefl _) (by ipra_ring) (GaussianCompactRiemannName.dyadic_six_lower s)) refineGrid
  have other := GaussianCompactRiemannName.name_at (Γ := Γ) evaluatorF s a C E H T x
  have first := GaussianRationalDistanceOrder.distance_congr (.eqRefl _) other.eqSymm (.eqRefl _) (.eqRefl _) later
  have rate := GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ (unit_positive s) first
  have bound := GaussianEulerExponentCompactBounds.fraction_bound e f Q hs.andE₂.andE₁.andE₁.andE₂
    hs.andE₂.andE₁.andE₂.andE₂.andE₂.andE₁
  have scale := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (fraction e f) _ _).eqSymm (by ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (unit_positive s) bound rate)
  exact GaussianRationalDistanceOrder.distance_triangle_same _ _ _ Q one _ (unit_positive s) scale
    (original_scheduled_distance s z R B A e f d h L Q S E T a C hs)

theorem actual_original_scheduled_power_scaling_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
      (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
        (var 11) (var 12) (var 13) (var 14) (var 15) ⟶
      comparison (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
        (var 11) (var 12) (var 13) (var 14) (var 15)) :=
  closeUniv 16 (.impI (original_scheduled_distance _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_scheduled_compact_power_scaling_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
      (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
        (var 11) (var 12) (var 13) (var 14) (var 15) ⟶
      namedComparison (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
        (var 11) (var 12) (var 13) (var 14) (var 15)) :=
  closeUniv 16 (.impI (original_scheduled_name_distance _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingGridSchedule
