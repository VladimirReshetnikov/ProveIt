import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsGridBudget
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsNormalizedGrid
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsEndpointRescale

/-!
# Actual compact Euler integration by parts with nonzero boundaries

The original normalized quadratures on any positive rational compact
interval are compared to the actual original shifted Euler observations
at its two true endpoints. A computed mesh and three independent row
query budgets pay the telescope, normalization and endpoint recoding
errors. Neither boundary is assumed small or zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsCompact

open_ipra
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianEulerIntegrationByPartsLinear (primitive)
open GaussianEulerIntegrationByPartsGrid (endpoint operatorF)
open GaussianEulerIntegrationByPartsNormalizedGrid (normalized)
open GaussianEulerIntegrationByPartsParameterShiftObservation (primitiveCost)
open GaussianEulerIntegrandName (sample fixedData)
open GaussianGammaEulerHeadShift (shifted)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub qnegative)
open GaussianRationalReciprocal (bound_congr bounded_negative)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a C E T : PTm n) : Fm PTm n := intervalSource z R B a C E T ⋏ le one C
def endpointCost (R E T : PTm n) : PTm n := two*(num 6*T+primitiveCost R E T)
def minimumObservation (t R E T N : PTm n) : PTm n :=
  GaussianEulerIntegrationByPartsGridBudget.minimumPrecision t R E T N+
    GaussianFastValueCut.exponent (T*GaussianEulerIntegrationByPartsNormalizedGrid.cost R E T) t+
    GaussianFastValueCut.exponent (endpointCost R E T) t
def boundary (p z B a C E : PTm n) : PTm n :=
  qsub (sample p (shifted z B) B (a+C) E) (sample p (shifted z B) B a E)

ipra_subst source
ipra_subst endpointCost
ipra_subst minimumObservation [GaussianEulerIntegrationByPartsGridBudget.minimumPrecision, GaussianEulerIntegrationByPartsGridBudget.observationCost, GaussianEulerIntegrationByPartsProductStep.observationCost, GaussianEulerIntegrationByPartsProductStep.linearBound, GaussianEulerCompactPowerMajorant.majorant, GaussianEulerCompactPowerMajorant.exponentRadius]
ipra_subst boundary

private theorem endpoint_source (z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    GaussianEulerIntegrationByPartsObservation.source z R B E T a E ⋏
      GaussianEulerIntegrationByPartsObservation.source z R B E T (a+C) E := by
  have ha := h.andE₂.andE₁
  have he := h.andE₁.andE₂.andE₁
  have aT := le_trans (le_add_right a C) h.andE₂.andE₂
  have low : Γ ⊢[PRAAx] le E (E*a) := le_congr (one_mul E) (mul_comm a E) (mul_le_mul_right E ha)
  have rightPositive := le_trans ha (le_add_right a C)
  have rightLow : Γ ⊢[PRAAx] le E (E*(a+C)) := le_congr (one_mul E) (mul_comm (a+C) E) (mul_le_mul_right E rightPositive)
  exact .andI (.andI h.andE₁ (.andI (.andI ha he) (.andI low (le_congr (.eqRefl _) (mul_comm E T) aT))))
    (.andI h.andE₁ (.andI (.andI rightPositive he) (.andI rightLow (le_congr (.eqRefl _) (mul_comm E T) h.andE₂.andE₂))))

private theorem negative_distance (u v A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded u v A D) : Γ ⊢[PRAAx] distanceBounded (qnegative u) (qnegative v) A D :=
  bound_congr (GaussianCharacteristicEntryNorm.negative_difference u v).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_negative _ _ _ hD h)

theorem original_boundary_observations (p N z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (qsub (endpoint N p z B a C E N) (endpoint zero p z B a C E N))
      (boundary p z B a C E) (endpointCost R E T) (unit p) := by
  have hB := h.andE₁.andE₁
  have ha := h.andE₂.andE₁
  have he := h.andE₁.andE₂.andE₁
  have aT := le_congr (.eqRefl _) (mul_comm E T) (le_trans (le_add_right a C) h.andE₂.andE₂)
  have cT := le_congr (.eqRefl _) (mul_comm E T) h.andE₂.andE₂
  have rightPositive := le_trans ha (le_add_right a C)
  have left := GaussianEulerIntegrationByPartsEndpointRescale.original_boundary_rescale p z B a E N T hB ha he hN aT
  have right := GaussianEulerIntegrationByPartsEndpointRescale.original_boundary_rescale p z B (a+C) E N T hB rightPositive he hN cT
  have leftActual : Γ ⊢[PRAAx] distanceBounded (endpoint zero p z B a C E N) (primitive p z B a E) (num 6*T) (unit p) :=
    distance_congr (GaussianEulerIntegrationByPartsGrid.primitive_numerator_congr p z B _ _ (E*N) (by ipra_ring))
      (.eqRefl _) (.eqRefl _) (.eqRefl _) left
  have rightActual : Γ ⊢[PRAAx] distanceBounded (endpoint N p z B a C E N) (primitive p z B (a+C) E) (num 6*T) (unit p) :=
    distance_congr (GaussianEulerIntegrationByPartsGrid.primitive_numerator_congr p z B _ _ (E*N) (by ipra_ring))
      (.eqRefl _) (.eqRefl _) (.eqRefl _) right
  have endpointSource := endpoint_source z R B a C E T h
  have leftNormalized := GaussianEulerIntegrationByPartsParameterShiftObservation.original_primitive_observation p z R B E T a E endpointSource.andE₁
  have rightNormalized := GaussianEulerIntegrationByPartsParameterShiftObservation.original_primitive_observation p z R B E T (a+C) E endpointSource.andE₂
  have leftFull := distance_triangle_same _ _ _ _ _ _ (unit_positive p) leftActual (distance_symmetric _ _ _ _ (unit_positive p) leftNormalized)
  have rightFull := distance_triangle_same _ _ _ _ _ _ (unit_positive p) rightActual (distance_symmetric _ _ _ _ (unit_positive p) rightNormalized)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold endpointCost; ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ (unit_positive p) rightFull (negative_distance _ _ _ _ (unit_positive p) leftFull))

theorem original_boundary_dyadic (t p N z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (endpointCost R E T) t) p) : Γ ⊢[PRAAx]
    distanceBounded (qsub (endpoint N p z B a C E N) (endpoint zero p z B a C E N)) (boundary p z B a C E) one (unit t) := by
  have query : Γ ⊢[PRAAx] le (endpointCost R E T*unit t) (unit p) :=
    le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone hp)
  exact distance_radius_mono _ _ _ _ one (unit t) (unit_positive p) (unit_positive t)
    (le_congr (.eqRefl _) (one_mul _).eqSymm query) (original_boundary_observations p N z R B a C E T h hN)

theorem original_compact_IBP (t p N z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T)
    (hm : Γ ⊢[PRAAx] le (GaussianEulerIntegrationByPartsGridBudget.minimumMesh t R E T C) N)
    (hp : Γ ⊢[PRAAx] le (minimumObservation t R E T N) p) : Γ ⊢[PRAAx]
    distanceBounded (normalized p N z B a C E) (boundary p z B a C E) (num 3) (unit t) := by
  have first : Γ ⊢[PRAAx] le (GaussianEulerIntegrationByPartsGridBudget.minimumPrecision t R E T N) p :=
    le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) hp
  have second : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (T*GaussianEulerIntegrationByPartsNormalizedGrid.cost R E T) t) p :=
    le_trans (le_trans (le_add_left _ _) (le_add_right _ _)) hp
  have third : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (endpointCost R E T) t) p := le_trans (le_add_left _ _) hp
  have grid := GaussianEulerIntegrationByPartsGridBudget.source_of_mesh t z R B a C E T N h.andE₁ h.andE₂ hm
  have hN := grid.andE₂.andE₁
  have finite := GaussianEulerIntegrationByPartsGridBudget.original_dyadic_error t p z R B a C E T N h.andE₁ h.andE₂ hm first
  have normal := GaussianEulerIntegrationByPartsNormalizedGrid.original_normalization_dyadic t p N z R B a C E T h.andE₁ hN second
  have bound := original_boundary_dyadic t p N z R B a C E T h.andE₁ hN third
  have total := distance_triangle_same _ _ _ _ _ _ (unit_positive t) normal
    (distance_triangle_same _ _ _ _ _ _ (unit_positive t) (distance_symmetric _ _ _ _ (unit_positive t) finite) bound)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) total

theorem actual_original_compact_Euler_IBP_nonzero_boundary_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⋏
      le (GaussianEulerIntegrationByPartsGridBudget.minimumMesh (var 0) (var 4) (var 8) (var 9) (var 7)) (var 2) ⋏
      le (minimumObservation (var 0) (var 4) (var 8) (var 9) (var 2)) (var 1)) ⟶
      distanceBounded (normalized (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8))
        (boundary (var 1) (var 3) (var 5) (var 6) (var 7) (var 8)) (num 3) (unit (var 0))) :=
  closeUniv 10 (.impI (original_compact_IBP _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsCompact
