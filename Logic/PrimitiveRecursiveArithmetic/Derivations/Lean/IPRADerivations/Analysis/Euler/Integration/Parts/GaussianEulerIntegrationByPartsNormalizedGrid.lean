import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsQuadrature
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsParameterShiftObservation
import IPRADerivations.Analysis.Polynomials.RootFinding.Characteristic.GaussianCharacteristicEntryNorm

/-!
# Original normalized Euler quadratures in the finite IBP identity

The raw operator quadrature is compared with z/B times the unchanged
original Euler quadrature minus the unchanged shifted Euler quadrature.
Every affine-grid time and every actual observation clock is retained.
The error is an explicit width times one dyadic, independent of the
number of mesh cells. No integral or Gamma recurrence is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsNormalizedGrid

open_ipra
open GaussianEulerIntegrationByPartsGrid (operatorF endpointF endpoint endpoint_grid_at)
open GaussianEulerIntegrationByPartsGridObservation (rawF rowCost grid_source)
open GaussianEulerIntegrationByPartsParameterShiftObservation (primitiveCost)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianGammaEulerHeadShift (shifted)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open GaussianRationalHorner (qmul ofGaussian positive_product qzero)
open GaussianRationalMetric (qsub qnegative bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_negative)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def cost (R E T : PTm n) : PTm n := R*rowCost R E T+primitiveCost R E T
def normalized (p N z B a C E : PTm n) : PTm n := qsub
  (qmul (ofGaussian z B) (quadrature evaluatorF p N a C E (fixedData z B)))
  (quadrature evaluatorF p N a C E (fixedData (shifted z B) B))
ipra_subst cost
ipra_subst normalized

theorem shifted_row_error (i p N z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded
      (inst2 (sampleBody evaluatorF) i (sampleData p N a C E (fixedData (shifted z B) B)))
      (inst2 (sampleBody endpointF) i (sampleData p N a C E (fixedData z B))) (primitiveCost R E T) (unit p) :=
  distance_congr (sample_body_at evaluatorF i p N a C E _).eqSymm
    (endpoint_grid_at i p z B a C E N).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerIntegrationByPartsParameterShiftObservation.original_primitive_observation p z R B E T (a*N+C*i) (E*N)
      (grid_source i N z R B a C E T h hN (le_of_lt hi)))

theorem original_shifted_grid_observations (p N z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF p N a C E (fixedData (shifted z B) B))
      (quadrature endpointF p N a C E (fixedData z B)) (C*primitiveCost R E T) (E*unit p) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] intervalSource (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have rows : Γ ⊢[PRAAx] termsDistance (sampleBody evaluatorF) (sampleBody endpointF) N
      (sampleData p N a C E (fixedData (shifted z B) B)) (sampleData p N a C E (fixedData z B)) (primitiveCost R E T) (unit p) := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,GaussianCompactRiemannName.subst_sampleData,GaussianEulerIntegrandName.subst_fixedData,
      GaussianGammaEulerHeadShift.subst_shifted,GaussianEulerIntegrationByPartsParameterShiftObservation.subst_primitiveCost,
      GaussianCoefficientNameBounds.subst_unit,Syn.shift] using
      shifted_row_error (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift z) (Syn.shift R) (Syn.shift B)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) hs.wk ns.wk Prf.hyp0
  have raw := sum_distance _ _ _ _ _ _ _ (unit_positive p) rows
  have hE := h.andE₁.andE₂.andE₁
  have hEN := positive_product E N hE hN
  have scaled := bounded_product _ _ C (E*N) (N*primitiveCost R E T) (unit p) hEN (unit_positive p)
    (weight_bound C E N hE hN) raw
  have difference := bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (weight C E N) _ _).eqSymm (.eqRefl _) (.eqRefl _) scaled
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hEN (unit_positive p)) (positive_product _ _ hE (unit_positive p))
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) difference

private theorem negative_distance (u v A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded u v A D) : Γ ⊢[PRAAx] distanceBounded (qnegative u) (qnegative v) A D :=
  bound_congr (GaussianCharacteristicEntryNorm.negative_difference u v).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_negative _ _ _ hD h)

/-- Same original normalized old and shifted rows, with no sampled
operator or boundary law supplied. Zero-width intervals are allowed. -/
theorem original_normalized_operator (p N z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature operatorF p N a C E (fixedData z B))
      (normalized p N z B a C E) (C*cost R E T) (E*unit p) := by
  let D := E*unit p
  have hd : Γ ⊢[PRAAx] le one D := positive_product E (unit p) h.andE₁.andE₂.andE₁ (unit_positive p)
  have old := distance_symmetric _ _ _ _ hd
    (GaussianEulerIntegrationByPartsGridObservation.original_grid_observations p N z R B a C E T h hN)
  have fraction := GaussianGammaEulerHead.fraction_disk z R B h.andE₁.andE₁ h.andE₁.andE₂.andE₂
  have product := bounded_product _ _ R one (C*rowCost R E T) D (le_refl one) hd fraction old
  have first : Γ ⊢[PRAAx] distanceBounded
      (qmul (ofGaussian z B) (quadrature rawF p N a C E (fixedData z B)))
      (qmul (ofGaussian z B) (quadrature evaluatorF p N a C E (fixedData z B))) (R*C*rowCost R E T) D :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm (by ipra_ring) (by ipra_ring) product
  have shifted := distance_symmetric _ _ _ _ hd (original_shifted_grid_observations p N z R B a C E T h hN)
  have last := negative_distance _ _ _ _ hd shifted
  have combined := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hd first last
  exact distance_congr (GaussianEulerIntegrationByPartsQuadrature.original_operator_quadrature_difference p N z B a C E).eqSymm
    (.eqRefl _) (by dsimp only [cost]; ipra_ring) (.eqRefl _) combined

theorem original_normalization_dyadic (t p N z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (T*cost R E T) t) p) : Γ ⊢[PRAAx]
    distanceBounded (normalized p N z B a C E)
      (quadrature operatorF p N a C E (fixedData z B)) one (unit t) := by
  have hd := positive_product E (unit p) h.andE₁.andE₂.andE₁ (unit_positive p)
  have width : Γ ⊢[PRAAx] le C (E*T) := le_trans (le_add_left C a) h.andE₂.andE₂
  have clock : Γ ⊢[PRAAx] le (T*cost R E T*unit t) (unit p) :=
    le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone hp)
  have near := distance_symmetric _ _ _ _ hd (original_normalized_operator p N z R B a C E T h hN)
  exact distance_radius_mono _ _ _ _ one (unit t) hd (unit_positive t)
    (by ipra_le (𝔞(cost R E T)*𝔞(unit t))*sl width+𝔞 E*sl clock) near

/-- The actual boundary and telescope each cost two dyadics; the
computed normalization query spends only one more. -/
theorem original_product_shift_error (t p N z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (T*cost R E T) t) p)
    (hnear : Γ ⊢[PRAAx] distanceBounded (quadrature operatorF p N a C E (fixedData z B))
      (qsub (GaussianEulerIntegrationByPartsGrid.endpoint N p z B a C E N)
        (GaussianEulerIntegrationByPartsGrid.endpoint ConciseIPRA.PTm.zero p z B a C E N)) two (unit t))
    (hboundary : Γ ⊢[PRAAx] bounded
      (qsub (GaussianEulerIntegrationByPartsGrid.endpoint N p z B a C E N)
        (GaussianEulerIntegrationByPartsGrid.endpoint ConciseIPRA.PTm.zero p z B a C E N)) two (unit t)) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (ofGaussian z B) (quadrature evaluatorF p N a C E (fixedData z B)))
      (quadrature evaluatorF p N a C E (fixedData (shifted z B) B)) (LeanProofs.IPRA.PTm.num 5) (unit t) := by
  have hu := unit_positive (Γ := Γ) t
  have boundary := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hu).iffMpr hboundary
  have middle := distance_triangle_same _ _ qzero two two (unit t) hu hnear boundary
  have total := distance_triangle_same _ _ qzero one (two+two) (unit t) hu
    (original_normalization_dyadic t p N z R B a C E T h hN hp) middle
  have five := distance_congr (.eqRefl _) (.eqRefl _)
    (by ipra_ring : Γ ⊢[PRAAx] one+(two+two) ≐ LeanProofs.IPRA.PTm.num 5) (.eqRefl _) total
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hu).iffMp five

theorem actual_original_normalized_Euler_IBP_operator_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((intervalSource (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏ le one (var 1)) ⟶
      distanceBounded (quadrature operatorF (var 0) (var 1) (var 5) (var 6) (var 7) (fixedData (var 2) (var 4)))
        (normalized (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7))
        (var 6*cost (var 3) (var 7) (var 8)) (var 7*unit (var 0))) :=
  closeUniv 9 (.impI (original_normalized_operator _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_Euler_IBP_product_shift_dyadic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((intervalSource (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⋏
      (le one (var 2) ⋏
       (le (GaussianFastValueCut.exponent (var 9*cost (var 4) (var 8) (var 9)) (var 0)) (var 1) ⋏
        (distanceBounded (quadrature operatorF (var 1) (var 2) (var 6) (var 7) (var 8) (fixedData (var 3) (var 5)))
          (qsub (endpoint (var 2) (var 1) (var 3) (var 5) (var 6) (var 7) (var 8) (var 2))
            (endpoint ConciseIPRA.PTm.zero (var 1) (var 3) (var 5) (var 6) (var 7) (var 8) (var 2))) two (unit (var 0)) ⋏
         bounded (qsub (endpoint (var 2) (var 1) (var 3) (var 5) (var 6) (var 7) (var 8) (var 2))
            (endpoint ConciseIPRA.PTm.zero (var 1) (var 3) (var 5) (var 6) (var 7) (var 8) (var 2))) two (unit (var 0)))))) ⟶
      distanceBounded
        (qmul (ofGaussian (var 3) (var 5)) (quadrature evaluatorF (var 1) (var 2) (var 6) (var 7) (var 8) (fixedData (var 3) (var 5))))
        (quadrature evaluatorF (var 1) (var 2) (var 6) (var 7) (var 8) (fixedData (shifted (var 3) (var 5)) (var 5)))
        (LeanProofs.IPRA.PTm.num 5) (unit (var 0))) :=
  closeUniv 10 (.impI (original_product_shift_error _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsNormalizedGrid
