import IPRADerivations.Analysis.GaussianBetaSharpUpperDifference

/-!
# A single quarter-degree endpoint for any later contiguous half-decay grid

The left endpoint is the original exact N/2 grid position at the
unchanged sharp degree. The width and mesh are arbitrary genuine
numerical parameters. One D_R endpoint term suffices for the whole grid.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSharpQuarterDecayGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaSharpUpperDifference (start endpointClock endpoint_clock_budget geometry)
open GaussianEulerSharpDegreeSchedule (degree)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive)
open GaussianWeightedHalfDecayEndpoint (coefficient meshNumerator meshDenominator)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianCompactRiemannName (quadrature)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def numerator (t p M C E R : PTm n) : PTm n := coefficient R*meshNumerator p (endpointClock t R) M C E*unit (t+num 3)+
  meshDenominator p (endpointClock t R) M E
def denominator (t p M E R : PTm n) : PTm n := meshDenominator p (endpointClock t R) M E*unit (t+num 3)

theorem original_scaled_half_bound (t p M k A C R : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) (hC : Γ ⊢[PRAAx] le one C)
    (hstep : Γ ⊢[PRAAx] le C ((two*etaDen k A R)*M)) : Γ ⊢[PRAAx]
    bounded (qmul (radiusPoint (majorant R) one)
      (quadrature GaussianEulerCompactUpperTail.halfEvaluator p M (start t k A R) C (etaDen k A R) zero))
      (numerator t p M C (etaDen k A R) R) (denominator t p M (etaDen k A R) R) := by
  let q := endpointClock t R
  let E := etaDen k A R
  let X := unit q+two*coefficient R*unit (t+num 4)
  let Y := unit (t+num 4)*unit q
  have geo := geometry t k A R hA
  have he := eta_den_positive (Γ := Γ) k A R
  have hy : Γ ⊢[PRAAx] le one Y := positive_product _ _ (unit_positive _) (unit_positive q)
  have same := GaussianRationalSyntheticDivision.qmul_congr (.eqRefl (radiusPoint (coefficient R) one))
    (GaussianBetaSharpPartition.half_point_decay_sample q k A R (degree t R) hA)
  have hStart : Γ ⊢[PRAAx] bounded (qmul (radiusPoint (coefficient R) one)
      (GaussianEulerDecayMesh.observation (start t k A R) (two*E) q)) X Y :=
    bound_congr same.eqSymm (.eqRefl _) (.eqRefl _) (GaussianEulerSharpDegreeSchedule.original_weighted_decay_bound t R q)
  have raw := GaussianWeightedHalfDecayEndpoint.original_scaled_half_decay_bound p q M (start t k A R) C E R X Y
    geo.andE₂.andE₁ hM hC he hstep hy hStart
  have hd := GaussianWeightedHalfDecayEndpoint.mesh_denominator_positive p q M E hM he
  have next : Γ ⊢[PRAAx] unit (t+num 4) ≐ two*unit (t+num 3) :=
    ((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] t+num 4 ≐ ConciseIPRA.PTm.succ (t+num 3)) (.eqRefl two)).eqTrans
      (pw_succ two (t+num 3))).eqTrans (mul_comm _ _)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hd (positive_product _ _ hy (unit_positive q)))
    (positive_product _ _ hd (unit_positive _)) _ raw
  dsimp only [numerator,denominator,GaussianWeightedHalfDecayEndpoint.numerator,GaussianWeightedHalfDecayEndpoint.denominator,X,Y,q,E]
  have eq := natEq next
  ipra_le (𝔞(meshDenominator p (endpointClock t R) M (etaDen k A R))*𝔞(meshDenominator p (endpointClock t R) M (etaDen k A R))*
      𝔞(unit (t+num 3))*𝔞(unit (endpointClock t R)))*sl (endpoint_clock_budget t R) using
    rw [eq]
    ring

theorem original_any_width_quarter_degree_half_decay_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 4) ⋏ le one (var 2) ⋏ le one (var 5) ⋏ le (var 5) ((two*etaDen (var 3) (var 4) (var 6))*var 2)) ⟶
      bounded (qmul (radiusPoint (majorant (var 6)) one)
        (quadrature GaussianEulerCompactUpperTail.halfEvaluator (var 1) (var 2) (start (var 0) (var 3) (var 4) (var 6))
          (var 5) (etaDen (var 3) (var 4) (var 6)) zero))
        (numerator (var 0) (var 1) (var 2) (var 5) (etaDen (var 3) (var 4) (var 6)) (var 6))
        (denominator (var 0) (var 1) (var 2) (etaDen (var 3) (var 4) (var 6)) (var 6))) :=
  closeUniv 7 (.impI (original_scaled_half_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSharpQuarterDecayGrid
