import IPRADerivations.Analysis.GaussianBarnesCanonicalLogRow
import IPRADerivations.Core.CongruenceTactic

/-!
# Independent observations of the original Barnes logarithm row

The source degree-three rounded evaluator gives a direct ordered
comparison at any two query precisions. Multiplication by the actual
factor index preserves the rounded samples and scales the error by k.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogObservation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogRow (source roundedCubic roundedValue local_source)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianRationalHorner (ofGaussian_represents)
open GaussianRationalMetric (bounded_of_cleared qsub distanceBounded)
open GaussianRationalSyntheticDivision (rescale_to)
open DyadicComplexLogarithm (observation endpointDifference unit)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem unit_span (p q : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] unit p*pw two (monus q p) ≐ unit q := by
  have atQuery : Γ ⊢[PRAAx] unit (p+monus q p) ≐ unit q := by
    ipra_congr (unit (var 0) : PTm 1) with [(eq_add_of_le h).eqSymm]
  exact (DyadicComplexLogarithm.unit_add p (monus q p)).eqSymm.eqTrans atQuery

theorem cubic_ordered_distance (p q z R N : PTm n) (h : Γ ⊢[PRAAx] GaussianLocalLogarithmName.source z R N)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (roundedCubic q z R N) (roundedCubic p z R N) (num 5) (unit p) := by
  let e := pw two (monus q p)
  let U := unit p
  let V := unit q
  let P := observation p z R N
  let Q := observation q z R N
  let T := endpointDifference p q z R N
  have hU := GaussianLocalLogarithmName.unit_positive (Γ := Γ) p
  have hV := GaussianLocalLogarithmName.unit_positive (Γ := Γ) q
  have hu := unit_span p q hpq
  have old := rescale_to (roundedCubic p z R N) P U e V (ofGaussian_represents P U hU) hu
  have late : Γ ⊢[PRAAx] GaussianRationalHorner.represents (roundedCubic q z R N) Q V :=
    ofGaussian_represents Q V hV
  have rep : Γ ⊢[PRAAx] GaussianRationalHorner.represents
      (qsub (roundedCubic q z R N) (roundedCubic p z R N)) T V := by
    simpa only [endpointDifference, GaussianRootAlgebra.sub, T, Q, P, V, e] using
      GaussianRationalMetric.qsub_represents (roundedCubic q z R N) (roundedCubic p z R N) Q
        (ComplexLogarithmRemainder.scale e P) V hV late old
  have native := DyadicComplexLogarithm.regular_endpoints p q z R N h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂ hpq
  have bound : Γ ⊢[PRAAx] le ((U*U)*ComplexLogarithmRemainder.normSq T) ((num 5*num 5)*(V*V)) :=
    le_congr (mul_comm _ _) (by
      have align := natEq hu
      apply deriveNat
      ipra_simps
      rw [← align]
      ring) (mul_le_mul_right (U*U) native)
  exact bounded_of_cleared _ _ _ _ _ hV hU rep bound

theorem ordered_distance (p q z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (roundedValue q z R B k) (roundedValue p z R B k) (num 5*k) (unit p) := by
  have raw := GaussianNamedDifferenceQuotient.scale_distance (radiusPoint k one)
    (roundedCubic q z (R*B) (B*k)) (roundedCubic p z (R*B) (B*k)) k (num 5) (unit p)
    (GaussianLocalLogarithmName.unit_positive p) (radius_bounded k one (le_refl one))
    (cubic_ordered_distance p q z (R*B) (B*k) (local_source z R B k h) hpq)
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (mul_comm _ _) (.eqRefl _) raw

theorem actual_ordered_Barnes_logarithm_row_observations_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 2) (var 3) (var 4) (var 5) ⟶ le (var 0) (var 1) ⟶
        distanceBounded (roundedValue (var 1) (var 2) (var 3) (var 4) (var 5))
          (roundedValue (var 0) (var 2) (var 3) (var 4) (var 5)) (num 5*var 5) (unit (var 0))) :=
  closeUniv 6 (.impI (.impI (ordered_distance _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogObservation
