import IPRADerivations.Analysis.Integration.Moments.GaussianOddMomentWholeAbsolute

/-!
# Independent reflected cutoffs for the odd Gaussian integral

Allow the positive and negative panels to use different observations
of the original exhaustion. Their signed sum tends to zero as both
cutoffs advance, with a sum of independent dyadic error bounds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianOddMomentIndependentCuts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianOddMomentSignedGrid (evaluatorF)
open GaussianOddMomentWholeLine (gridWith query count span lowerDenominator halfData)
open GaussianRationalHorner (qadd qzero qadd_canonical positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (point_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def signedSample (p r N c d : PTm n) : PTm n := qadd (gridWith (evaluatorF false) p N c d) (gridWith (evaluatorF true) r N c d)

theorem signed_separate_cutoffs (p r N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] distanceBounded (signedSample p r N c d) qzero (two*(unit p+unit r)) (unit p*unit r) := by
  let P := unit p
  let R := unit r
  let A := gridWith (evaluatorF false) p N c d
  let B := gridWith (evaluatorF false) r N c d
  let X := halfData N c d
  let D := P*R
  have hP : Γ ⊢[PRAAx] le one P := unit_positive p
  have hR : Γ ⊢[PRAAx] le one R := unit_positive r
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hP hR
  have ep := distance_symmetric _ _ _ _ hP (GaussianOddMomentWholeLine.finite_half_error p N c d hc hd)
  have er := GaussianOddMomentWholeLine.finite_half_error r N c d hc hd
  have pNear := distance_radius_mono _ _ _ _ R D hP hD (le_of_eq_add (d := zero) (by dsimp [D]; ipra_ring)) ep
  have rNear := distance_radius_mono _ _ _ _ P D hR hD (le_of_eq_add (d := zero) (by dsimp [D]; ipra_ring)) er
  have between := point_at GaussianOddMomentWholeAbsolute.positiveHalfF X p r (GaussianOddMomentWholeAbsolute.half_regular N c d hc hd)
  have diff : Γ ⊢[PRAAx] distanceBounded A B (two*(P+R)) D :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same A (ap2 GaussianOddMomentWholeAbsolute.positiveHalfF p X) B R (P+R+P) D hD pNear
        (distance_triangle_same (ap2 GaussianOddMomentWholeAbsolute.positiveHalfF p X) (ap2 GaussianOddMomentWholeAbsolute.positiveHalfF r X) B (P+R) P D hD between rNear))
  let S := signedSample p r N c d
  have reflected : Γ ⊢[PRAAx] S ≐ GaussianRationalMetric.qsub A B :=
    qadd_congr (.eqRefl _) (GaussianOddMomentSignedGrid.reflected_quadrature
      (query r N c d) (count r N c d) one (span r N c d) (lowerDenominator r N c d)
      (GaussianOddSymmetricQuadrature.fixedData N c d))
  have sub := (GaussianRationalReconstruction.qsub_zero_right S (qadd_canonical _ _)).eqTrans reflected
  exact GaussianRationalReciprocal.bound_congr sub.eqSymm (.eqRefl _) (.eqRefl _) diff

theorem actual_original_odd_Gaussian_independent_improper_cutoffs_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 3) ⟶ le one (var 4) ⟶
        distanceBounded (signedSample (var 0) (var 1) (var 2) (var 3) (var 4)) qzero
          (two*(unit (var 0)+unit (var 1))) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (.impI (signed_separate_cutoffs _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianOddMomentIndependentCuts
