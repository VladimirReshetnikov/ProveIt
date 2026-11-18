import IPRADerivations.Analysis.GaussianRationalNormClearing
import IPRADerivations.Analysis.GaussianRationalSyntheticDivision

/-!
# Exact rational relative Euclidean triangle with an arbitrary denominator

The common relative budget need not be a rational square. Two bounds
normSq(a)<=A^2/H and normSq(b)<=B^2/H imply the exact bound
normSq(a+b)<=(A+B)^2/H. The original decoded denominators are preserved
by actual rescaling. Native Gaussian numerators are scaled by H, and
only a proved positive H is cancelled. No square root or rounding is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRelativeTriangle

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (represents positive_product qadd qadd_represents represents_rescale represents_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq qnormSq_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq scale add normSq_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem from_representations (a b ga gb D A B H : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hH : Γ ⊢[PRAAx] le one H)
    (ha : Γ ⊢[PRAAx] represents a ga D) (hb : Γ ⊢[PRAAx] represents b gb D)
    (hA : Γ ⊢[PRAAx] RationalArgmin.rationalLE (qnormSq a) (fraction (A*A) H))
    (hB : Γ ⊢[PRAAx] RationalArgmin.rationalLE (qnormSq b) (fraction (B*B) H)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (qadd a b)) (fraction ((A+B)*(A+B)) H) := by
  have ca := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (qnormSq_represents a ga D hD ha) (fraction_represents (A*A) H hH) hA
  have cb := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (qnormSq_represents b gb D hD hb) (fraction_represents (B*B) H hH) hB
  have left : Γ ⊢[PRAAx] le (normSq (scale H ga)) (A*A*(D*D*H)) :=
    le_congr (normSq_scale H ga).eqSymm (by ipra_ring)
      (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right H ca))
  have right : Γ ⊢[PRAAx] le (normSq (scale H gb)) (B*B*(D*D*H)) :=
    le_congr (normSq_scale H gb).eqSymm (by ipra_ring)
      (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right H cb))
  have triangle := GaussianRelativeNormTriangle.relative_triangle (scale H ga) (scale H gb) A B (D*D*H) left right
  have cancelled : Γ ⊢[PRAAx] le (H*normSq (add ga gb)) ((A+B)*(A+B)*(D*D)) :=
    RationalValueBounds.positive_cancel hH
      (le_congr ((GaussianRationalNormClearing.norm_sum_scaled H ga gb).eqTrans (by ipra_ring))
        (by ipra_ring) triangle)
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (positive_product D D hD hD) hH (qnormSq_represents _ _ D hD (qadd_represents a b ga gb D hD ha hb))
    (fraction_represents ((A+B)*(A+B)) H hH) cancelled

/-- The actual scalar inputs may be raw or noncanonical. Their common
positive denominator and both rescaled representations are derived. -/
theorem relative_triangle (a b A B H : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hA : Γ ⊢[PRAAx] RationalArgmin.rationalLE (qnormSq a) (fraction (A*A) H))
    (hB : Γ ⊢[PRAAx] RationalArgmin.rationalLE (qnormSq b) (fraction (B*B) H)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (qadd a b)) (fraction ((A+B)*(A+B)) H) := by
  have ha := represents_rescale a (rawGaussian a) (rawDen a) (rawDen b) (raw_represents (Γ := Γ) a)
  have hb := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _)
    (mul_comm (rawDen b) (rawDen a))
    (represents_rescale b (rawGaussian b) (rawDen b) (rawDen a) (raw_represents (Γ := Γ) b))
  exact from_representations a b _ _ (rawDen a*rawDen b) A B H
    (positive_product _ _ (raw_den_positive a) (raw_den_positive b)) hH ha hb hA hB

theorem rational_relative_triangle_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶
      RationalArgmin.rationalLE (qnormSq (var 0)) (fraction (var 2*var 2) (var 4)) ⟶
      RationalArgmin.rationalLE (qnormSq (var 1)) (fraction (var 3*var 3) (var 4)) ⟶
      RationalArgmin.rationalLE (qnormSq (qadd (var 0) (var 1)))
        (fraction ((var 2+var 3)*(var 2+var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (relative_triangle _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalRelativeTriangle
