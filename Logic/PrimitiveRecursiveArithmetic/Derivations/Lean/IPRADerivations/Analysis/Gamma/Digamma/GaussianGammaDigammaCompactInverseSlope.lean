import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaCompactSlopeLower
import IPRADerivations.Analysis.Inequalities.GaussianRationalLowerSlopeDistance

/-!
# Invert the positive digamma lower slope at rational samples

Every positive pair can be put in rational order, even when its two
denominators differ. On a shared upper bounded interval the original
digamma observations bound the exact distance between the inputs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaCompactInverseSlope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaNative (nameF data)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaLogarithm (source)
open RationalValueBounds (upper_congr upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gain (M H : PTm n) : PTm n := M*M*(num 5+H)

private theorem ordered (a b c d M p H : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (hm : Γ ⊢[PRAAx] le one M) (ho : Γ ⊢[PRAAx] le (d*a) (b*c)) (hu : Γ ⊢[PRAAx] le c (M*d))
    (he : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data a b)) (ap2 nameF p (data c d)) H (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) (gain M H) (unit p) := by
  let P := unit p
  let x := ap2 nameF p (data a b)
  let y := ap2 nameF p (data c d)
  let z := GaussianGammaDigammaCompactSlopeLower.margin a b c d M
  have hp := unit_positive (Γ := Γ) p
  have slope := GaussianGammaDigammaCompactSlopeLower.lower_slope_at a b c d M p p ha hc hm ho hu
  have h1 := upper_mono _ _ _ _ (num 5) P (positive_product _ _ hp hp) slope
    (le_of_eq_add (d := zero) (by dsimp only [P]; ipra_ring))
  have h2 := upper_congr (RationalGaussianRealPart.real_add x z).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) h1
  exact GaussianRationalLowerSlopeDistance.input_distance a b c d (M*M) x y H (num 5) P ha.andE₂ hc.andE₂
    (positive_product _ _ hm hm) hp ho h2 he

theorem input_distance (a b c d M p H : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (hm : Γ ⊢[PRAAx] le one M) (hu : Γ ⊢[PRAAx] le a (M*b)) (hv : Γ ⊢[PRAAx] le c (M*d))
    (he : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data a b)) (ap2 nameF p (data c d)) H (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) (gain M H) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  refine .orE (le_total (d*a) (b*c)) ?_ ?_
  · exact ordered a b c d M p H ha.wk hc.wk hm.wk Prf.hyp0 hv.wk he.wk
  · exact distance_symmetric _ _ _ _ hp.wk (ordered c d a b M p H hc.wk ha.wk hm.wk Prf.hyp0 hu.wk
      (distance_symmetric _ _ _ _ hp.wk he.wk))

theorem actual_positive_digamma_compact_inverse_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 0) (var 1) ⋏ source (var 2) (var 3)) ⟶
      (le one (var 4) ⋏ (le (var 0) (var 4*var 1) ⋏ le (var 2) (var 4*var 3))) ⟶
      distanceBounded (ap2 nameF (var 5) (data (var 0) (var 1))) (ap2 nameF (var 5) (data (var 2) (var 3)))
        (var 6) (unit (var 5)) ⟶
      distanceBounded (fraction (var 0) (var 1)) (fraction (var 2) (var 3)) (gain (var 4) (var 6)) (unit (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (input_distance _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.andE₁ Prf.hyp0.wk.wk.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaCompactInverseSlope
