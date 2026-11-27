import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalLocationComparison
import IPRADerivations.Analysis.Logarithm.PositiveAxis.Increments.GaussianPositiveRationalLogarithmVariation
import IPRADerivations.Analysis.Integration.Partitions.GaussianRationalSignedPanelTailDistance
import IPRADerivations.Analysis.Stirling.Expansions.OddSeries.GaussianStirlingOddCoefficients

/-!
# Rational inverse slope for the native shifted negative digamma

At one independent precision, closeness of the actual shifted
digamma observations controls the input gap by the original lower
slope of one quarter. The estimate handles both endpoint orders.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigammaInverseSlope

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (nameF nameData)
open GaussianGammaNegativeCriticalLocationComparison (margin mixed_lower_at)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianPositiveRationalLogarithmVariation (time native crossNumerator cross_norm)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (positive_product qadd qzero)
open GaussianRationalMetric (bounded_difference_iff distanceBounded)
open GaussianRationalSyntheticDivision (rescale_to)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open RationalGaussianEmbedding (embed scalarZero scalar_zero_represents)
open RationalHarmonicIntervalVariation (gap)
open RationalValueBounds (upper upper_congr upper_mono upper_of_radius upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def inverseNumerator (H : PTm n) : PTm n := num 4*(H+num 5)

private theorem fraction_distance_of_gap (a b c d A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] le (D*gap a b c d) (A*b*d)) :
    Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D := by
  let x := embed (time a b)
  let y := embed (time c d)
  let E := b*d
  have e := positive_product _ _ hb hd
  have left := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (time a b) (ZT.ofNat a) b
    (RationalCubeMidpoint.fraction_represents a b hb)
  have right := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (time c d) (ZT.ofNat c) d
    (RationalCubeMidpoint.fraction_represents c d hd)
  have l := rescale_to x (native a) b d E left (.eqRefl _)
  have r := rescale_to y (native c) d b E right (mul_comm _ _)
  have ds : Γ ⊢[PRAAx] distanceBounded x y A D := by
    apply (bounded_difference_iff x y _ _ E A D e hD l r).iffMpr
    change Γ ⊢[PRAAx] le ((D*D)*ComplexLogarithmRemainder.normSq (crossNumerator a b c d)) ((A*A)*(E*E))
    exact le_congr ((congrMul (.eqRefl (D*D)) (cross_norm (Γ := Γ) a b c d)).eqTrans (by ipra_ring)).eqSymm
      (by dsimp [E]; ipra_ring) (le_mul_mono h h)
  exact distance_congr (GaussianStirlingOddCoefficients.fraction_embed a b hb)
    (GaussianStirlingOddCoefficients.fraction_embed c d hd) (.eqRefl _) (.eqRefl _) ds

private theorem ordered_margin_upper (p a b c d N H : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d) (ho : Γ ⊢[PRAAx] le (d*a) (b*c))
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (nameData a b N)) (ap2 nameF p (nameData c d N)) H (unit p)) :
    Γ ⊢[PRAAx] upper (fstT (margin a b c d)) scalarZero (H+num 5) (unit p) := by
  let P := unit p
  let x := ap2 nameF p (nameData a b N)
  let y := ap2 nameF p (nameData c d N)
  let M := margin a b c d
  have hp := unit_positive (Γ := Γ) p
  have slope := upper_congr (RationalGaussianRealPart.real_add x M).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (mixed_lower_at p p a b c d N (.andI ha (.andI hc ho)))
  have back := upper_of_radius _ _ _ _ (scalar_coordinate_distance y x H P hp (distance_symmetric _ _ _ _ hp h))
  have joined := upper_triangle _ _ _ _ _ _ _ slope back
  have amount : Γ ⊢[PRAAx] upper (fstT (qadd x M)) (fstT x) (H+num 5) P :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hp) hp) joined (by dsimp only [P]; ipra_le 0)
  exact upper_congr (.eqRefl _) RationalGaussianRealPart.real_zero (.eqRefl _) (.eqRefl _)
    (GaussianRationalSignedPanelTailDistance.real_add_cancel x M _ _ amount)

private theorem ordered_inverse (p a b c d N H : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d) (ho : Γ ⊢[PRAAx] le (d*a) (b*c))
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (nameData a b N)) (ap2 nameF p (nameData c d N)) H (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) (inverseNumerator H) (unit p) := by
  let P := unit p
  let A := H+num 5
  let W := monus (b*c) (d*a)
  let E := num 4*(d*b)
  let s := fstT (margin a b c d)
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have hd := le_trans hc.andE₁ (le_of_lt hc.andE₂)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (by ipra_le 3) (positive_product _ _ hd hb)
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents s (ZT.ofNat W) E :=
    GaussianGammaDigammaHarmonicCells.point_fraction_represents W E hE
  let l := ZT.ofNat (P*one)*ZT.ofNat W
  let r := ZT.ofNat (P*E)*ZT.ofNat zero+ZT.ofNat (A*E*one)
  have signed : Γ ⊢[PRAAx] zle l r :=
    RationalUpperRepresentation.upper_from_representations s scalarZero E one A P
      (ZT.ofNat W) (ZT.ofNat zero) rep (scalar_zero_represents one) (ordered_margin_upper p a b c d N H ha hc ho h)
  have cleared : Γ ⊢[PRAAx] le (P*W) (A*E) := by
    apply le_of_eq_add (d := PolynomialBisection.slack l r)
    have e := zle_toZ signed
    dsimp only [l,r] at e ⊢
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e
    apply deriveNat
    simp only [PolynomialBisection.slack] at e ⊢
    ipra_simps
    linear_combination -e
  have eg : Γ ⊢[PRAAx] gap a b c d ≐ W := by
    unfold gap
    exact (congrAdd (congrMonus (mul_comm a d) (.eqRefl _)) (congrMonus (.eqRefl _) (mul_comm a d))).eqTrans
      ((congrAdd ho (.eqRefl _)).eqTrans (zero_add _))
  apply fraction_distance_of_gap a b c d _ _ hb hd (unit_positive p)
  exact le_congr (congrMul (.eqRefl _) eg).eqSymm (by dsimp only [A,E,inverseNumerator]; ipra_ring) cleared

theorem input_distance (p a b c d N H : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (nameData a b N)) (ap2 nameF p (nameData c d N)) H (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) (inverseNumerator H) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  refine .orE (le_total (d*a) (b*c)) ?_ ?_
  · exact ordered_inverse p a b c d N H ha.wk hc.wk Prf.hyp0 h.wk
  · exact distance_symmetric _ _ _ _ hp.wk
      (ordered_inverse p c d a b N H hc.wk ha.wk Prf.hyp0 (distance_symmetric _ _ _ _ hp.wk h.wk))

theorem actual_original_negative_interval_digamma_inverse_slope_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (guard (var 1) (var 2) ⋏ guard (var 3) (var 4) ⟶
        distanceBounded (ap2 nameF (var 0) (nameData (var 1) (var 2) (var 5)))
          (ap2 nameF (var 0) (nameData (var 3) (var 4) (var 5))) (var 6) (unit (var 0)) ⟶
        distanceBounded (fraction (var 1) (var 2)) (fraction (var 3) (var 4)) (inverseNumerator (var 6)) (unit (var 0))) :=
  closeUniv 7 (.impI (.impI (input_distance _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigammaInverseSlope
