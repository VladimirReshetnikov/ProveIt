import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicCutoffSplit
import IPRADerivations.Analysis.Euler.Logarithms.UpperBounds.GaussianEulerLogarithmicUpperCutoffBudget

/-!
# Compare original logarithmic intervals with the same lower endpoint

With a common positive lower endpoint, the difference between two
compact intervals consists of one upper tail. The earlier name keeps its
original radius and top guard. A change of compact client and the actual
addition program account for the observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicTopExtension

open_ipra
open GaussianEulerLogarithmicIntervalName (data nameF name_regular)
open GaussianEulerLogarithmicCutoffSplit (interval_data_congr)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianGammaIntegralCutoffs (tailCoefficient)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product qadd qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_to_diagonal cross_trans)
open GaussianNameArithmetic (addData addF)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def width (E T : PTm n) : PTm n := monus (E*T) one
def tailWidth (E L T : PTm n) : PTm n := E*monus T (two*L)
def fullData (j z R B E T : PTm n) : PTm n := data j z R B one (width E T) E T
def tailData (j z R B E L T : PTm n) : PTm n := data j z R B (two*L*E) (tailWidth E L T) E T
def source (z R S B E L T : PTm n) : Fm PTm n :=
  GaussianEulerUpperPowerCoefficients.source z R B ⋏
    (GaussianEulerUpperPowerCoefficients.source z S B ⋏ (le one E ⋏ (le one L ⋏ le (two*L) T)))
def numerator (p q j S L : PTm n) : PTm n := tailCoefficient (S+j)*unit p*unit q+unit L*(unit q+num 5*unit p)
def denominator (p q L : PTm n) : PTm n := unit L*unit p*unit q

private theorem positive_top (L : PTm n) (hL : Γ ⊢[PRAAx] le one L) : Γ ⊢[PRAAx] le two (two*L) :=
  le_congr (one_mul two) (mul_comm _ _) (mul_le_mul_right two hL)

private theorem right_endpoint (E T : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx]
    one+width E T ≐ E*T := (eq_add_of_le (positive_product _ _ hE hT)).eqSymm

theorem full_interval_source (z R B E T : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B)
    (hE : Γ ⊢[PRAAx] le one E) (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx]
    intervalSource z R B one (width E T) E T :=
  .andI (.andI h.andE₁ (.andI hE h.andE₂))
    (.andI (le_refl one) (le_congr (right_endpoint E T hE hT).eqSymm (.eqRefl _) (le_refl _)))

private theorem combined_width (E L T : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hL : Γ ⊢[PRAAx] le one L)
    (hT : Γ ⊢[PRAAx] le (two*L) T) : Γ ⊢[PRAAx] width E (two*L)+tailWidth E L T ≐ width E T := by
  have mid := le_trans (le_of_eq_add (d := one) (by ipra_ring : Γ ⊢[PRAAx] two ≐ one+one)) (positive_top L hL)
  have go := (congrMul (.eqRefl E) (eq_add_of_le hT)).eqTrans
    (by unfold tailWidth; ipra_ring : Γ ⊢[PRAAx] E*(two*L+monus T (two*L)) ≐ E*(two*L)+tailWidth E L T)
  ipra_lc -(natEq (go.eqTrans (congrAdd (right_endpoint E (two*L) hE mid).eqSymm (.eqRefl _)))+natEq (right_endpoint E T hE (le_trans mid hT)))

private theorem shifted_short_source (z R B E L T : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B)
    (hE : Γ ⊢[PRAAx] le one E) (hL : Γ ⊢[PRAAx] le one L) (hT : Γ ⊢[PRAAx] le (two*L) T) : Γ ⊢[PRAAx]
    intervalSource z R B one (width E (two*L)) E T := by
  have mid := le_trans (le_of_eq_add (d := one) (by ipra_ring : Γ ⊢[PRAAx] two ≐ one+one)) (positive_top L hL)
  have old := full_interval_source z R B E (two*L) h hE mid
  exact .andI old.andE₁ (.andI old.andE₂.andE₁
    (le_trans old.andE₂.andE₂ (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E hT))))

private theorem top_sources (z R S B E L T : PTm n) (h : Γ ⊢[PRAAx] source z R S B E L T)
    (strict : Γ ⊢[PRAAx] lt (two*L) T) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicIntervalAdditivity.source z S B one (width E (two*L)) (tailWidth E L T) E T ⋏
      GaussianEulerLogarithmicNamedUpperBound.source z S B (two*L*E) (tailWidth E L T) E T := by
  have hE := h.andE₂.andE₂.andE₁
  have hL := h.andE₂.andE₂.andE₂.andE₁
  have hT := h.andE₂.andE₂.andE₂.andE₂
  have large := full_interval_source z S B E T h.andE₂.andE₁ hE
    (le_trans (le_of_eq_add (d := one) (by ipra_ring : Γ ⊢[PRAAx] two ≐ one+one)) (le_trans (positive_top L hL) hT))
  have extent := combined_width E L T hE hL hT
  have sumCap := le_congr (congrAdd (.eqRefl one) extent).eqSymm (.eqRefl _) large.andE₂.andE₂
  have smallPos : Γ ⊢[PRAAx] le one (width E (two*L)) :=
    GaussianGammaCompactCutoffGeometry.gap_positive one (E*(two*L))
      (le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono hE (positive_top L hL)))
  have widePos := positive_product _ _ hE (GaussianGammaCompactCutoffGeometry.gap_positive _ _ strict)
  have endPoint : Γ ⊢[PRAAx] two*L*E+tailWidth E L T ≐ E*T :=
    (by unfold tailWidth; ipra_ring : Γ ⊢[PRAAx] two*L*E+tailWidth E L T ≐ E*(two*L+monus T (two*L))).eqTrans
      (congrMul (.eqRefl E) (eq_add_of_le hT).eqSymm)
  have startLe : Γ ⊢[PRAAx] le E (two*L*E) :=
    le_congr (one_mul E) (.eqRefl _) (mul_le_mul_right E (le_trans
      (le_of_eq_add (d := one) (by ipra_ring : Γ ⊢[PRAAx] two ≐ one+one)) (positive_top L hL)))
  exact .andI (.andI (.andI large.andE₁ (.andI (le_refl _) sumCap)) (.andI smallPos widePos))
    (.andI (.andI large.andE₁ (.andI startLe (le_congr endPoint.eqSymm (.eqRefl _) (le_refl _)))) widePos)

private theorem tail_interval_source (z R B E L T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLogarithmicNamedUpperBound.source z R B (two*L*E) (tailWidth E L T) E T) : Γ ⊢[PRAAx]
    intervalSource z R B (two*L*E) (tailWidth E L T) E T :=
  .andI h.andE₁.andE₁ (.andI (le_trans h.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₁) h.andE₁.andE₂.andE₂)

theorem strict_split (j z R S B E L T : PTm n) (h : Γ ⊢[PRAAx] source z R S B E L T)
    (strict : Γ ⊢[PRAAx] lt (two*L) T) : Γ ⊢[PRAAx]
    crossEquivalent nameF (addF nameF nameF) (fullData j z S B E T)
      (addData (fullData j z R B E (two*L)) (tailData j z S B E L T)) := by
  let W := width E (two*L)
  let C := tailWidth E L T
  let x := fullData j z R B E (two*L)
  let y := data j z S B one W E T
  let tail := tailData j z S B E L T
  let whole := fullData j z S B E T
  have hE := h.andE₂.andE₂.andE₁
  have hL := h.andE₂.andE₂.andE₂.andE₁
  have hT := h.andE₂.andE₂.andE₂.andE₂
  have mid := le_trans (le_of_eq_add (d := one) (by ipra_ring : Γ ⊢[PRAAx] two ≐ one+one)) (positive_top L hL)
  have xSource := full_interval_source z R B E (two*L) h.andE₁ hE mid
  have ySource := shifted_short_source z S B E L T h.andE₂.andE₁ hE hL hT
  have guards := top_sources z R S B E L T h strict
  have tailSource := tail_interval_source z S B E L T guards.andE₂
  have align := GaussianEulerLogarithmicClientIndependence.original_independence j z S R B one W E E T E (two*L)
    (.andI (GaussianEulerLogarithmicClientIntervalName.canonical_source _ _ _ _ _ _ _ ySource)
      (GaussianEulerLogarithmicClientIntervalName.canonical_source _ _ _ _ _ _ _ xSource))
  have hx := name_regular j z R B one W E (two*L) xSource
  have hy := name_regular j z S B one W E T ySource
  have hz := name_regular j z S B (two*L*E) C E T tailSource
  have next := GaussianNameArithmetic.add_equivalent nameF nameF nameF nameF y x tail tail hy hx hz hz
    (cross_to_diagonal _ _ _ _ align) (cross_to_diagonal _ _ _ _ (cross_refl _ _ hz))
  have split := GaussianEulerLogarithmicIntervalAdditivity.original_additivity j z S B one W C E T guards.andE₁
  have eqWhole := interval_data_congr j z S B one (W+C) E T one (width E T) E T (.eqRefl _)
    (combined_width E L T hE hL hT) (.eqRefl _) (.eqRefl _)
  have eqTail := interval_data_congr j z S B (one+W) C E T (two*L*E) C E T
    ((right_endpoint E (two*L) hE mid).eqTrans (mul_comm _ _)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
  have middle := GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ whole _ (addData y tail) eqWhole
    (GaussianGammaCompactCutoffSplit.add_data_congr y y _ tail (.eqRefl _) eqTail) split
  exact cross_trans _ _ _ _ _ _ middle next

theorem original_strict_observations (p q j z R S B E L T : PTm n) (h : Γ ⊢[PRAAx] source z R S B E L T)
    (strict : Γ ⊢[PRAAx] lt (two*L) T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (fullData j z S B E T)) (ap2 nameF q (fullData j z R B E (two*L)))
      (numerator p q j S L) (denominator p q L) := by
  let X := fullData j z R B E (two*L)
  let Y := tailData j z S B E L T
  let Z := ap2 nameF q X
  let Q := unit q
  let D := denominator p q L
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)
  have hq := unit_positive (Γ := Γ) q
  have hL := unit_positive (Γ := Γ) L
  have hE := h.andE₂.andE₂.andE₁
  have hTop := le_trans (le_of_eq_add (d := one) (by ipra_ring : Γ ⊢[PRAAx] two ≐ one+one))
    (positive_top L h.andE₂.andE₂.andE₂.andE₁)
  have guards := top_sources z R S B E L T h strict
  have regularX := name_regular j z R B one (width E (two*L)) E (two*L)
    (full_interval_source z R B E (two*L) h.andE₁ hE hTop)
  have regularY := name_regular j z S B (two*L*E) (tailWidth E L T) E T (tail_interval_source z S B E L T guards.andE₂)
  have split := cross_at _ _ _ _ p q (strict_split j z R S B E L T h strict)
  have read := GaussianNameRingLaws.add_sample_error nameF nameF X Y q regularX regularY
  have first := distance_radius_mono _ _ _ _ ((unit p+Q)*unit L) D
    (positive_product _ _ (unit_positive p) hq) hD (le_congr (.eqRefl _) (by unfold D denominator; ipra_ring) (le_refl _)) split
  have second := distance_radius_mono _ _ _ _ (num 3*unit L*unit p) D hq hD
    (le_congr (.eqRefl _) (by unfold GaussianNameRingLaws.three D denominator; ipra_ring) (le_refl _)) read
  have tail := GaussianEulerLogarithmicUpperCutoffBudget.original_integer_tail_bound q j z S B L (tailWidth E L T) E T guards.andE₂
  have dy : Γ ⊢[PRAAx] le one (unit L*Q) := positive_product _ _ hL hq
  have distance := (GaussianReconstructionRoots.distance_zero_iff _ _ _ dy).iffMpr tail
  have held := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) Z _ dy
  have canonical : Γ ⊢[PRAAx] GaussianRationalHorner.canonical Z :=
    GaussianCompactRiemannName.name_canonical GaussianEulerLogarithmicCompactName.evaluatorF q one (width E (two*L)) E
      (GaussianEulerLogarithmicMultiplier.lipschitz j R E (two*L)) (two*L) (GaussianEulerLogarithmicCompactName.fixedData j R E (two*L) z B)
  have third := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ dy held distance
  have reduced : Γ ⊢[PRAAx] distanceBounded (qadd Z (ap2 nameF q Y)) Z
      (tailCoefficient (S+j)*Q+unit L) (unit L*Q) :=
    distance_congr (.eqRefl _) (GaussianRationalLinearProduct.qadd_zero_right Z canonical)
      ((zero_add _).eqTrans (congrAdd
        (congrMul (GaussianEulerUpperTailCauchyBudget.exact_tail_coefficient (S+j)).eqSymm (.eqRefl Q)) (.eqRefl _)))
      (.eqRefl _) third
  have last := distance_radius_mono _ _ _ _ ((tailCoefficient (S+j)*Q+unit L)*unit p) D dy hD
    (le_congr (.eqRefl _) (by unfold D denominator; ipra_ring) (le_refl _)) reduced
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator Q; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first (distance_triangle_same _ _ _ _ _ _ hD second last))

theorem actual_original_logarithmic_strict_top_extension_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶ lt (two*var 8) (var 9) ⟶
      distanceBounded (ap2 nameF (var 0) (fullData (var 2) (var 3) (var 5) (var 6) (var 7) (var 9)))
        (ap2 nameF (var 1) (fullData (var 2) (var 3) (var 4) (var 6) (var 7) (two*var 8)))
        (numerator (var 0) (var 1) (var 2) (var 5) (var 8)) (denominator (var 0) (var 1) (var 8))) :=
  closeUniv 10 (.impI (.impI (original_strict_observations _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicTopExtension
