import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalLocationResidual
import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalRescale
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitCompactTimeBounds
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmVariation
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport
import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.GaussianRationalNonnegativeFractions

/-!
# Uniform rational variation of the shifted negative-interval digamma

The original upper and lower slopes give a two-sided estimate on the
real observations of the native shifted digamma. Common-denominator
rescaling preserves the actual argument and the pole margins. An
independent observation estimate follows by removal of auxiliary slack.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigammaRationalRate

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalCorrectionSlope (ordered domain)
open GaussianGammaNegativeCriticalEndpoints (nameF nameData name_regular)
open GaussianGammaNegativeCriticalLocationComparison (datum_congr)
open GaussianGammaNegativeCriticalLocationResidual (realF realData original_cross real_samples)
open GaussianGammaNegativeCriticalRescale (scaled_guard original_rescale)
open GaussianGammaNegativeCriticalSlope (coefficient cap upper_at)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (ofGaussian_canonical positive_product qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedNameExponentialOrder (real_sample_at)
open RationalArgmin (rationalLE_congr reflexive)
open RationalGaussianEmbedding (canonical_axis_roundtrip)
open RationalGaussianRealPart (real_add real_zero)
open RationalHarmonicIntervalVariation (gap)
open RationalValueBounds (upper upper_mono upper_order_left radius radius_congr radius_mono radius_of_upper radius_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "compact" => GaussianEulerUnitCompactTimeBounds.source

def input (a b c d E X D : PTm n) : Fm PTm n :=
  compact a b E ⋏ (compact c d E ⋏ (le one D ⋏ distanceBounded (fraction a b) (fraction c d) X D))

ipra_subst input

ipra_subst realData

theorem real_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx] pointCN realF (realData a b N) := by
  have e := original_cross a b N h
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e) e

private theorem compact_scaled (a b E s : PTm n) (h : Γ ⊢[PRAAx] compact a b E)
    (hs : Γ ⊢[PRAAx] le one s) : Γ ⊢[PRAAx] compact (s*a) (s*b) E := by
  exact .andI (scaled_guard a b s h.andE₁ hs) (.andI h.andE₂.andE₁
    (.andI (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right s h.andE₂.andE₂.andE₁))
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right s h.andE₂.andE₂.andE₂))))

private theorem compact_congr {a b b' E : PTm n} (he : Γ ⊢[PRAAx] b ≐ b')
    (h : Γ ⊢[PRAAx] compact a b E) : Γ ⊢[PRAAx] compact a b' E :=
  .andI (.andI h.andE₁.andE₁ (lt_congr (.eqRefl _) he h.andE₁.andE₂)) (.andI h.andE₂.andE₁
    (.andI (le_congr he (.eqRefl _) h.andE₂.andE₂.andE₁)
      (le_congr (congrAdd (.eqRefl _) he) (congrMul (.eqRefl _) he) h.andE₂.andE₂.andE₂)))

private theorem drop_margin (v K B : PTm n) (hv : Γ ⊢[PRAAx] GaussianRationalHorner.canonical v)
    (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT v) (RationalArithmetic.add (fstT v) (fstT (fraction K B))) := by
  let m := fraction K B
  have hm := (GaussianRationalNonnegativeFractions.fraction_nonnegative K B hB).andE₁
  have add := GaussianStirlingTailComparison.point_add_order v v qzero m (reflexive _) (rationalLE_congr real_zero.eqSymm (.eqRefl _) hm)
  have e := (GaussianRationalLinearProduct.qadd_commutative v qzero).eqTrans (GaussianRationalSyntheticDivision.qzero_add v hv)
  exact rationalLE_congr (congrFst e) (real_add v m) add

private theorem ordered_scalar_radius (p a c b E N : PTm n) (h : Γ ⊢[PRAAx] domain a c b E) :
    Γ ⊢[PRAAx] radius (fstT (ap2 nameF p (nameData a b N))) (fstT (ap2 nameF p (nameData c b N)))
      (cap a c N E*unit p+num 5*b) (b*unit p) := by
  let P := unit p
  let x := ap2 nameF p (nameData a b N)
  let y := ap2 nameF p (nameData c b N)
  let m := GaussianGammaNegativeCriticalLowerSlope.margin a c b
  let U := cap a c N E*P+num 5*b
  have hp := unit_positive (Γ := Γ) p
  have hb := GaussianGammaNegativeCriticalCorrectionSlope.denominator_positive a c b h.andE₁
  have hm := positive_product _ _ (show Γ ⊢[PRAAx] le one (num 4 : PTm n) from by ipra_le 3) hb
  have hx : Γ ⊢[PRAAx] GaussianRationalHorner.canonical x := GaussianNameArithmetic.add_canonical _ _ _ _ p
  have lo := upper_order_left (fstT x) (RationalArithmetic.add (fstT x) (fstT m)) (fstT y) _ _
    (drop_margin x (monus c a) (num 4*b) hx hm) (GaussianGammaNegativeCriticalLowerSlope.lower_at p p a c b N h.andE₁)
  have hi := upper_at p p a c b N E h
  exact radius_of_upper _ _ _ _
    (upper_mono _ _ _ _ U (b*P) (positive_product _ _ hp hp) lo
      (by dsimp only [U,P]; ipra_le 𝔞(cap a c N E)*𝔞(unit p)^3))
    (upper_mono _ _ _ _ U (b*P) (GaussianNamedInverseRate.denominator_positive b p p hb) hi
      (by dsimp only [U,P,rateNumerator,rateDenominator]; ipra_le 3*𝔞(b)^2*𝔞(unit p)^2))

private theorem original_cross_scaled (a b s N : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] crossEquivalent nameF realF (nameData (s*a) (s*b) N) (realData a b N) :=
  cross_trans _ _ _ _ _ _ (original_rescale a b N s h hs) (original_cross a b N h)

private theorem cleared_gap (a b c d X D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) X D) :
    Γ ⊢[PRAAx] le (D*gap a b c d) (X*b*d) := by
  have e := GaussianStirlingMultiplicativeBoundsOrder.fraction_real_part a b hb
  have f := GaussianStirlingMultiplicativeBoundsOrder.fraction_real_part c d hd
  exact GaussianPositiveRationalLogarithmVariation.original_time_distance a b c d X D hb hd hD
    (radius_congr e f (.eqRefl _) (.eqRefl _) (scalar_coordinate_distance _ _ _ _ hD h))

private theorem ordered_diagonal (p a b c d N E X D : PTm n)
    (ha : Γ ⊢[PRAAx] compact a b E) (hc : Γ ⊢[PRAAx] compact c d E)
    (hD : Γ ⊢[PRAAx] le one D) (ho : Γ ⊢[PRAAx] le (d*a) (b*c))
    (hclose : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) X D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 realF p (realData a b N)) (ap2 realF p (realData c d N))
      (diagonalNumerator (coefficient N E*X) D (num 9) p) (diagonalDenominator D p) := by
  let A := d*a
  let C := b*c
  let B := d*b
  let P := unit p
  let x := ap2 realF p (realData a b N)
  let y := ap2 realF p (realData c d N)
  let u := ap2 nameF p (nameData A B N)
  let v := ap2 nameF p (nameData C B N)
  have hb := le_trans ha.andE₁.andE₁ (le_of_lt ha.andE₁.andE₂)
  have hd := le_trans hc.andE₁.andE₁ (le_of_lt hc.andE₁.andE₂)
  have hp := unit_positive (Γ := Γ) p
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ hd hb
  have left : Γ ⊢[PRAAx] compact A B E := compact_scaled a b E d ha hd
  have right : Γ ⊢[PRAAx] compact C B E := compact_congr (mul_comm b d) (compact_scaled c d E b hc hb)
  have hdom : Γ ⊢[PRAAx] domain A C B E := .andI (.andI left.andE₁.andE₁ (.andI ho right.andE₁.andE₂))
    (.andI left.andE₂.andE₂.andE₁ (GaussianEulerUnitCompactTimeBounds.gap_margin C B E right))
  have xl := cross_at _ _ _ _ p p (cross_symm _ _ _ _ (original_cross_scaled a b d N ha.andE₁ hd))
  have yr : Γ ⊢[PRAAx] crossEquivalent nameF realF (nameData C B N) (realData c d N) :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (datum_congr (.eqRefl _) (mul_comm b d))
      (.eqRefl _) (original_cross_scaled c d b N hc.andE₁ hb)
  have hpp := positive_product _ _ hp hp
  have left_error : Γ ⊢[PRAAx] radius (fstT x) (fstT u) two P :=
    radius_mono _ _ _ _ _ _ hpp (scalar_coordinate_distance _ _ _ _ hpp xl) (by ipra_le 0)
  have right_error : Γ ⊢[PRAAx] radius (fstT v) (fstT y) two P :=
    radius_mono _ _ _ _ _ _ hpp (scalar_coordinate_distance _ _ _ _ hpp (cross_at _ _ _ _ p p yr)) (by ipra_le 0)
  have mid := ordered_scalar_radius p A C B E N hdom
  have joined := radius_triangle _ _ _ _ _ _ _ (radius_triangle _ _ _ _ _ _ _ left_error mid) right_error
  have e : Γ ⊢[PRAAx] gap a b c d ≐ monus C A := by
    unfold gap
    exact (congrAdd (congrMonus (mul_comm a d) (.eqRefl _)) (congrMonus (.eqRefl _) (mul_comm a d))).eqTrans
      ((congrAdd ho (.eqRefl _)).eqTrans (zero_add _))
  have gap_bound : Γ ⊢[PRAAx] le (D*monus C A) (X*B) :=
    le_congr (congrMul (.eqRefl _) e) (by dsimp [B]; ipra_ring) (cleared_gap a b c d X D hb hd hD hclose)
  have final : Γ ⊢[PRAAx] radius (fstT x) (fstT y)
      (diagonalNumerator (coefficient N E*X) D (num 9) p) (diagonalDenominator D p) := by
    apply radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp (positive_product _ _ hB hp)) hp) joined
    dsimp only [diagonalNumerator,diagonalDenominator,cap,P]
    ipra_le 𝔞(coefficient N E)*𝔞(unit p)^4*sl gap_bound
  have xr := real_sample_at realF (realData a b N) p (real_samples a b N ha.andE₁)
  have yr' := real_sample_at realF (realData c d N) p (real_samples c d N hc.andE₁)
  exact distance_congr (canonical_axis_roundtrip x xr.andE₁ xr.andE₂) (canonical_axis_roundtrip y yr'.andE₁ yr'.andE₂)
    (.eqRefl _) (.eqRefl _) (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (positive_product _ _ hD hp) final)

theorem real_diagonal (p a b c d N E X D : PTm n) (h : Γ ⊢[PRAAx] input a b c d E X D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 realF p (realData a b N)) (ap2 realF p (realData c d N))
      (diagonalNumerator (coefficient N E*X) D (num 9) p) (diagonalDenominator D p) := by
  have ha := h.andE₁
  have hc := h.andE₂.andE₁
  have hd := h.andE₂.andE₂.andE₁
  have hd' := positive_product D (unit p) hd (unit_positive p)
  have near := h.andE₂.andE₂.andE₂
  refine .orE (le_total (d*a) (b*c)) ?_ ?_
  · exact ordered_diagonal p a b c d N E X D ha.wk hc.wk hd.wk Prf.hyp0 near.wk
  · exact distance_symmetric _ _ _ _ hd'.wk
      (ordered_diagonal p c d a b N E X D hc.wk ha.wk hd.wk Prf.hyp0 (distance_symmetric _ _ _ _ hd.wk near.wk))

theorem real_rate (a b c d N E X D : PTm n) (h : Γ ⊢[PRAAx] input a b c d E X D) :
    Γ ⊢[PRAAx] independentRate realF realF (realData a b N) (realData c d N) (coefficient N E*X) D := by
  refine GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 9) h.andE₂.andE₂.andE₁
    (real_regular a b N h.andE₁.andE₁) (real_regular c d N h.andE₂.andE₁.andE₁) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (sh a) (sh b) (sh c) (sh d) (sh E) (sh X) (sh D) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift
  simpa only [diagonalEnvelope,subst_realData,GaussianGammaNegativeCriticalSlope.subst_coefficient,
    PTm.subst_mul,PTm.subst_num,Syn.shift,sh] using
    real_diagonal (var 0) (sh a) (sh b) (sh c) (sh d) (sh N) (sh E) (sh X) (sh D) hs

theorem original_rate (a b c d N E X D : PTm n) (h : Γ ⊢[PRAAx] input a b c d E X D) :
    Γ ⊢[PRAAx] independentRate nameF nameF (nameData a b N) (nameData c d N) (coefficient N E*X) D :=
  GaussianNamedRateTransport.transport realF realF nameF nameF (realData a b N) (realData c d N)
    (nameData a b N) (nameData c d N) (coefficient N E*X) D h.andE₂.andE₂.andE₁
    (real_rate a b c d N E X D h) (original_cross a b N h.andE₁.andE₁) (original_cross c d N h.andE₂.andE₁.andE₁)

theorem actual_original_shifted_negative_digamma_rational_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (input (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) ⟶
        independentRate nameF nameF (nameData (var 0) (var 1) (var 4)) (nameData (var 2) (var 3) (var 4))
          (coefficient (var 4) (var 5)*var 6) (var 7)) :=
  closeUniv 8 (.impI (original_rate _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDigammaRationalRate
