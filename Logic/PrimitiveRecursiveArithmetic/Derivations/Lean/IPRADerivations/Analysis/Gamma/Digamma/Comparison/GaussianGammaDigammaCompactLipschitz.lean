import IPRADerivations.Analysis.Gamma.Digamma.Comparison.GaussianGammaDigammaLipschitz
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaReal
import IPRADerivations.Analysis.Gamma.Digamma.Comparison.GaussianGammaDigammaMonotone
import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaRescale
import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaRescaling
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmVariation
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# Uniform upper slope for independently encoded positive digamma inputs

The compact lower margin gives a uniform upper slope K(K+1).
Monotonicity supplies the opposite scalar bound. The exact real
representatives translate these scalar bounds into a Gaussian metric
comparison, which is then transported to the original native names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaCompactLipschitz

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaNative (nameF data name_regular)
open GaussianGammaDigammaReal (original_cross name_real)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive rate_at)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedNameExponentialOrder (real_sample_at)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open RationalGaussianEmbedding (canonical_axis_roundtrip)
open RationalHarmonicIntervalVariation (gap)
open RationalValueBounds (radius radius_of_upper radius_congr radius_mono radius_triangle upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "F" => GaussianGammaDigammaReal.nameF
local notation "fd" => GaussianGammaDigammaReal.data

def gain (K : PTm n) : PTm n := K*(K+one)

def window (a b K : PTm n) : Fm PTm n := source a b ⋏ le b (K*a)

def input (a b c d K X D : PTm n) : Fm PTm n :=
  window a b K ⋏ (window c d K ⋏ (le one D ⋏ distanceBounded (fraction a b) (fraction c d) X D))

ipra_subst gain [one]

ipra_subst window

ipra_subst input

private theorem common_radius (p a c b K : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hac : Γ ⊢[PRAAx] le a c) (hm : Γ ⊢[PRAAx] le b (K*a)) :
    Γ ⊢[PRAAx] radius (fstT (ap2 nameF p (data a b))) (fstT (ap2 nameF p (data c b)))
      (gain K*monus c a*unit p+two*b) (b*unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hb := ha.andE₂
  have lhs := GaussianGammaDigammaMonotone.monotone_at p p a c b ha hc hac
  have rhs := GaussianGammaDigammaLipschitz.compact_upper_at p p a c b K ha hc hac hm
  exact radius_of_upper _ _ _ _
    (upper_mono _ _ _ _ _ _ (positive_product _ _ hp hp) lhs (by ipra_le 𝔞(gain K)*𝔞(monus c a)*𝔞(unit p)^3))
    (upper_mono _ _ _ _ _ _ (denominator_positive _ _ _ hb) rhs
      (by unfold gain rateNumerator rateDenominator; ipra_le 0))

private theorem cleared_gap (a b c d X D : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (hD : Γ ⊢[PRAAx] le one D) (hac : Γ ⊢[PRAAx] le (d*a) (b*c))
    (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) X D) :
    Γ ⊢[PRAAx] le (D*monus (b*c) (d*a)) (X*(d*b)) := by
  have left := fraction_real_part a b hb
  have right := fraction_real_part c d hd
  have hg := GaussianPositiveRationalLogarithmVariation.original_time_distance a b c d X D hb hd hD
    (radius_congr left right (.eqRefl _) (.eqRefl _) (scalar_coordinate_distance _ _ _ _ hD h))
  have e : Γ ⊢[PRAAx] gap a b c d ≐ monus (b*c) (d*a) :=
    (congrAdd (congrMonus (mul_comm a d) (.eqRefl _)) (congrMonus (.eqRefl _) (mul_comm a d))).eqTrans
      ((congrAdd hac (.eqRefl _)).eqTrans (zero_add _))
  exact le_congr (congrMul (.eqRefl _) e) (by ipra_ring) hg

private theorem real_cross_scaled (a b s : PTm n) (h : Γ ⊢[PRAAx] source a b) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] crossEquivalent nameF F (data (s*a) (s*b)) (fd a b) :=
  cross_trans _ _ _ _ _ _ (GaussianGammaDigammaRescaling.original_rescaling a b s h hs) (original_cross a b h)

private theorem observation_radius (U V : PR 2) (p x y : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent U V x y) :
    Γ ⊢[PRAAx] radius (fstT (ap2 U p x)) (fstT (ap2 V p y)) two (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hpp := positive_product _ _ hp hp
  exact radius_mono _ _ _ _ _ _ hpp (scalar_coordinate_distance _ _ _ _ hpp (cross_at _ _ _ _ p p h)) (by ipra_le 0)

private theorem ordered_real_diagonal (p a b c d K X D : PTm n)
    (ha : Γ ⊢[PRAAx] window a b K) (hc : Γ ⊢[PRAAx] window c d K) (hD : Γ ⊢[PRAAx] le one D)
    (hac : Γ ⊢[PRAAx] le (d*a) (b*c)) (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) X D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p (fd a b)) (ap2 F p (fd c d))
      (diagonalNumerator (gain K*X) D (num 6) p) (diagonalDenominator D p) := by
  let A := d*a
  let C := b*c
  let B := d*b
  let P := unit p
  let x := ap2 F p (fd a b)
  let y := ap2 F p (fd c d)
  have hb := ha.andE₁.andE₂
  have hd := hc.andE₁.andE₂
  have hB := positive_product d b hd hb
  have hp := unit_positive (Γ := Γ) p
  have first : Γ ⊢[PRAAx] source A B := .andI (positive_product _ _ hd ha.andE₁.andE₁) hB
  have last : Γ ⊢[PRAAx] source C B := .andI (positive_product _ _ hb hc.andE₁.andE₁) hB
  have margin : Γ ⊢[PRAAx] le B (K*A) := by dsimp only [A,B]; ipra_le 𝔞(d)*sl ha.andE₂
  have left := observation_radius F nameF p (fd a b) (data A B)
    (cross_symm _ _ _ _ (real_cross_scaled a b d ha.andE₁ hd))
  have rightCross : Γ ⊢[PRAAx] crossEquivalent nameF F (data C B) (fd c d) :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _
      (GaussianGammaDigammaRescale.datum_congr (.eqRefl _) (mul_comm b d)) (.eqRefl _)
      (real_cross_scaled c d b hc.andE₁ hb)
  have right := observation_radius nameF F p (data C B) (fd c d) rightCross
  have joined := radius_triangle _ _ _ _ _ _ _
    (radius_triangle _ _ _ _ _ _ _ left (common_radius p A C B K first last hac margin)) right
  have hgap := cleared_gap a b c d X D hb hd hD hac h
  have final : Γ ⊢[PRAAx] radius (fstT x) (fstT y) (diagonalNumerator (gain K*X) D (num 6) p) (diagonalDenominator D p) := by
    apply radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp (positive_product _ _ hB hp)) hp) joined
    dsimp only [diagonalNumerator,diagonalDenominator,A,C,B,P]
    ipra_le 𝔞(gain K)*𝔞(unit p)^4*sl hgap
  have xr := real_sample_at (Γ := Γ) F (fd a b) p (name_real a b)
  have yr := real_sample_at (Γ := Γ) F (fd c d) p (name_real c d)
  exact distance_congr (canonical_axis_roundtrip x xr.andE₁ xr.andE₂) (canonical_axis_roundtrip y yr.andE₁ yr.andE₂)
    (.eqRefl _) (.eqRefl _) (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (positive_product _ _ hD hp) final)

theorem real_diagonal (p a b c d K X D : PTm n) (h : Γ ⊢[PRAAx] input a b c d K X D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p (fd a b)) (ap2 F p (fd c d))
      (diagonalNumerator (gain K*X) D (num 6) p) (diagonalDenominator D p) := by
  have ha := h.andE₁
  have hc := h.andE₂.andE₁
  have hD := h.andE₂.andE₂.andE₁
  have close := h.andE₂.andE₂.andE₂
  refine .orE (le_total (d*a) (b*c)) ?_ ?_
  · exact ordered_real_diagonal p a b c d K X D ha.wk hc.wk hD.wk Prf.hyp0 close.wk
  · exact distance_symmetric _ _ _ _ (positive_product _ _ hD.wk (unit_positive p))
      (ordered_real_diagonal p c d a b K X D hc.wk ha.wk hD.wk Prf.hyp0 (distance_symmetric _ _ _ _ hD.wk close.wk))

theorem real_rate (a b c d K X D : PTm n) (h : Γ ⊢[PRAAx] input a b c d K X D) :
    Γ ⊢[PRAAx] independentRate F F (fd a b) (fd c d) (gain K*X) D := by
  refine GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 6) h.andE₂.andE₂.andE₁
    (GaussianGammaDigammaReal.name_regular a b h.andE₁.andE₁) (GaussianGammaDigammaReal.name_regular c d h.andE₂.andE₁.andE₁) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (sh a) (sh b) (sh c) (sh d) (sh K) (sh X) (sh D) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift
  simpa only [diagonalEnvelope,GaussianGammaDigammaReal.subst_data,subst_gain,PTm.subst_mul,PTm.subst_num,Syn.shift,sh] using
    real_diagonal (var 0) (sh a) (sh b) (sh c) (sh d) (sh K) (sh X) (sh D) hs

theorem original_rate (a b c d K X D : PTm n) (ha : Γ ⊢[PRAAx] window a b K) (hc : Γ ⊢[PRAAx] window c d K)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) X D) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data a b) (data c d) (gain K*X) D :=
  GaussianNamedRateTransport.transport F F nameF nameF (fd a b) (fd c d) (data a b) (data c d) (gain K*X) D hD
    (real_rate a b c d K X D (.andI ha (.andI hc (.andI hD h)))) (original_cross a b ha.andE₁) (original_cross c d hc.andE₁)

theorem original_observations (a b c d K X D p q : PTm n) (ha : Γ ⊢[PRAAx] window a b K) (hc : Γ ⊢[PRAAx] window c d K)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) X D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data a b)) (ap2 nameF q (data c d))
      (rateNumerator (gain K*X) D p q) (rateDenominator D p q) :=
  rate_at _ _ _ _ _ _ p q (original_rate a b c d K X D ha hc hD h)

theorem actual_original_positive_digamma_compact_rational_Lipschitz_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        independentRate nameF nameF (data (var 0) (var 1)) (data (var 2) (var 3)) (gain (var 4)*var 5) (var 6)) :=
  closeUniv 7 (.impI (original_rate _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaCompactLipschitz
