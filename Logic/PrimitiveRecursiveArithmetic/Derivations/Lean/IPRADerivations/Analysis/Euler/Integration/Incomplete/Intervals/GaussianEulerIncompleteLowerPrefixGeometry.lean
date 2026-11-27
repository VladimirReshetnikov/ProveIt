import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteName
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactAlignment

/-!
# Original lower Euler pieces below a dyadic endpoint

For positive a/b<=1/etaDen(k), the later original lower piece and its
remaining interval up to 1/etaDen(k) share one explicit denominator.
All three actual compact sources, the two original rescalings, and
strict additivity are derived from the numerical input guards. The
equal-endpoint case retains the literal zero-width remainder.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteLowerPrefixGeometry

open_ipra
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianEulerCompactAdditivity (nameF data intervalSource)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def start (k A R b : PTm n) : PTm n := b*etaDen k A R
def firstWidth (k j A R a b : PTm n) : PTm n := etaDen k A R*GaussianEulerIncompleteCutoff.lowerWidth j A R a b
def restWidth (k j A R a b : PTm n) : PTm n := etaDen j A R*monus b (a*etaDen k A R)
def denominator (k j A R b : PTm n) : PTm n := b*etaDen k A R*etaDen j A R
def originalData (z R B A j a b : PTm n) : PTm n := GaussianEulerIncompleteCutoffParts.lowerData z R B j A a b
def firstData (z R B A k j a b : PTm n) : PTm n :=
  data z R B (start k A R b) (firstWidth k j A R a b) (denominator k j A R b) (top j A R)
def restData (z R B A k j a b : PTm n) : PTm n :=
  data z R B (start k A R b+firstWidth k j A R a b) (restWidth k j A R a b) (denominator k j A R b) (top j A R)
def wholeData (z R B A k j a b : PTm n) : PTm n :=
  data z R B (start k A R b) (firstWidth k j A R a b+restWidth k j A R a b) (denominator k j A R b) (top j A R)
abbrev sumF : PR 2 := GaussianNameArithmetic.addF nameF nameF
def sumData (z R B A k j a b : PTm n) : PTm n :=
  GaussianNameArithmetic.addData (firstData z R B A k j a b) (restData z R B A k j a b)
def source (s z R B A k j a b : PTm n) : Fm PTm n :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏ (le one a ⋏ (le one b ⋏
    (le (a*etaDen k A R) b ⋏ (le k j ⋏ le (GaussianEulerIncompleteCutoff.clock s a b) j))))

ipra_subst start [etaDen, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst firstWidth [GaussianEulerIncompleteCutoff.lowerWidth, GaussianEulerIncompleteCutoff.splitPoint, etaDen, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst restWidth [etaDen, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst denominator [etaDen, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst originalData
ipra_subst firstData [top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst restData [top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst wholeData [top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst sumData
ipra_subst source [GaussianEulerIncompleteCutoff.clock, etaDen, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem cutoff_source (s z R B A k j a b : PTm n) (h : Γ ⊢[PRAAx] source s z R B A k j a b) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteCutoff.source z R B A a b :=
  .andI h.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁ (.andI h.andE₂.andE₁ h.andE₂.andE₂.andE₁))

theorem first_endpoint (s z R B A k j a b : PTm n) (h : Γ ⊢[PRAAx] source s z R B A k j a b) : Γ ⊢[PRAAx]
    start k A R b+firstWidth k j A R a b ≐ a*etaDen k A R*etaDen j A R := by
  have original := (GaussianEulerIncompleteCutoff.original_partition s j z R B A a b
    (cutoff_source s z R B A k j a b h) h.andE₂.andE₂.andE₂.andE₂.andE₂).andE₁
  exact (by unfold start firstWidth; ipra_ring : Γ ⊢[PRAAx]
    start k A R b+firstWidth k j A R a b ≐ etaDen k A R*(b+GaussianEulerIncompleteCutoff.lowerWidth j A R a b)).eqTrans
      ((congrMul (.eqRefl _) original).eqTrans (by unfold GaussianEulerIncompleteCutoff.splitPoint; ipra_ring))

theorem whole_endpoint (s z R B A k j a b : PTm n) (h : Γ ⊢[PRAAx] source s z R B A k j a b) : Γ ⊢[PRAAx]
    start k A R b+(firstWidth k j A R a b+restWidth k j A R a b) ≐ b*etaDen j A R := by
  have split := first_endpoint s z R B A k j a b h
  have remainder := (eq_add_of_le h.andE₂.andE₂.andE₂.andE₁).eqSymm
  exact ((by ipra_ring : Γ ⊢[PRAAx]
    start k A R b+(firstWidth k j A R a b+restWidth k j A R a b) ≐
      (start k A R b+firstWidth k j A R a b)+restWidth k j A R a b).eqTrans
    (congrAdd split (.eqRefl _))).eqTrans
      ((by unfold restWidth; ipra_ring : Γ ⊢[PRAAx]
        a*etaDen k A R*etaDen j A R+restWidth k j A R a b ≐
          etaDen j A R*(a*etaDen k A R+monus b (a*etaDen k A R))).eqTrans
        ((congrMul (.eqRefl _) remainder).eqTrans (mul_comm _ _)))

theorem whole_width (s z R B A k j a b : PTm n) (h : Γ ⊢[PRAAx] source s z R B A k j a b) : Γ ⊢[PRAAx]
    firstWidth k j A R a b+restWidth k j A R a b ≐ start k A R b*GaussianGammaCompactCutoffGeometry.lowerWidth k j A := by
  have refined := GaussianGammaCompactCutoffGeometry.eta_den_refinement k j A R h.andE₂.andE₂.andE₂.andE₂.andE₁
  have original : Γ ⊢[PRAAx] start k A R b+start k A R b*GaussianGammaCompactCutoffGeometry.lowerWidth k j A ≐ b*etaDen j A R :=
    (by ipra_ring : Γ ⊢[PRAAx] start k A R b+start k A R b*GaussianGammaCompactCutoffGeometry.lowerWidth k j A ≐
      start k A R b*(one+GaussianGammaCompactCutoffGeometry.lowerWidth k j A)).eqTrans
      ((congrMul (.eqRefl _) (GaussianGammaCompactCutoffGeometry.lower_endpoint k j A)).eqTrans
        ((by unfold start; ipra_ring : Γ ⊢[PRAAx] start k A R b*GaussianGammaCompactCutoffGeometry.ratio k j A ≐
          b*(GaussianGammaCompactCutoffGeometry.ratio k j A*etaDen k A R)).eqTrans (congrMul (.eqRefl _) refined.eqSymm)))
  ipra_lc natEq (whole_endpoint s z R B A k j a b h)-natEq original

theorem interval_sources (s z R B A k j a b : PTm n) (h : Γ ⊢[PRAAx] source s z R B A k j a b) : Γ ⊢[PRAAx]
    intervalSource z R B (start k A R b) (firstWidth k j A R a b) (denominator k j A R b) (top j A R) ⋏
      (intervalSource z R B (start k A R b+firstWidth k j A R a b) (restWidth k j A R a b) (denominator k j A R b) (top j A R) ⋏
        intervalSource z R B (start k A R b) (firstWidth k j A R a b+restWidth k j A R a b) (denominator k j A R b) (top j A R)) := by
  have hE := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have hF := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) j A R
  have hT := GaussianGammaIntegralCutoffs.top_positive (Γ := Γ) j A R
  have hb := h.andE₂.andE₂.andE₁
  have positiveStart : Γ ⊢[PRAAx] le one (start k A R b) := positive_product _ _ hb hE
  have positiveDen : Γ ⊢[PRAAx] le one (denominator k j A R b) := positive_product _ _ positiveStart hF
  have nativeSource : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B (denominator k j A R b) :=
    .andI h.andE₁.andE₁.andE₂.andE₁.andE₁ (.andI positiveDen h.andE₁.andE₁.andE₂.andE₁.andE₂)
  have cap : Γ ⊢[PRAAx] le (b*etaDen j A R) (denominator k j A R b*top j A R) :=
    le_congr (by ipra_ring) (by unfold denominator; ipra_ring)
      (mul_le_mul_right (b*etaDen j A R) (positive_product _ _ hE hT))
  have firstEnd : Γ ⊢[PRAAx] le (start k A R b+firstWidth k j A R a b) (denominator k j A R b*top j A R) :=
    le_trans (le_congr (first_endpoint s z R B A k j a b h).eqSymm (.eqRefl _)
      (mul_le_mul_right (etaDen j A R) h.andE₂.andE₂.andE₂.andE₁)) cap
  have wholeEnd := le_congr (whole_endpoint s z R B A k j a b h).eqSymm (.eqRefl _) cap
  have restEnd : Γ ⊢[PRAAx] le ((start k A R b+firstWidth k j A R a b)+restWidth k j A R a b)
      (denominator k j A R b*top j A R) := le_congr (by ipra_ring) (.eqRefl _) wholeEnd
  exact .andI (.andI nativeSource (.andI positiveStart firstEnd))
    (.andI (.andI nativeSource (.andI (le_trans positiveStart (le_add_right _ _)) restEnd))
      (.andI nativeSource (.andI positiveStart wholeEnd)))

theorem original_first_alignment (s z R B A k j a b : PTm n) (h : Γ ⊢[PRAAx] source s z R B A k j a b) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (firstData z R B A k j a b) (originalData z R B A j a b) := by
  let L := GaussianEulerIncompleteCutoff.lowerWidth j A R a b
  let F := GaussianEulerIncompleteCutoff.denominator j A R b
  let T := top j A R
  let E := etaDen k A R
  have old := (GaussianEulerIncompleteCutoffParts.piece_sources s j z R B A a b
    (cutoff_source s z R B A k j a b h) h.andE₂.andE₂.andE₂.andE₂.andE₂).andE₁
  have input : Γ ⊢[PRAAx] GaussianEulerCompactAlignment.source z R B b L F T T E :=
    .andI old.andE₁ (.andI old.andE₂.andE₁ (.andI (GaussianGammaIntegralCutoffs.eta_den_positive k A R)
      (.andI old.andE₂.andE₂ old.andE₂.andE₂)))
  have scaled := GaussianEulerCompactAlignment.aligned_names z R B b L F T T E input
  have actual : Γ ⊢[PRAAx] data z R B (E*b) (E*L) (E*F) T ≐ firstData z R B A k j a b :=
    GaussianGammaCompactCutoffSplit.euler_data_congr z R B _ _ _ _ _ _ _ _
      (by dsimp only [E,start]; ipra_ring) (.eqRefl _)
      (by dsimp only [E,F,denominator,GaussianEulerIncompleteCutoff.denominator]; ipra_ring) (.eqRefl _)
  exact cross_symm _ _ _ _ (GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF
    (originalData z R B A j a b) (originalData z R B A j a b) _ (firstData z R B A k j a b) (.eqRefl _) actual scaled)

theorem original_whole_alignment (s z R B A k j a b : PTm n) (h : Γ ⊢[PRAAx] source s z R B A k j a b) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (wholeData z R B A k j a b) (GaussianGammaCompactCutoffSplit.lowerData z R B k j A) := by
  let S := start k A R b
  let W := GaussianGammaCompactCutoffGeometry.lowerWidth k j A
  let F := etaDen j A R
  let T := top j A R
  have tailSource : Γ ⊢[PRAAx] GaussianGammaCompactCutoffSplit.source z R B k j A :=
    .andI h.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₁)
  have old := GaussianGammaCompactCutoffSplit.lower_source z R B k j A tailSource
  have positiveStart : Γ ⊢[PRAAx] le one S := positive_product _ _ h.andE₂.andE₂.andE₁
    (GaussianGammaIntegralCutoffs.eta_den_positive k A R)
  have input : Γ ⊢[PRAAx] GaussianEulerCompactAlignment.source z R B one W F T T S :=
    .andI old.andE₁ (.andI old.andE₂.andE₁ (.andI positiveStart (.andI old.andE₂.andE₂ old.andE₂.andE₂)))
  have scaled := GaussianEulerCompactAlignment.aligned_names z R B one W F T T S input
  have actual : Γ ⊢[PRAAx] data z R B (S*one) (S*W) (S*F) T ≐ wholeData z R B A k j a b :=
    GaussianGammaCompactCutoffSplit.euler_data_congr z R B _ _ _ _ _ _ _ _
      (by ipra_ring) (whole_width s z R B A k j a b h).eqSymm
      (.eqRefl _) (.eqRefl _)
  exact cross_symm _ _ _ _ (GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF
    (GaussianGammaCompactCutoffSplit.lowerData z R B k j A) (GaussianGammaCompactCutoffSplit.lowerData z R B k j A)
    _ (wholeData z R B A k j a b) (.eqRefl _) actual scaled)

theorem first_positive (s z R B A k j a b : PTm n) (h : Γ ⊢[PRAAx] source s z R B A k j a b) : Γ ⊢[PRAAx]
    le one (firstWidth k j A R a b) :=
  positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive k A R)
    (GaussianEulerIncompleteCutoff.original_partition s j z R B A a b
      (cutoff_source s z R B A k j a b h) h.andE₂.andE₂.andE₂.andE₂.andE₂).andE₂.andE₂.andE₂.andE₁

theorem rest_positive (k j A R a b : PTm n) (h : Γ ⊢[PRAAx] lt (a*etaDen k A R) b) : Γ ⊢[PRAAx]
    le one (restWidth k j A R a b) :=
  positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive j A R)
    (GaussianGammaCompactCutoffGeometry.gap_positive _ _ h)

theorem original_strict_additivity (s z R B A k j a b : PTm n) (h : Γ ⊢[PRAAx] source s z R B A k j a b)
    (hStrict : Γ ⊢[PRAAx] lt (a*etaDen k A R) b) : Γ ⊢[PRAAx]
    crossEquivalent nameF sumF (wholeData z R B A k j a b) (sumData z R B A k j a b) :=
  GaussianEulerCompactAdditivity.name_additivity z R B _ _ _ _ _
    (.andI (interval_sources s z R B A k j a b h).andE₂.andE₂
      (.andI (first_positive s z R B A k j a b h) (rest_positive k j A R a b hStrict)))

theorem rest_zero (k j A R a b : PTm n) (h : Γ ⊢[PRAAx] a*etaDen k A R ≐ b) : Γ ⊢[PRAAx]
    restWidth k j A R a b ≐ ConciseIPRA.PTm.zero :=
  (congrMul (.eqRefl _) ((congrMonus (.eqRefl b) h).eqTrans (monus_self b))).eqTrans (mul_zero _)

theorem whole_eq_first (z R B A k j a b : PTm n) (h : Γ ⊢[PRAAx] a*etaDen k A R ≐ b) : Γ ⊢[PRAAx]
    wholeData z R B A k j a b ≐ firstData z R B A k j a b :=
  GaussianGammaCompactCutoffSplit.euler_data_congr z R B _ _ _ _ _ _ _ _ (.eqRefl _)
    ((congrAdd (.eqRefl _) (rest_zero k j A R a b h)).eqTrans (add_zero _)) (.eqRefl _) (.eqRefl _)

theorem actual_original_incomplete_Euler_lower_prefix_alignments_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        crossEquivalent nameF nameF (firstData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
          (originalData (var 1) (var 2) (var 3) (var 4) (var 6) (var 7) (var 8)) ⋏
        crossEquivalent nameF nameF (wholeData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
          (GaussianGammaCompactCutoffSplit.lowerData (var 1) (var 2) (var 3) (var 5) (var 6) (var 4))) :=
  closeUniv 9 (.impI (.andI (original_first_alignment _ _ _ _ _ _ _ _ _ Prf.hyp0)
    (original_whole_alignment _ _ _ _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteLowerPrefixGeometry
