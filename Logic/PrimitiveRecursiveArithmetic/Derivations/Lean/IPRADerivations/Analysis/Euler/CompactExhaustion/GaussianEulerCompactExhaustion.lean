import IPRADerivations.Analysis.Euler.CompactExhaustion.Tails.GaussianEulerCompactExhaustionUpperTail
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteIntervalRate
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteSmallRationalEndpoint
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# Ordinary Euler quadrature on arbitrary enclosing rational panels

The left endpoint can be anywhere below the original lower cutoff.
Split at the original upper cutoff and use the bound for the remaining
upper tail, including when its panel has zero width. The ordinary
panel may use any certified reciprocal lower margin for its clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustion

open_ipra
open GaussianGammaIntegralCutoffs (etaDen top height)
open GaussianEulerCompactAdditivity (nameF data intervalSource)
open GaussianEulerCompactModulus (lipschitz)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNameArithmetic (addF addData)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaCompactCutoffSplit (euler_data_congr add_data_congr)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A k a C E G T : PTm n) : Fm PTm n :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏
    (GaussianEulerPositivePowerChartImageCompactModulus.source z R B a C E G T ⋏
      (le (a*etaDen k A R) E ⋏ le (top k A R*E) (a+C)))

def prefixWidth (k A R a E : PTm n) : PTm n := monus (top k A R*E) a
def suffixWidth (k A R a C E : PTm n) : PTm n := monus (a+C) (top k A R*E)
def budget (A R : PTm n) : PTm n := (two*majorant R+one)+A
def denominator (k : PTm n) : PTm n := unit (k+num 6)

theorem full_source (z R B A k a C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k a C E G T) : Γ ⊢[PRAAx]
    intervalSource z R B a C E T :=
  .andI (.andI h.andE₂.andE₁.andE₁.andE₁
    (.andI h.andE₂.andE₁.andE₂.andE₁.andE₂ h.andE₂.andE₁.andE₁.andE₂.andE₂))
    (.andI h.andE₂.andE₁.andE₂.andE₁.andE₁
      (le_congr (.eqRefl _) (mul_comm T E) h.andE₂.andE₁.andE₂.andE₂.andE₂))

theorem width_data (z R B A k a C E G T : PTm n) (h : Γ ⊢[PRAAx] source z R B A k a C E G T) :
    Γ ⊢[PRAAx] (le one (prefixWidth k A R a E) ⋏
      ((a+prefixWidth k A R a E ≐ top k A R*E) ⋏
        (top k A R*E+suffixWidth k A R a C E ≐ a+C))) := by
  let X := top k A R*E
  have hE := h.andE₂.andE₁.andE₂.andE₁.andE₂
  have ha : Γ ⊢[PRAAx] le a E := le_trans
    (le_congr ((mul_comm a one).eqTrans (one_mul _)) (.eqRefl _)
      (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl a) (GaussianGammaIntegralCutoffs.eta_den_positive k A R)))
    h.andE₂.andE₂.andE₁
  have ht : Γ ⊢[PRAAx] le two (top k A R) :=
    le_congr (one_mul two) (mul_comm (height k A R) two)
      (mul_le_mul_right two (GaussianGammaIntegralCutoffs.height_positive k A R))
  have he : Γ ⊢[PRAAx] le (a+one) X := le_trans (add_le_add₂ ha hE)
    (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right E ht))
  have cut : Γ ⊢[PRAAx] X ≐ a+(one+monus X (a+one)) :=
    (eq_add_of_le he).eqTrans (by ipra_ring)
  have positive : Γ ⊢[PRAAx] le one (prefixWidth k A R a E) :=
    le_congr (.eqRefl _) ((congrMonus cut (.eqRefl a)).eqTrans (add_monus' _ a)).eqSymm
      (le_add_right one (monus X (a+one)))
  exact .andI positive (.andI (eq_add_of_le (le_trans (le_add_right a one) he)).eqSymm
    (eq_add_of_le h.andE₂.andE₂.andE₂).eqSymm)

theorem prefix_source (z R B A k a C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k a C E G T) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteIntervalRate.source k z R B A a (prefixWidth k A R a E) E T := by
  have hw := width_data z R B A k a C E G T h
  have hf := full_source z R B A k a C E G T h
  have he := le_trans h.andE₂.andE₂.andE₂ hf.andE₂.andE₂
  exact .andI (.andI h.andE₁ (.andI hf.andE₂.andE₁ (.andI hw.andE₁
    (.andI hf.andE₁.andE₂.andE₁ (le_congr hw.andE₂.andE₁.eqSymm (.eqRefl _) he))))) hw.andE₂.andE₁

theorem suffix_source (z R B A k a C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k a C E G T) : Γ ⊢[PRAAx]
    GaussianEulerCompactExhaustionUpperTail.source z R B k A (suffixWidth k A R a C E) E E T := by
  have he := h.andE₂.andE₁.andE₂.andE₁.andE₂
  have eq := (width_data z R B A k a C E G T h).andE₂.andE₂
  exact .andI h.andE₁.andE₁.andE₂.andE₁
    (.andI he (.andI he (le_congr eq.eqSymm (.eqRefl _) h.andE₂.andE₁.andE₂.andE₂.andE₂)))

theorem widths_sum (z R B A k a C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k a C E G T) : Γ ⊢[PRAAx]
    prefixWidth k A R a E+suffixWidth k A R a C E ≐ C := by
  let L := prefixWidth k A R a E
  let U := suffixWidth k A R a C E
  have w := (width_data z R B A k a C E G T h).andE₂
  have he : Γ ⊢[PRAAx] a+(L+U) ≐ a+C :=
    (by ipra_ring : Γ ⊢[PRAAx] a+(L+U) ≐ (a+L)+U).eqTrans
      ((congrAdd w.andE₁ (.eqRefl U)).eqTrans w.andE₂)
  exact add_left_cancel he

theorem split_positive_suffix (z R B A k a C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k a C E G T)
    (hu : Γ ⊢[PRAAx] le one (suffixWidth k A R a C E)) : Γ ⊢[PRAAx]
    crossEquivalent nameF (addF nameF nameF) (data z R B a C E T)
      (addData (data z R B a (prefixWidth k A R a E) E T)
        (data z R B (top k A R*E) (suffixWidth k A R a C E) E T)) := by
  let L := prefixWidth k A R a E
  let U := suffixWidth k A R a C E
  have hs := widths_sum z R B A k a C E G T h
  have hw := width_data z R B A k a C E G T h
  have hf := full_source z R B A k a C E G T h
  have splitInput : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.source z R B a L U E T :=
    .andI (.andI hf.andE₁ (.andI hf.andE₂.andE₁
      (le_congr (congrAdd (.eqRefl a) hs).eqSymm (.eqRefl _) hf.andE₂.andE₂))) (.andI hw.andE₁ hu)
  have split := GaussianEulerCompactAdditivity.name_additivity z R B a L U E T splitInput
  exact cross_data_congr _ _ _ _ _ _
    (euler_data_congr z R B a (L+U) E T a C E T (.eqRefl _) hs (.eqRefl _) (.eqRefl _))
    (add_data_congr _ _ _ _ (.eqRefl _)
      (euler_data_congr z R B (a+L) U E T (top k A R*E) U E T hw.andE₂.andE₁ (.eqRefl _) (.eqRefl _) (.eqRefl _))) split

private theorem suffix_samples (z R B A k C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactExhaustionUpperTail.source z R B k A C E E T) :
    Γ ⊢[PRAAx] GaussianNamedSmallAddendRate.tailSamples nameF
      (data z R B (top k A R*E) C E T) (two*majorant R) (unit (height k A R)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerCompactExhaustionUpperTail.source
      (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift k) (Syn.shift A) (Syn.shift C) (Syn.shift E)
        (Syn.shift E) (Syn.shift T) := by
    simpa only [Fm.shift,Syn.shift,GaussianEulerCompactExhaustionUpperTail.subst_source] using h.shift
  refine .allI ?_
  simpa [GaussianNamedSmallAddendRate.tailSamples,GaussianEulerCompactExhaustionUpperTail.point,
    GaussianEulerNamedUpperTail.numerator,GaussianEulerNamedUpperTail.denominator,
    top,height,GaussianGammaIntegralCutoffs.tailCoefficient,Syn.shift] using
    (.andI (GaussianEulerCompactExhaustionUpperTail.point_canonical (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift k) (Syn.shift A) (Syn.shift C) (Syn.shift E) (Syn.shift E) (Syn.shift T))
      (GaussianEulerCompactExhaustionUpperTail.original_named_upper_tail (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B)
        (Syn.shift k) (Syn.shift A) (Syn.shift C) (Syn.shift E) (Syn.shift E) (Syn.shift T) hs))

theorem rate_to_prefix (z R B A k a C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k a C E G T) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data z R B a C E T) (data z R B a (prefixWidth k A R a E) E T)
      (two*majorant R) (unit (height k A R)) := by
  let L := prefixWidth k A R a E
  let U := suffixWidth k A R a C E
  let P := data z R B a L E T
  let F := data z R B a C E T
  let X := top k A R*E
  let S := data z R B X U E T
  let D := unit (height k A R)
  have hl := GaussianEulerCompactAdditivity.name_regular z R B a L E T
    (GaussianEulerIncompleteInterval.original_interval_source _ _ _ _ _ _ _ _ (prefix_source z R B A k a C E G T h).andE₁)
  have hf := GaussianEulerCompactAdditivity.name_regular z R B a C E T (full_source z R B A k a C E G T h)
  refine .orE (zero_or_succ U) ?_ ?_
  · have hlc : (U ≐ zero)::Γ ⊢[PRAAx] L ≐ C :=
      ((congrAdd (.eqRefl L) Prf.hyp0).eqTrans (by ipra_ring : (U ≐ zero)::Γ ⊢[PRAAx] L+zero ≐ L)).eqSymm.eqTrans
        (widths_sum z R B A k a C E G T h.wk)
    have ep : (U ≐ zero)::Γ ⊢[PRAAx] P ≐ F :=
      euler_data_congr z R B a L E T a C E T (.eqRefl _) hlc (.eqRefl _) (.eqRefl _)
    have same := cross_data_congr nameF nameF P F P P ep (.eqRefl P) (cross_refl nameF P hl.wk)
    have self := GaussianNamedDifferenceRate.self_rate (Γ := (U ≐ zero)::Γ) nameF P hl.wk
    have relaxed := GaussianNamedRateRadius.weaken nameF nameF P P zero one (two*majorant R) D
      (le_refl one) (unit_positive _) (le_congr (by ipra_ring) (.eqRefl _) (zero_le _)) self
    exact GaussianNamedRateTransport.transport nameF nameF nameF nameF P P F P _ _
      (unit_positive _) relaxed same (cross_refl nameF P hl.wk)
  · have hu : (U ≐ succ (pred U))::Γ ⊢[PRAAx] le one U :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred U))
    have hs := suffix_source (Γ := (U ≐ succ (pred U))::Γ) z R B A k a C E G T h.wk
    have tail := GaussianEulerCompactExhaustionUpperTail.point_regular z R B k A U E E T hs
    have rate := GaussianNamedSmallAddendRate.independent_rate nameF nameF nameF P F S (two*majorant R) D
      (unit_positive _) hl.wk hf.wk tail (split_positive_suffix z R B A k a C E G T h.wk hu)
      (suffix_samples z R B A k U E T hs)
    exact GaussianNamedRateComposition.symmetric nameF nameF P F _ D (unit_positive _) rate

private theorem weaken_height (F H : PR 2) (x y M k A R : PTm n)
    (h : Γ ⊢[PRAAx] independentRate F H x y M (unit (height k A R))) : Γ ⊢[PRAAx]
    independentRate F H x y M (denominator k) := by
  have later : Γ ⊢[PRAAx] le (k+num 6) (height k A R) := by
    apply le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+num 4)
    unfold height
    ipra_ring
  exact GaussianNamedRateRadius.weaken F H x y M _ M _ (unit_positive _) (unit_positive _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl M) (GaussianExponentialReference.unit_monotone later)) h

theorem image_clock_equivalent (z R B A k a C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k a C E G T) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (GaussianEulerPositivePowerChartImageCompactModulus.data z R B a C E G T)
      (data z R B a C E T) :=
  GaussianCompactMeshIndependence.name_independence evaluatorF a C E (lipschitz R G T) T
    (lipschitz R E T) T (fixedData z B)
    (.andI (GaussianEulerPositivePowerChartImageCompactModulus.compact_input z R B a C E G T h.andE₂.andE₁)
      (GaussianEulerCompactAdditivity.compact_input z R B a C E T (full_source z R B A k a C E G T h)))

theorem original_gamma_rate (z R B A k a C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k a C E G T) : Γ ⊢[PRAAx]
    independentRate nameF GaussianGammaReciprocalInverse.gammaF
      (GaussianEulerPositivePowerChartImageCompactModulus.data z R B a C E G T)
      (GaussianGammaReciprocalInverse.gammaData z R B A) (budget A R) (denominator k) := by
  let F := data z R B a C E T
  let D := denominator k
  let L := prefixWidth k A R a E
  let P := data z R B a L E T
  let U := GaussianEulerIncompleteName.data z R B A a E
  let J := GaussianGammaReciprocalInverse.gammaData z R B A
  let UFn := GaussianEulerIncompleteName.upperF
  let JFn := GaussianGammaReciprocalInverse.gammaF
  have hD : Γ ⊢[PRAAx] le one D := unit_positive _
  have cut := prefix_source z R B A k a C E G T h
  have tail : Γ ⊢[PRAAx] independentRate nameF nameF F P (two*majorant R) D :=
    weaken_height _ _ _ _ _ k A R (rate_to_prefix z R B A k a C E G T h)
  have piece : Γ ⊢[PRAAx] independentRate nameF UFn P U one D :=
    GaussianEulerIncompleteIntervalRate.original_interval_rate k z R B A a L E T cut
  have sm : Γ ⊢[PRAAx] GaussianEulerIncompleteSmallRationalEndpoint.source z R B A k a E :=
    .andI (GaussianEulerIncompleteInterval.left_source z R B A a L E T cut.andE₁) h.andE₂.andE₂.andE₁
  have lower : Γ ⊢[PRAAx] independentRate UFn JFn U J A D :=
    weaken_height _ _ _ _ _ k A R
      (GaussianEulerIncompleteSmallRationalEndpoint.original_upper_small_rational_rate z R B A k a E sm)
  have first := GaussianNamedRateComposition.same_denominator nameF nameF UFn F P U _ D one hD tail piece
  have all := GaussianNamedRateComposition.same_denominator nameF UFn JFn F U J _ D A hD first lower
  exact GaussianNamedRateTransport.transport nameF JFn nameF JFn F J _ J _ D hD all
    (image_clock_equivalent z R B A k a C E G T h)
    (cross_refl JFn J (GaussianEulerIntegralGammaIdentification.original_gamma_regular z R B A h.andE₁))

theorem original_improper_rate (z R B A k a C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k a C E G T) : Γ ⊢[PRAAx]
    independentRate nameF GaussianEulerImproperName.nameF
      (GaussianEulerPositivePowerChartImageCompactModulus.data z R B a C E G T)
      (GaussianEulerImproperName.data z R B A) (budget A R) (denominator k) :=
  GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive _)
    (original_gamma_rate z R B A k a C E G T h)
    (cross_refl _ _ (GaussianEulerPositivePowerChartImageCompactModulus.name_regular z R B a C E G T h.andE₂.andE₁))
    (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B A h.andE₁)

theorem actual_original_Euler_improper_exhaustion_by_enclosing_panels_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        independentRate nameF GaussianEulerImproperName.nameF
          (GaussianEulerPositivePowerChartImageCompactModulus.data (var 0) (var 1) (var 2) (var 5) (var 6) (var 7) (var 8) (var 9))
          (GaussianEulerImproperName.data (var 0) (var 1) (var 2) (var 3)) (budget (var 3) (var 1)) (denominator (var 4))) :=
  closeUniv 10 (.impI (original_improper_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustion
