import IPRADerivations.Analysis.Stirling.Bounds.Logarithmic.GaussianStirlingGlobalBounds
import IPRADerivations.Analysis.Stirling.GammaLogarithm.GaussianStirlingRationalLogShift

/-!
# Fractional arguments in the translated Stirling estimate

Write A/B as a nonnegative integer plus r/B with (1le rle B).
Using a positive fractional part also covers integer inputs, where
r=B. The reference integer is at least the original cofinal cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 780000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsShiftArguments

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianRationalHorner (positive_product)
open GaussianStirlingNames (source logXF logXData logGammaF logGammaData log_x_regular log_gamma_regular)
open GaussianStirlingGlobalBounds (steps)
open GaussianStirlingTelescope (shifted)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fractionNumerator (a b : PTm n) : PTm n := succ (rem (pred a) b)
def integerAnchor (a b p : PTm n) : PTm n := steps p+quo (pred a) b
def shiftedNumerator (i r b : PTm n) : PTm n := b*i+r
def positiveFraction (r b : PTm n) : PTm n := fraction r b
def ratioData (i r b : PTm n) : PTm n := GaussianPositiveRationalLogarithm.data (shiftedNumerator i r b) (b*i)
def deltaF : PR 2 := GaussianNamedDifference.nameF logGammaF logGammaF
def deltaData (i r b : PTm n) : PTm n :=
  GaussianNamedDifference.data (logGammaData (shiftedNumerator i r b) b) (logGammaData i one)
def slopeF : PR 2 := multiplyF constantF logXF
def slopeData (i r b : PTm n) : PTm n := multiplyData constantF logXF (positiveFraction r b) (logXData i one)

ipra_subst fractionNumerator
ipra_subst integerAnchor
ipra_subst shiftedNumerator
ipra_subst ratioData
ipra_subst deltaData
ipra_subst slopeData [positiveFraction]

theorem fractional_guard (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le one (fractionNumerator a b) ⋏ le (fractionNumerator a b) b :=
  .andI (zero_lt_succ _) (div_mod_at (x := pred a) (pos_of_one_le hb)).andE₂

theorem anchor_later (a b p : PTm n) : Γ ⊢[PRAAx] le (steps p) (integerAnchor a b p) :=
  le_add_right _ _

theorem anchor_pred_later (a b p : PTm n) : Γ ⊢[PRAAx] le (GaussianStirlingIntegerLimit.index p) (pred (integerAnchor a b p)) := by
  have h : Γ ⊢[PRAAx] le one (integerAnchor a b p) := le_trans (zero_lt_succ _) (anchor_later a b p)
  have e := natEq (pos_of_one_le h)
  have j := anchor_later (Γ := Γ) a b p
  dsimp [steps] at j
  ipra_le sl j using linear_combination -e

theorem argument_readback (a b p : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    shiftedNumerator (integerAnchor a b p) (fractionNumerator a b) b ≐ shifted a b (steps p) := by
  have d := natEq (div_mod_at (x := pred a) (pos_of_one_le hs.andE₂)).andE₁
  have e := natEq (pos_of_one_le hs.andE₁)
  dsimp [shiftedNumerator,integerAnchor,fractionNumerator,shifted]
  apply deriveNat
  ipra_simps
  linear_combination -d-e

theorem shifted_positive (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le one (shiftedNumerator i r b) :=
  le_trans (positive_product _ _ hb hi) (le_add_right _ _)

theorem log_ratio_regular (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] pointCN logF (ratioData i r b) :=
  GaussianPositiveRationalLogarithm.name_regular _ _ (.andI (shifted_positive _ _ _ hi hb) (positive_product _ _ hb hi))

theorem delta_regular (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] pointCN deltaF (deltaData i r b) := GaussianNamedDifference.name_regular _ _ _ _
    (log_gamma_regular _ _ (.andI (shifted_positive _ _ _ hi hb) hb)) (log_gamma_regular _ _ (.andI hi (le_refl one)))

theorem slope_regular (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx] pointCN slopeF (slopeData i r b) :=
  multiply_fast _ _ _ _ (constant_regular _) (log_x_regular _ _ (.andI hi (le_refl one)))

theorem shifted_log (i r b : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent logXF (addF logXF logF) (logXData (shiftedNumerator i r b) b)
      (addData (logXData i one) (ratioData i r b)) := by
  let z := shiftedNumerator i r b
  let d := ratioData i r b
  let v := logXData i one
  let h := GaussianPositiveRationalLogarithm.data i one
  let o := GaussianPositiveRationalLogarithm.data (i*z) (one*(b*i))
  have hz : Γ ⊢[PRAAx] source z b := .andI (shifted_positive _ _ _ hi hb) hb
  have hx : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have hd : Γ ⊢[PRAAx] source z (b*i) := .andI hz.andE₁ (positive_product _ _ hb hi)
  have ho : Γ ⊢[PRAAx] source (i*z) (one*(b*i)) :=
    .andI (positive_product _ _ hi hz.andE₁) (positive_product _ _ (le_refl one) hd.andE₂)
  have first := cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original z b hz)
  have same := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper z b (i*z) (one*(b*i)) hz ho (by ipra_ring)
  have product := GaussianEulerPositiveTimePowerProduct.logarithm_product i one z (b*i) (.andI hx hd)
  have hr := log_ratio_regular i r b hi hb
  have final := add_cross logF logXF logF logF h v d d
    (GaussianPositiveRationalLogarithm.name_regular i one hx) (log_x_regular i one hx) hr hr
    (GaussianHarmonicLogarithmName.cross_original i one hx) (cross_refl _ _ hr)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ same (cross_trans _ _ _ _ _ _ product final))

end LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsShiftArguments
