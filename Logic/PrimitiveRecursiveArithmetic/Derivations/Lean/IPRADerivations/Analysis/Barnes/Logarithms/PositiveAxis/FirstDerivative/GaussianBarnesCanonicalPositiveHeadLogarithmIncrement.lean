import IPRADerivations.Analysis.Names.Apartness.GaussianNamedClearedScalarQuotient
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalHeadRelativeRealAxis
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalPositiveHeadRealAxis
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalPositiveLogarithmRealAxis
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdDerivativePositiveMargin
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.FiniteFactors.GaussianBarnesCanonicalHeadDerivativeFractionProperness
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeLogIncrement

/-! The original kept-power logarithm difference realizes the original relative local logarithm
on the positive chart. Independent-radius real exponential injectivity fixes the branch. -/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveHeadLogarithmIncrement

open_ipra
open ComplexLogarithmRemainder (add im eval_im_code)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step shifted_center)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRealNameExponentialInjectivity (independent_radii_injective)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianBarnesCanonicalPositiveHeadLogarithm.nameF
local notation "ld" => GaussianBarnesCanonicalPositiveHeadLogarithm.data
local notation "J" => GaussianBarnesCanonicalHeadRelativeLog.nameF
local notation "jd" => GaussianBarnesCanonicalHeadRelativeLog.data
local notation "ed" => GaussianBarnesCanonicalHeadRelativeLog.expData
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "P" => GaussianBarnesCanonicalBaseProductShift.powerProduct
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

theorem sum_cross (A C B N : PTm n) (ha : Γ ⊢[PRAAx] le one A) (hc : Γ ⊢[PRAAx] le one C)
    (hb : Γ ⊢[PRAAx] le one B)
    (hj : Γ ⊢[PRAAx] GaussianBarnesCanonicalHeadRelativeLog.source (center A B) (step A C) B N) :
    Γ ⊢[PRAAx] crossEquivalent (addF L J) L
      (addData (ld A B N) (jd (center A B) (step A C) B N)) (ld C B N) := by
  let z := center A B
  let h := step A C
  let w := add z h
  let x := ld A B N
  let y := ld C B N
  let t := jd z h B N
  let F := addF L J
  let f := addData x t
  let v := ed z h B N
  have hx := GaussianBarnesCanonicalPositiveHeadLogarithm.regular A B N ha hb
  have hy := GaussianBarnesCanonicalPositiveHeadLogarithm.regular C B N hc hb
  have ht := GaussianBarnesCanonicalHeadRelativeLog.regular z h B N hj
  have hf := add_fast L J x t hx ht
  have ex := exponential_input L x hx
  have et := GaussianBarnesCanonicalHeadRelativeLog.exp_input z h B N hj
  have ef := exponential_input F f hf
  have e₁ := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent L J F
    (U L x) one (U F f) x t f ex et ef (cross_refl F f hf)
  have ur := GaussianRadiusExponentialName.name_regular L _ _ ex
  have vr := GaussianRadiusExponentialName.name_regular J _ _ et
  have pc := constant_regular (Γ := Γ) (P z B N)
  have e₂ := GaussianGammaAdjacentCutoff.multiply_cross (E L) constantF (E J) (E J)
    (exponentialInputData L x) (P z B N) v v ur pc vr vr
    (GaussianBarnesCanonicalPositiveHeadLogarithm.exponential_kept_powers A B N ha hb) (cross_refl _ _ vr)
  have e₃ := GaussianNameRingLaws.multiply_commutative constantF (E J) (P z B N) v pc vr
  have e₄ := GaussianBarnesCanonicalHeadRelativeLog.exponential_restores z h B N hj
  have plain := GaussianGammaFiniteValueProperness.fraction_equal _ _ _ hb (shifted_center A C B)
  have ep := GaussianBarnesCanonicalHeadDerivativeFractionProperness.original_power_equal w (center C B) B B N hb hb plain
  have e₅ := GaussianGammaWeierstrassApproximant.constant_data_cross _ _ ep
  have e₆ := GaussianBarnesCanonicalPositiveHeadLogarithm.exponential_kept_powers C B N hc hb
  have realStep : Γ ⊢[PRAAx] ZT.eq (im h) (ZT.ofNat zero) := ZT.derive (by simp only [h,step,eval_im_code])
  have xr := GaussianBarnesCanonicalPositiveHeadRealAxis.real_samples (Γ := Γ) A B N
  have yr := GaussianBarnesCanonicalPositiveHeadRealAxis.real_samples (Γ := Γ) C B N
  have tr := GaussianBarnesCanonicalPositiveLogarithmRealAxis.real_axis J t
    (GaussianBarnesCanonicalHeadRelativeRealAxis.relative_real z h B N hb
      (GaussianBarnesCanonicalPositiveLogarithmRealAxis.center_axis A B) realStep)
  exact independent_radii_injective F L (U F f) (U L y) f y ef (exponential_input L y hy)
    (GaussianNamedPositiveLogarithmScale.sum_axis L J x t xr tr) yr
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e₁) (cross_trans _ _ _ _ _ _ e₂
      (cross_trans _ _ _ _ _ _ e₃ (cross_trans _ _ _ _ _ _ e₄
        (cross_trans _ _ _ _ _ _ e₅ (cross_symm _ _ _ _ e₆))))))

theorem difference_cross (A C B N : PTm n) (ha : Γ ⊢[PRAAx] le one A) (hc : Γ ⊢[PRAAx] le one C)
    (hb : Γ ⊢[PRAAx] le one B)
    (hj : Γ ⊢[PRAAx] GaussianBarnesCanonicalHeadRelativeLog.source (center A B) (step A C) B N) :
    Γ ⊢[PRAAx] crossEquivalent (Diff L L) J (dd (ld C B N) (ld A B N))
      (jd (center A B) (step A C) B N) := by
  let z := center A B
  let h := step A C
  let t := jd z h B N
  let x := ld A B N
  let y := ld C B N
  have hx := GaussianBarnesCanonicalPositiveHeadLogarithm.regular A B N ha hb
  have hy := GaussianBarnesCanonicalPositiveHeadLogarithm.regular C B N hc hb
  have ht := GaussianBarnesCanonicalHeadRelativeLog.regular z h B N hj
  have e := GaussianNamedDifferenceQuotientProperness.difference_proper L (addF L J) L L y (addData x t) x x hy
    (add_fast _ _ _ _ hx ht) hx hx (cross_symm _ _ _ _ (sum_cross A C B N ha hc hb hj)) (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ _ _ e (GaussianNamedClearedScalarQuotient.subtract_first_addend L J x t hx ht)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveHeadLogarithmIncrement
