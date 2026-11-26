import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalRelativeLogarithmRealAxis
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdDerivativePositiveMargin
import IPRADerivations.Analysis.Names.Apartness.GaussianNamedClearedScalarQuotient

/-!
# The real relative increment of the original Barnes logarithm

The existing relative evaluator exponentiates to the Barnes value shift.
Real exponential injectivity identifies the relative evaluator with the
difference of the two full positive-axis logarithms.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmIncrement

open_ipra
open ComplexLogarithmRemainder (add im eval_im_code)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step shifted_center)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRealNameExponentialInjectivity (independent_radii_injective)
open GaussianRootAlgebra (equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianBarnesCanonicalPositiveLogarithm.nameF
local notation "ld" => GaussianBarnesCanonicalPositiveLogarithm.data
local notation "J" => GaussianBarnesCanonicalRelativeLogIncrement.nameF
local notation "jd" => GaussianBarnesCanonicalRelativeLogIncrement.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

def source (a c b R S h : PTm n) : Fm PTm n :=
  (GaussianBarnesCanonicalPositiveLogarithm.source a b R ⋏ GaussianBarnesCanonicalPositiveLogarithm.source c b S) ⋏
    (GaussianBarnesCanonicalRelativeLogIncrement.source (center a b) h R b ⋏
      (ZT.eq (im h) (ZT.ofNat zero) ⋏ equal (add (center a b) h) (center c b)))

theorem sum_cross (a c b R S h : PTm n) (hs : Γ ⊢[PRAAx] source a c b R S h) : Γ ⊢[PRAAx]
    crossEquivalent (addF L J) L (addData (ld a b R) (jd (center a b) h R b)) (ld c b S) := by
  let z := center a b
  let w := add z h
  let x := ld a b R
  let y := ld c b S
  let t := jd z h R b
  let F := addF L J
  let f := addData x t
  let u := exponentialInputData L x
  let v := exponentialInputData J t
  have hx := GaussianBarnesCanonicalPositiveLogarithm.regular a b R hs.andE₁.andE₁
  have hy := GaussianBarnesCanonicalPositiveLogarithm.regular c b S hs.andE₁.andE₂
  have ht := GaussianBarnesCanonicalRelativeLogIncrement.regular z h R b hs.andE₂.andE₁
  have hf : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN F f := add_fast L J x t hx ht
  have ex := exponential_input L x hx
  have et := exponential_input J t ht
  have ef := exponential_input F f hf
  have e₁ := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent L J F
    (U L x) (U J t) (U F f) x t f ex et ef (cross_refl _ _ hf)
  have ur := GaussianRadiusExponentialName.name_regular L _ _ ex
  have vr := GaussianRadiusExponentialName.name_regular J _ _ et
  have vz := GaussianBarnesCanonicalValue.regular z R b hs.andE₂.andE₁.andE₁
  have e₂ := GaussianGammaAdjacentCutoff.multiply_cross (E L) V (E J) (E J) u (vd z R b) v v
    ur vz vr vr (GaussianBarnesCanonicalPositiveLogarithm.exponential_value a b R hs.andE₁.andE₁) (cross_refl _ _ vr)
  have flip := GaussianNameRingLaws.multiply_commutative V (E J) (vd z R b) v vz vr
  have e₃ := GaussianBarnesCanonicalRelativeLogIncrement.exponential_restores z h R b hs.andE₂.andE₁
  have e₄ := GaussianBarnesCanonicalProperness.proper w (center c b) R S b b hs.andE₂.andE₁.andE₂.andE₁
    hs.andE₁.andE₂.andE₂ (GaussianGammaFiniteValueProperness.fraction_equal _ _ _ hs.andE₁.andE₁.andE₂.andE₁ hs.andE₂.andE₂.andE₂)
  have e₅ := GaussianBarnesCanonicalPositiveLogarithm.exponential_value c b S hs.andE₁.andE₂
  have xr := GaussianBarnesCanonicalPositiveLogarithmRealAxis.samples_axis a b R hs.andE₁.andE₁
  have yr := GaussianBarnesCanonicalPositiveLogarithmRealAxis.samples_axis c b S hs.andE₁.andE₂
  have tr := GaussianBarnesCanonicalRelativeLogarithmRealAxis.samples_axis z h R b hs.andE₁.andE₁.andE₂.andE₁
    (GaussianBarnesCanonicalPositiveLogarithmRealAxis.center_axis _ _) hs.andE₂.andE₂.andE₁
  exact independent_radii_injective F L (U F f) (U L y) f y ef (exponential_input L y hy)
    (GaussianNamedPositiveLogarithmScale.sum_axis L J x t xr tr) yr
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e₁) (cross_trans _ _ _ _ _ _ e₂
      (cross_trans _ _ _ _ _ _ flip (cross_trans _ _ _ _ _ _ e₃
        (cross_trans _ _ _ _ _ _ e₄ (cross_symm _ _ _ _ e₅))))))

theorem difference_cross (a c b R S h : PTm n) (hs : Γ ⊢[PRAAx] source a c b R S h) : Γ ⊢[PRAAx]
    crossEquivalent (Diff L L) J (dd (ld c b S) (ld a b R)) (jd (center a b) h R b) := by
  let t := jd (center a b) h R b
  let x := ld a b R
  let y := ld c b S
  have hx := GaussianBarnesCanonicalPositiveLogarithm.regular a b R hs.andE₁.andE₁
  have hy := GaussianBarnesCanonicalPositiveLogarithm.regular c b S hs.andE₁.andE₂
  have ht := GaussianBarnesCanonicalRelativeLogIncrement.regular (center a b) h R b hs.andE₂.andE₁
  have e := GaussianNamedDifferenceQuotientProperness.difference_proper L (addF L J) L L y (addData x t) x x hy
    (add_fast _ _ _ _ hx ht) hx hx (cross_symm _ _ _ _ (sum_cross a c b R S h hs)) (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ _ _ e (GaussianNamedClearedScalarQuotient.subtract_first_addend L J x t hx ht)

theorem rational_steps (a c b R : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hc : Γ ⊢[PRAAx] le one c)
    (hr : Γ ⊢[PRAAx] GaussianBarnesCanonicalRelativeLogIncrement.source (center a b) (step a c) R b) :
    Γ ⊢[PRAAx] crossEquivalent (Diff L L) J (dd (ld c b (c+b)) (ld a b R)) (jd (center a b) (step a c) R b) := by
  have realStep : Γ ⊢[PRAAx] ZT.eq (im (step a c)) (ZT.ofNat zero) := ZT.derive (by simp only [step,eval_im_code])
  exact difference_cross a c b R (c+b) (step a c) (.andI
    (.andI (.andI ha hr.andE₁) (GaussianBarnesCanonicalPositiveLogarithm.default_source c b hc hr.andE₁.andE₁))
    (.andI hr (.andI realStep (shifted_center a c b))))

theorem actual_original_Barnes_relative_logarithm_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let a := var 0
     let c := var 1
     let b := var 2
     let R := var 3
     let S := var 4
     let h := var 5
     source a c b R S h ⟶ crossEquivalent (Diff L L) J (dd (ld c b S) (ld a b R)) (jd (center a b) h R b)) :=
  closeUniv 6 (.impI (difference_cross _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmIncrement
