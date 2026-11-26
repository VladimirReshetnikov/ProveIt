import IPRADerivations.Analysis.Gamma.GaussianGammaFunctionalEquation
import IPRADerivations.Analysis.Gamma.GaussianGammaRadiusOverlap
import IPRADerivations.Analysis.Gamma.GaussianGammaInputProperness
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianRobinMeshExponential

/-!
# One shift of the original pole-free Gamma name

The original reciprocal-Gamma shift identifies its value at w with w
times its value at w+1. Invert this identity on the certified pole-free
domain. The terminal encoding can have its own disk and pole guard.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNativeShiftRecurrence

open_ipra
open GaussianBoundedInverseApartness (ones_equivalent reciprocal_matches_inverse)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadLower (pole_at translated_zero)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaReciprocalInverse (source gammaF gammaData gammaHeight gamma_regular gamma_product
  original_gamma_inverse constant_inverse inverse_pairs)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF)
open GaussianRationalHorner (ofGaussian ofGaussian_represents)
open GaussianRationalReciprocal (reciprocal reciprocal_identity normNumerator)
open GaussianRootAlgebra (equal normSq_equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def resultF : PR 2 := multiplyF constantF gammaF

def resultData (w z S B e : PTm n) : PTm n :=
  multiplyData constantF gammaF (reciprocal (ofGaussian w B)) (gammaData z S B e)

theorem input_norm_positive (w R B a d : PTm n) (hw : Γ ⊢[PRAAx] source w R B a d) :
    Γ ⊢[PRAAx] le one (normNumerator (ofGaussian w B)) := by
  have hb := hw.andE₁.andE₂.andE₁
  have ha := hw.andE₂.andE₁
  have hd := hw.andE₂.andE₂.andE₁
  have h0 := pole_at w B a d (two*R) zero hw.andE₂.andE₂.andE₂ (zero_le _)
  have hnorm := normSq_equal (translated_zero (Γ := Γ) w B)
  have lower := GaussianRationalLowerBounds.lower_from_representation _ w B a d hb hd
    (ofGaussian_represents w B hb) (le_congr (by ipra_ring) (congrMul (.eqRefl (d*d)) hnorm) h0)
  exact GaussianNameReciprocal.lower_norm_positive _ d hd
    (GaussianRationalLowerBounds.name_lower _ _ _ ha hd lower)

private theorem reciprocal_gamma_shift (w z R S B : PTm n)
    (hw : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source w R B)
    (hz : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z S B)
    (hShift : Γ ⊢[PRAAx] equal (shifted w B) z) :
    Γ ⊢[PRAAx] crossEquivalent GaussianGammaC7Name.nameF GaussianGammaFunctionalEquation.leftLimitF
      (GaussianGammaC7Name.data w R B)
      (multiplyData constantF GaussianGammaC7Name.nameF (ofGaussian w B) (GaussianGammaC7Name.data z S B)) := by
  let P := GaussianGammaC7Name.nameF
  let c := ofGaussian w B
  let x := GaussianGammaC7Name.data (shifted w B) (R+one) B
  let y := GaussianGammaC7Name.data z S B
  have hs := GaussianGammaEulerShiftLimit.shifted_source w R B hw
  have ht := GaussianGammaFiniteValueProperness.source_equal (shifted w B) z (R+one) B hs hShift
  have same := GaussianGammaInputProperness.original_C7_proper (shifted w B) z (R+one) B hs hShift
  have overlap := GaussianGammaRadiusOverlap.original_P_overlap z (R+one) S B ht hz
  have hx := GaussianGammaC7Name.name_regular (shifted w B) (R+one) B hs
  have hy := GaussianGammaC7Name.name_regular z S B hz
  have hc := constant_regular (Γ := Γ) c
  have replace := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF P P c c x y
    hc hc hx hy (cross_refl constantF c hc) (cross_trans _ _ _ _ _ _ same overlap)
  have shift := GaussianGammaFunctionalEquation.original_C20_shift w R B hw
    GaussianRobinMeshExponential.all_mesh_exponential_inverses
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ shift) replace

theorem original_gamma_shift_inverse (w z R S B a d c e : PTm n)
    (hw : Γ ⊢[PRAAx] source w R B a d)
    (hz : Γ ⊢[PRAAx] source z S B c e)
    (hShift : Γ ⊢[PRAAx] equal (shifted w B) z) :
    Γ ⊢[PRAAx] crossEquivalent gammaF resultF (gammaData w R B d) (resultData w z S B e) := by
  let P := GaussianGammaC7Name.nameF
  let x := GaussianGammaC7Name.data w R B
  let y := GaussianGammaC7Name.data z S B
  let g := gammaData z S B e
  let u := ofGaussian w B
  let v := reciprocal u
  let t := multiplyData constantF P u y
  let r := resultData w z S B e
  have hx := GaussianGammaC7Name.name_regular w R B hw.andE₁
  have hy := GaussianGammaC7Name.name_regular z S B hz.andE₁
  have hg := gamma_regular z S B c e hz
  have hu := constant_regular (Γ := Γ) u
  have hv := constant_regular (Γ := Γ) v
  have ht := multiply_fast constantF P u y hu hy
  have hr := multiply_fast constantF gammaF v g hv hg
  have shift := reciprocal_gamma_shift w z R S B hw.andE₁ hz.andE₁ hShift
  have transport := GaussianGammaAdjacentCutoff.multiply_cross P (multiplyF constantF P)
    resultF resultF x t r r hx ht hr hr shift (cross_refl resultF r hr)
  have factor := constant_inverse u v x (reciprocal_identity u (input_norm_positive w R B a d hw))
  have terminal := cross_trans _ _ _ _ _ _ (gamma_product z S B c e hz) (ones_equivalent y x)
  have cancel := inverse_pairs constantF P constantF gammaF u y v g x hu hy hv hg factor terminal
  have apart := (original_gamma_inverse w R B a d hw).andE₁.andE₂
  exact reciprocal_matches_inverse P resultF (gammaHeight w R B d) x r hx hr apart
    (cross_trans _ _ _ _ _ _ transport cancel)

theorem original_gamma_shift_observations (p q w z R S B a d c e : PTm n)
    (hw : Γ ⊢[PRAAx] source w R B a d)
    (hz : Γ ⊢[PRAAx] source z S B c e)
    (hShift : Γ ⊢[PRAAx] equal (shifted w B) z) :
    Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (ap2 gammaF p (gammaData w R B d))
      (ap2 resultF q (resultData w z S B e))
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) :=
  cross_at _ _ _ _ p q (original_gamma_shift_inverse w z R S B a d c e hw hz hShift)

theorem actual_original_pole_free_Gamma_one_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 0) (var 2) (var 4) (var 5) (var 6) ⋏
      (source (var 1) (var 3) (var 4) (var 7) (var 8) ⋏ equal (shifted (var 0) (var 4)) (var 1))) ⟶
      crossEquivalent gammaF resultF (gammaData (var 0) (var 2) (var 4) (var 6))
        (resultData (var 0) (var 1) (var 3) (var 4) (var 8))) :=
  closeUniv 9 (.impI (original_gamma_shift_inverse _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNativeShiftRecurrence
