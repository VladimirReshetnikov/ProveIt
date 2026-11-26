import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianNamedEvenSinePolynomial
import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianNamedSineSincFactorization
import IPRADerivations.Analysis.Names.Scaling.GaussianNaturalScaleProductName
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaFirstCrossing
import IPRADerivations.Analysis.Names.ImaginaryParts.GaussianNamedImaginaryNaturalScale

/-!
# Cleared named sinc multiple-angle factorization

Compose the original sine–sinc law with the checked odd multiple-angle
polynomial. Before cancellation the exact same scaled argument
multiplies both sinc expressions. An explicit apartness certificate
for the original argument also supplies the scaled certificate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedClearedSincMultipleAngle

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedNaturalScale (clock sample_at exponential_input radius)
open GaussianNameReciprocal (anchor tail_lower)
open GaussianRationalNaturalScale (naturalPoint natScale_as_product natural_point_represents)
open GaussianRationalLowerBounds (lower_from_representation lower_congr product_lower name_lower)
open GaussianNamedSineTaylor (imaginaryF imaginary_input)
open GaussianNamedSineFromExponential (sineF sineData sine_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (multiply_commutative)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianArctangentDivisionAngles (modulus)
open GaussianNamedEvenSinePolynomial (sineDisk polynomialF polynomialData rootProductF
  original_sine_bounds polynomial_regular scaledPolynomialF scaledPolynomialData
  scaled_polynomial_regular root_product_cross odd_multiple_cross)
open GaussianRadiusExponentialName (input)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul)
open ComplexLogarithmRemainder (normSq normSq_scale scale oneCode normSq_one)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "scaledF" => GaussianNamedNaturalScale.nameF
local notation "stageData" => GaussianNamedNaturalScale.data
local notation "sincF" => GaussianNamedSinc.nameF
local notation "sincData" => GaussianNamedSinc.data

def rootFactorF (f : PR 2) : PR 2 := rootProductF (imaginaryF f)
def rootFactorData (f : PR 2) (J R x z : PTm n) : PTm n := polynomialData (imaginaryF f) J R x z
def factoredF (f : PR 2) : PR 2 := multiplyF (sincF f) (rootFactorF f)
def factoredData (f : PR 2) (J R x z : PTm n) : PTm n :=
  multiplyData (sincF f) (rootFactorF f) (sincData f R x) (rootFactorData f J R x z)
def scaledSincData (f : PR 2) (E J R x : PTm n) : PTm n :=
  sincData (scaledF f) (radius E R) (stageData E (modulus J) x)

theorem root_factor_regular (f : PR 2) (J R x z : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] pointCN (rootFactorF f) (rootFactorData f J R x z) := by
  let I := imaginaryF f
  have hI := imaginary_input f R x hf
  exact GaussianSineNormalizedSampleName.product_regular (sineF I) J (sineDisk I R x) (sineData I R x) z
    (sine_regular I R x hI) (original_sine_bounds I R x hI)

theorem cleared (f : PR 2) (E J R x z : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hc : Γ ⊢[PRAAx] le (modulus J) E) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (sincF (scaledF f)) (scaledF f)) (multiplyF (factoredF f) (scaledF f))
      (multiplyData (sincF (scaledF f)) (scaledF f) (scaledSincData f E J R x) (stageData E (modulus J) x))
      (multiplyData (factoredF f) (scaledF f) (factoredData f J R x z) (stageData E (modulus J) x)) := by
  let m := modulus J
  let M := naturalPoint m
  let I := imaginaryF f
  let W := scaledF f
  let T := sincF f
  let C := constantF
  let Q := rootFactorF f
  let A := stageData E m x
  let V := scaledSincData f E J R x
  let t := sincData f R x
  let q := rootFactorData f J R x z
  let D := factoredData f J R x z
  have hw := exponential_input f E m R x hf hc
  have hs := GaussianNamedSinc.name_regular W (radius E R) A hw
  have ht := GaussianNamedSinc.name_regular f R x hf
  have hq := root_factor_regular f J R x z hf
  have hI := imaginary_input f R x hf
  have hM := constant_regular (Γ := Γ) M
  have sinRegular := sine_regular I R x hI
  have hp := polynomial_regular I J R x z hI
  have scaledP := scaled_polynomial_regular I J R x z hI
  have onRight := multiply_cross C C (polynomialF I) Q M M (polynomialData I J R x z) q hM hM hp hq
    (cross_refl _ _ hM) (cross_symm _ _ _ _ (root_product_cross I J R x z hI))
  have onLeft := GaussianNamedSineSincFactorization.original_sine_factors f R x hf
  have leftReg := multiply_fast f T x t hf.andE₁ ht
  have rightReg := multiply_fast C Q M q hM hq
  have replaced := multiply_cross (sineF I) (multiplyF f T) (scaledPolynomialF I) (multiplyF C Q)
    (sineData I R x) (multiplyData f T x t) (scaledPolynomialData I J R x z) (multiplyData C Q M q)
    sinRegular leftReg scaledP rightReg onLeft onRight
  have exchange := GaussianGammaReciprocalInverse.named_product_exchange f T C Q x t M q hf.andE₁ ht hM hq
  have scaled := GaussianNaturalScaleProductName.scale_product_cross f E m R x hf hc
  have coeff := cross_trans _ _ _ _ _ _ (multiply_commutative f C x M hf.andE₁ hM)
    (cross_symm _ _ _ _ scaled)
  have hd := multiply_fast T Q t q ht hq
  have joined := multiply_cross (multiplyF f C) W (factoredF f) (factoredF f)
    (multiplyData f C x M) A D D (multiply_fast f C x M hf.andE₁ hM) hw.andE₁ hd hd coeff (cross_refl _ _ hd)
  have scaleSine := GaussianNamedSineSincFactorization.original_sine_factors W (radius E R) A hw
  have lo := cross_symm _ _ _ _ (multiply_commutative W (sincF W) A V hw.andE₁ hs)
  have rotated := GaussianNamedImaginaryNaturalScale.sine_cross f E m R x hf hc
  exact cross_trans _ _ _ _ _ _ lo
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ scaleSine)
      (cross_trans _ _ _ _ _ _ rotated
        (cross_trans _ _ _ _ _ _ (odd_multiple_cross I E J R x z hI hc)
          (cross_trans _ _ _ _ _ _ replaced
            (cross_trans _ _ _ _ _ _ exchange
              (cross_trans _ _ _ _ _ _ joined (multiply_commutative W (factoredF f) A D hw.andE₁ hd)))))))

theorem natural_point_lower (m : PTm n) : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower (naturalPoint m) m one := by
  apply lower_from_representation _ _ _ _ _ (le_refl one) (le_refl one) (natural_point_represents m)
  have norm : Γ ⊢[PRAAx] normSq (scale m oneCode) ≐ m*m := (normSq_scale m oneCode).eqTrans
    ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))
  exact le_congr (by ipra_ring) (((congrMul (.eqRefl _) norm).eqTrans (by ipra_ring)).eqSymm)
    (le_refl (m*m))

theorem scaled_apart (f : PR 2) (E m h x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (ha : Γ ⊢[PRAAx] GaussianNameReciprocal.apart f h x) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.apart (scaledF f) (succ h) (stageData E m x) := by
  let p := anchor (succ h)
  let k := clock p E
  let U := unit (succ h)
  let s := monus k (anchor h)
  let q := ap2 f k x
  have hp : Γ ⊢[PRAAx] le (anchor h) p := by
    apply le_of_eq_add (d := one)
    dsimp only [p, anchor]
    exact (congrAdd (succ_eq_add_one h) (.eqRefl _)).eqTrans (by ipra_ring)
  have hk := le_trans hp (GaussianNamedNaturalScale.clock_later p E)
  have e : Γ ⊢[PRAAx] k ≐ s+anchor h :=
    (eq_add_of_le hk).eqTrans (add_comm _ _)
  have t : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower q one U :=
    GaussianNameReciprocal.lower_congr (congrAp2 f e.eqSymm (.eqRefl _)) (.eqRefl _) (tail_lower f h x s hf ha)
  have hU : Γ ⊢[PRAAx] le one U := unit_positive _
  have eq : Γ ⊢[PRAAx] ap2 (scaledF f) p (stageData E m x) ≐ qmul (naturalPoint m) q :=
    (sample_at f p E m x).eqTrans (natScale_as_product m q)
  have prod := product_lower _ _ _ _ _ _ (le_refl one) hU (natural_point_lower (Γ := Γ) m) t
  exact name_lower _ _ _ hm hU (lower_congr eq.eqSymm (by ipra_ring) (one_mul U) prod)

theorem from_apart (f : PR 2) (E J R x z h : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hc : Γ ⊢[PRAAx] le (modulus J) E)
    (ha : Γ ⊢[PRAAx] GaussianNameReciprocal.apart f h x) :
    Γ ⊢[PRAAx] crossEquivalent (sincF (scaledF f)) (factoredF f)
      (scaledSincData f E J R x) (factoredData f J R x z) := by
  let m := modulus J
  let A := stageData E m x
  have hw := exponential_input f E m R x hf hc
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  exact GaussianNamedGammaFirstCrossing.cancel_right _ _ (scaledF f) _ _ A (succ h)
    (GaussianNamedSinc.name_regular _ _ _ hw)
    (multiply_fast _ _ _ _ (GaussianNamedSinc.name_regular f R x hf) (root_factor_regular f J R x z hf))
    hw.andE₁ (scaled_apart f E m h x hf.andE₁ ha hm) (cleared f E J R x z hf hc)

theorem actual_named_sinc_multiple_angle_from_apart_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input f (var 2) (var 3) ⟶ le (modulus (var 1)) (var 0) ⟶
      GaussianNameReciprocal.apart f (var 5) (var 3) ⟶
      crossEquivalent (sincF (scaledF f)) (factoredF f) (scaledSincData f (var 0) (var 1) (var 2) (var 3))
        (factoredData f (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI
    (from_apart f _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedClearedSincMultipleAngle
