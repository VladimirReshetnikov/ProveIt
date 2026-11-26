import IPRADerivations.Analysis.Trigonometry.GaussianSineProductScaledArgumentCancellation
import IPRADerivations.Analysis.Trigonometry.GaussianNamedEvenSinePolynomial

/-!
# The zero branch of the encoded odd sine product

An encoded zero numerator gives exact zero samples for the original
argument and for its scaled and rotated names. The two sinc names and
the normalized polynomial product are each equivalent to one.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductScaledZero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq)
open GaussianArctangentDivisionAngles (modulus)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameConjugation (pointwiseEqual equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans diagonal_at cross_to_diagonal)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianNamedEvenSinePolynomial (rootProductF polynomialData original_sine_bounds)
open GaussianNamedSincQuadraticBounds (observationBound zero_is_one)
open GaussianNamedSineFromExponential (sineF sineData sine_regular sine_zero_of_exponential_one)
open GaussianNamedSineTaylor (imaginaryF imaginary_at imaginary_input)
open GaussianRadiusExponentialName (input)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qmul qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalNaturalScale (natScale_as_product natScale_congr)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right qone_canonical)
open GaussianSineNormalizedSampleReconstruction (normalizedValue inverse_odd_unit)
open GaussianSinePolynomialVariation (variationBudget normalized_value_distance)
open GaussianSineProductScaledArgumentCancellation (zero_at)
open GaussianSineProductScaledArguments (nameF data)
open GaussianSineSquaredTrace (fromSine)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zeroSamples (f : PR 2) (x : PTm n) : Fm PTm n :=
  .all (ap2 f (var 0) (Syn.shift x) ≐ qzero)

@[simp] theorem subst_zeroSamples {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x : PTm n) :
    (zeroSamples f x).subst σ = zeroSamples f (Syn.subst σ x) := by
  simp [zeroSamples,Syn.subst_shift,Syn.shift_subst]

theorem zero_sample_at (f : PR 2) (x p : PTm n) (h : Γ ⊢[PRAAx] zeroSamples f x) :
    Γ ⊢[PRAAx] ap2 f p x ≐ qzero := by simpa [zeroSamples] using h.allE p

theorem zero_observation_bound (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] zeroSamples f x) :
    Γ ⊢[PRAAx] observationBound f x zero one := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] zeroSamples f (Syn.shift x) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [observationBound,Syn.shift,one] using GaussianRationalReciprocal.bound_congr
    (zero_sample_at f (Syn.shift x) (var 0) hs).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero one (le_refl one))

theorem scaled_zero_samples (z R B m x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] zeroSamples nameF (data z R B m x) := by
  refine .allI ?_
  have hB' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,one] using hB.shift
  have hm' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift,one] using hm.shift
  have hz' : Γ.map Fm.shift ⊢[PRAAx] normSq (Syn.shift z) ≐ zero := by simpa [Fm.shift,Syn.shift] using hz.shift
  simpa [zeroSamples,Syn.shift] using zero_at (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift m) (Syn.shift x)
    (var 0) hB' hm' hz'

theorem natural_multiple_zero_samples (f : PR 2) (E m x : PTm n) (h : Γ ⊢[PRAAx] zeroSamples f x) :
    Γ ⊢[PRAAx] zeroSamples (GaussianNamedNaturalScale.nameF f) (GaussianNamedNaturalScale.data E m x) := by
  refine .allI ?_
  let y := Syn.shift x
  let N := Syn.shift E
  let M := Syn.shift m
  let p : PTm (n+1) := var 0
  have hs : Γ.map Fm.shift ⊢[PRAAx] zeroSamples f y := by simpa [y,Fm.shift,Syn.shift] using h.shift
  have e := zero_sample_at f y (GaussianNamedNaturalScale.clock p N) hs
  have q := (GaussianNamedNaturalScale.sample_at f p N M y).eqTrans
    ((natScale_congr (.eqRefl _) e).eqTrans ((natScale_as_product _ _).eqTrans (qmul_zero_right _)))
  simpa [zeroSamples,GaussianNamedNaturalScale.sample,Syn.shift,y,N,M,p] using q

theorem imaginary_zero_samples (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] zeroSamples f x) :
    Γ ⊢[PRAAx] zeroSamples (imaginaryF f) x := by
  refine .allI ?_
  let y := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] zeroSamples f y := by simpa [y,Fm.shift,Syn.shift] using h.shift
  exact (imaginary_at f (var 0) y).eqTrans
    ((qmul_congr (.eqRefl _) (zero_sample_at f y (var 0) hs)).eqTrans (qmul_zero_right _))

private theorem exponential_one (f : PR 2) (R x : PTm n) (hi : Γ ⊢[PRAAx] input f R x) (hz : Γ ⊢[PRAAx] zeroSamples f x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianRadiusExponentialName.nameF f) constantF (GaussianRadiusExponentialName.data R x) qone := by
  apply equal_samples_cross _ _ _ _ (GaussianRadiusExponentialName.name_regular f R x hi) (constant_regular qone)
  refine .allI ?_
  let r := Syn.shift R
  let y := Syn.shift x
  let p : PTm (n+1) := var 0
  have hz' : Γ.map Fm.shift ⊢[PRAAx] zeroSamples f y := by simpa [y,Fm.shift,Syn.shift] using hz.shift
  have atInput := zero_sample_at f y (GaussianRadiusExponentialName.inputPrecision r p) hz'
  have e := (GaussianRadiusExponentialName.sample_at f r p y).eqTrans
    ((GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _) atInput).eqTrans
      (GaussianGammaCanonicalTailExponential.scalar_zero_point _))
  simpa [pointwiseEqual,GaussianRadiusExponentialName.sample,Syn.shift,r,y,p] using e.eqTrans (constant_at p qone).eqSymm

theorem sine_zero (f : PR 2) (R x : PTm n) (hi : Γ ⊢[PRAAx] input f R x) (hz : Γ ⊢[PRAAx] zeroSamples f x) :
    Γ ⊢[PRAAx] crossEquivalent (sineF f) constantF (sineData f R x) qzero :=
  sine_zero_of_exponential_one f R x hi (exponential_one f R x hi hz)

theorem normalized_value_at_zero (J : PTm n) : Γ ⊢[PRAAx] normalizedValue J (fromSine qzero) ≐ qone :=
  (qmul_congr (.eqRefl _) ((GaussianRationalMonicReduction.evaluate_congr (.eqRefl _)
    GaussianSineRootNormalization.trace_at_zero).eqTrans (GaussianSineSquaredNormalization.normalization J))).eqTrans
      (inverse_odd_unit J)

theorem normalized_product_zero (f : PR 2) (J B x z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hb : Γ ⊢[PRAAx] GaussianSineNormalizedSampleName.bound f B x)
    (hz : Γ ⊢[PRAAx] crossEquivalent f constantF x qzero) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianSineNormalizedSampleName.nameF f) constantF (GaussianSineNormalizedSampleName.data J B x z) qone := by
  let F := GaussianSineNormalizedSampleName.polynomialF f
  let d := GaussianSineNormalizedSampleName.data J B x z
  have poly : Γ ⊢[PRAAx] crossEquivalent F constantF d qone := by
    apply cross_of_diagonal_rate _ _ _ _ (variationBudget J B*two)
      (GaussianSineNormalizedSampleName.polynomial_regular f J B x z hf hb) (constant_regular _)
    refine .allI ?_
    let N := Syn.shift J
    let A := Syn.shift B
    let X := Syn.shift x
    let Z := Syn.shift z
    let p : PTm (n+1) := var 0
    let t := GaussianSineNormalizedSampleName.precision N A p
    have hb' : Γ.map Fm.shift ⊢[PRAAx] GaussianSineNormalizedSampleName.bound f A X :=
      by simpa [A,X,Fm.shift,Syn.shift] using hb.shift
    have hz' : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent f constantF X qzero :=
      by simpa [X,Fm.shift,Syn.shift] using hz.shift
    have small := distance_congr (.eqRefl _) (constant_at t qzero) (.eqRefl _) (.eqRefl _)
      (diagonal_at _ _ _ _ t (cross_to_diagonal _ _ _ _ hz'))
    have comparison := normalized_value_distance N (ap2 f t X) qzero A two (unit t)
      (GaussianCoefficientNameBounds.unit_positive t) (GaussianRootApproximationWitness.point_at f A X t hb')
      (GaussianMonicResidualRadius.zero_bounded A one (le_refl one)) small
    have near := GaussianExponentialReference.dyadic_weaken _ _ _ p t (le_add_right _ _) comparison
    simpa [diagonalRate,d,F,Syn.shift,N,A,X,Z,p] using distance_congr
      (GaussianSineNormalizedSampleName.polynomial_at f p N A X Z).eqSymm
      ((normalized_value_at_zero N).eqTrans (constant_at p qone).eqSymm) (.eqRefl _) (.eqRefl _) near
  exact cross_trans _ _ _ _ _ _ (GaussianSineNormalizedSampleName.polynomial_cross f J B x z hf hb) poly

theorem zero_identity (f : PR 2) (W J E a x : PTm n) (hf : Γ ⊢[PRAAx] input f W a)
    (hE : Γ ⊢[PRAAx] le (modulus J) E) (zf : Γ ⊢[PRAAx] zeroSamples f a) :
    let m := modulus J
    let V := GaussianNamedNaturalScale.radius E W
    let g := GaussianNamedNaturalScale.nameF f
    let b := GaussianNamedNaturalScale.data E m a
    let r := rootProductF (imaginaryF f)
    let d := polynomialData (imaginaryF f) J W a x
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedSinc.nameF g) (multiplyF (GaussianNamedSinc.nameF f) r)
      (GaussianNamedSinc.data g V b) (multiplyData (GaussianNamedSinc.nameF f) r (GaussianNamedSinc.data f W a) d) := by
  dsimp only
  let m := modulus J
  let g := GaussianNamedNaturalScale.nameF f
  let b := GaussianNamedNaturalScale.data E m a
  let V := GaussianNamedNaturalScale.radius E W
  let S := GaussianNamedSinc.nameF f
  let s := GaussianNamedSinc.data f W a
  let F := imaginaryF f
  let r := rootProductF F
  let d := polynomialData F J W a x
  have hg : Γ ⊢[PRAAx] input g V b := GaussianNamedNaturalScale.exponential_input f E m W a hf hE
  have zg := natural_multiple_zero_samples f E m a zf
  have sinc_f := zero_is_one f W a hf (zero_observation_bound f a zf)
  have sinc_g := zero_is_one g V b hg (zero_observation_bound g b zg)
  have hF : Γ ⊢[PRAAx] input F W a := imaginary_input f W a hf
  have zeroSine := sine_zero F W a hF (imaginary_zero_samples f a zf)
  have sn := sine_regular F W a hF
  have sb := original_sine_bounds F W a hF
  have prod_one : Γ ⊢[PRAAx] crossEquivalent r constantF d qone :=
    normalized_product_zero _ _ _ _ _ sn sb zeroSine
  have prod_regular : Γ ⊢[PRAAx] pointCN r d :=
    GaussianSineNormalizedSampleName.product_regular _ _ _ _ _ sn sb
  have both := GaussianGammaAdjacentCutoff.multiply_cross S constantF r constantF s qone d qone
    (GaussianNamedSinc.name_regular f W a hf) (constant_regular _) prod_regular (constant_regular _) sinc_f prod_one
  have one_product : Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF constantF) constantF
      (multiplyData constantF constantF qone qone) qone :=
    cross_trans _ _ _ _ _ _ (constant_product_cross qone qone)
      (constant_data_cross _ _ (GaussianReciprocalHorner.qmul_one_right _ qone_canonical))
  exact cross_trans _ _ _ _ _ _ sinc_g (cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ both one_product))

end LeanProofs.IPRA.Analysis.GaussianSineProductScaledZero
