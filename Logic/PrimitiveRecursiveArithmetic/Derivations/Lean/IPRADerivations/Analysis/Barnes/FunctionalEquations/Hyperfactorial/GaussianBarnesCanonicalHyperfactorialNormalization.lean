import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorial
import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalNormalization
import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialInverse

/-! # The positive rational analytic hyperfactorial takes value one at one -/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialNormalization

open_ipra
open GaussianBarnesCanonicalHyperfactorial
  (center radius barnesData exponentF exponentData specialLogData powerF powerData powerRadius
    nameF data productF productData barnes_regular power_regular regular cleared_relation)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_at one_fast multiply_one)
open GaussianRationalHorner (ofGaussian qzero zero_represents)
open GaussianRationalSyntheticDivision (qone qzero_canonical qmul_congr qmul_zero_left)
open ComplexLogarithmRemainder (normSq zeroCode oneCode scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem center_zero : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (center (one : PTm n) one) zeroCode :=
  GaussianRootAlgebra.sub_self (scale one oneCode)

theorem zero_multiplier : Γ ⊢[PRAAx] ofGaussian (center (one : PTm n) one) one ≐ qzero := by
  apply GaussianRationalHorner.canonical_unique _ _ zeroCode one
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) qzero_canonical (le_refl _)
    _ (zero_represents one)
  exact GaussianRationalHorner.represents_congr (.eqRefl _) center_zero (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))

theorem exponent_at_one (p : PTm n) : Γ ⊢[PRAAx] ap2 exponentF p (exponentData one one) ≐ qzero := by
  let L := GaussianLogGammaEulerCofinal.nameF
  let d := ofGaussian (center (one : PTm n) one) one
  let x := specialLogData (one : PTm n) one
  let k := GaussianNamedSmallPerturbationTransport.productClock constantF L d x p
  exact (GaussianNamedSmallPerturbationTransport.product_at constantF L d x p).eqTrans
    ((qmul_congr ((constant_at k d).eqTrans zero_multiplier) (.eqRefl _)).eqTrans (qmul_zero_left _))

theorem power_at_one (p : PTm n) : Γ ⊢[PRAAx] ap2 powerF p (powerData one one) ≐ qone := by
  let R := powerRadius (one : PTm n) one
  let x := exponentData (one : PTm n) one
  let k := GaussianRadiusExponentialName.inputPrecision R p
  exact (GaussianRadiusExponentialName.sample_at exponentF R p x).eqTrans
    ((GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (.eqRefl _) (exponent_at_one k)).eqTrans (GaussianGammaCanonicalTailExponential.scalar_zero_point _))

theorem normalization : Γ ⊢[PRAAx] crossEquivalent nameF oneF (data (one : PTm n) one) zero := by
  let G := GaussianBarnesCanonicalValue.nameF
  let x := data (one : PTm n) one
  let y := barnesData (one : PTm n) one
  let P := powerData (one : PTm n) one
  have h := le_refl (Γ := Γ) (one : PTm n)
  have hx := regular one one h h
  have hy := barnes_regular one one h
  have hp := power_regular one one h h
  have z : Γ ⊢[PRAAx] normSq (center (one : PTm n) one) ≐ zero :=
    (GaussianRootAlgebra.normSq_equal center_zero).eqTrans ComplexLogarithmRemainder.normSq_zero
  have gOne := GaussianBarnesCanonicalNormalization.normalization (center one one) (radius one one) one h z
  have constOne : Γ ⊢[PRAAx] crossEquivalent constantF oneF qone x := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (one_fast x)
    refine .allI ?_
    simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalSyntheticDivision.subst_qone] using
      (constant_at (var 0) qone).eqTrans (one_at (var 0) (Syn.shift x)).eqSymm
  have cleared := cleared_relation one one h h
  have collapse := GaussianGammaAdjacentCutoff.multiply_cross nameF nameF G oneF x x y x
    hx hx hy (one_fast x) (cross_refl _ _ hx) (cross_trans _ _ _ _ _ _ gOne constOne)
  have pOne : Γ ⊢[PRAAx] crossEquivalent powerF oneF P zero := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _ hp (one_fast zero)
    refine .allI ?_
    simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,
      GaussianBarnesCanonicalHyperfactorial.subst_powerData,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using (power_at_one (var 0)).eqTrans (one_at (var 0) zero).eqSymm
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_one nameF x hx))
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ collapse) (cross_trans _ _ _ _ _ _ cleared pOne))

theorem actual_original_Barnes_hyperfactorial_at_one_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] crossEquivalent nameF oneF (data one one) zero :=
  normalization

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialNormalization
