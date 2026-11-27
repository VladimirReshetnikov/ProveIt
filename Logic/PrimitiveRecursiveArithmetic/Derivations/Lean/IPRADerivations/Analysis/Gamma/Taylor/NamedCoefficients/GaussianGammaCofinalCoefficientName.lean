import IPRADerivations.Analysis.Gamma.Taylor.FinitePolynomials.GaussianGammaFiniteCoefficientPolynomial
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.HorizonCoherence.GaussianGammaSynchronousExponentCompatibility
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianBoundedConstantProductName
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaC7Name

/-!
# Actual cofinal polynomial observations of the original C7 name

Every observation is exactly an evaluation of the actual original finite
coefficient polynomial. Its coefficient precision and both Taylor cutoffs
are computed solely from the numerical disk radius and requested precision,
and all three are cofinal. The actual name is regular and cross-equivalent
to the unchanged original C7 name. Fixed-degree limiting coefficient names
and full infinite coefficient consistency remain separate obligations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCofinalCoefficientName

open_ipra
open GaussianRationalHorner (qmul evaluate ofGaussian)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianGammaCanonicalExponent (source)
open GaussianGammaCanonicalExponentBound (numericalRadius)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_to_diagonal diagonal_refl)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaC9Bound (majorant)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def headMass (R : PTm n) : PTm n := R*pw (one+R) (two*R)
def exponentialF : PR 2 := GaussianRadiusExponentialName.nameF GaussianGammaSynchronousExponentName.nameF
def exponentialData (z R B : PTm n) : PTm n := GaussianRadiusExponentialName.data (numericalRadius R)
  (GaussianGammaSynchronousExponentName.data z R B)
def nameF : PR 2 := GaussianBoundedConstantProductName.nameF exponentialF
def data (z R B : PTm n) : PTm n := GaussianBoundedConstantProductName.data (headMass R)
  (GaussianGammaC7Name.head z R B) (exponentialData z R B)
def sample (p z R B : PTm n) : PTm n := ap2 nameF p (data z R B)
def outerClock (p R : PTm n) : PTm n := GaussianBoundedConstantProductName.clock p (headMass R)
def inputClock (p R : PTm n) : PTm n := GaussianRadiusExponentialName.inputPrecision (numericalRadius R) (outerClock p R)
def exponentClock (p R : PTm n) : PTm n := GaussianGammaSynchronousExponentName.clock (inputClock p R) R
def coefficientPrecision (p R : PTm n) : PTm n := GaussianGammaSynchronousExponentName.gammaClock (exponentClock p R) R
def degreeCutoff (p R : PTm n) : PTm n := GaussianGammaZetaTailSeries.cutoff (exponentClock p R) R
def exponentialCutoff (p R : PTm n) : PTm n := GaussianRadiusExponentialName.index (numericalRadius R) (outerClock p R)
ipra_subst headMass
ipra_subst exponentialData
ipra_subst data

theorem exponential_input (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input GaussianGammaSynchronousExponentName.nameF (numericalRadius R)
      (GaussianGammaSynchronousExponentName.data z R B) := by
  refine .andI (GaussianGammaSynchronousExponentName.name_regular z R B h) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,
    GaussianGammaSynchronousExponentName.subst_data,GaussianGammaCanonicalExponentBound.subst_numericalRadius,
    GaussianGammaSynchronousExponentName.sample] using
      GaussianGammaSynchronousExponentName.sample_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) hs

theorem exponential_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN exponentialF (exponentialData z R B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input z R B h)

theorem original_exponential_identity (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent exponentialF GaussianGammaCanonicalExponent.exponentialF (exponentialData z R B)
      (GaussianGammaCanonicalExponent.exponentialData z R B) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (exponential_input z R B h) (GaussianGammaCanonicalExponent.exponential_input z R B h)
    (GaussianGammaSynchronousExponentCompatibility.original_exponent_identity z R B h)

theorem product_input (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianBoundedConstantProductName.input exponentialF (headMass R) (GaussianGammaC7Name.head z R B) (exponentialData z R B) :=
  .andI (exponential_regular z R B h) (GaussianGammaC7Name.head_bound z R B h)
theorem name_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN nameF (data z R B) :=
  GaussianBoundedConstantProductName.name_regular _ _ _ _ (product_input z R B h)

theorem original_C7_identity (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianGammaC7Name.nameF (data z R B) (GaussianGammaC7Name.data z R B) := by
  have first := GaussianBoundedConstantProductName.ordinary_product_identity _ _ _ _ (product_input z R B h)
  have second := GaussianNameArithmetic.multiply_equivalent
    GaussianBoundedConstantProductName.constantF GaussianGammaCanonicalExponent.constantF exponentialF GaussianGammaCanonicalExponent.exponentialF
    (GaussianGammaC7Name.head z R B) (GaussianGammaC7Name.head z R B)
    (exponentialData z R B) (GaussianGammaCanonicalExponent.exponentialData z R B)
    (GaussianBoundedConstantProductName.constant_regular _) (GaussianGammaCanonicalExponent.constant_regular _)
    (exponential_regular z R B h) (GaussianGammaCanonicalExponent.exponential_regular z R B h)
    (diagonal_refl _ _) (cross_to_diagonal _ _ _ _ (original_exponential_identity z R B h))
  exact cross_trans _ _ _ _ _ _ first second

/-- Both sides use the actual stored exponential coefficients, with the
same computed shared precision and both computed numerical cutoffs. -/
theorem exponential_sample_polynomial (p z R B : PTm n) : Γ ⊢[PRAAx]
    ap2 exponentialF (outerClock p R) (exponentialData z R B) ≐
      evaluate (GaussianGammaExponentCoefficientPolynomial.exponential (coefficientPrecision p R) R (degreeCutoff p R) (exponentialCutoff p R))
        (ofGaussian z B) := by
  have left := (GaussianRadiusExponentialName.sample_at (Γ := Γ) GaussianGammaSynchronousExponentName.nameF
    (numericalRadius R) (outerClock p R) (GaussianGammaSynchronousExponentName.data z R B)).eqTrans
      (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _)
        (GaussianGammaSynchronousExponentName.sample_at (inputClock p R) z R B))
  have right := (GaussianRationalPolynomialExponential.polynomial_evaluation (Γ := Γ) _ _ (exponentialCutoff p R) _
    (GaussianGammaExponentCoefficientPolynomial.polynomial_length (coefficientPrecision p R) (two*R) (degreeCutoff p R))).eqTrans
      (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl (succ (exponentialCutoff p R)))
        (GaussianGammaSynchronousExponentName.raw_polynomial_binding (exponentClock p R) z R B))
  exact left.eqTrans right.eqSymm

theorem actual_polynomial_observation (p z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    evaluate (GaussianGammaFiniteCoefficientPolynomial.polynomial (coefficientPrecision p R) R (degreeCutoff p R) (exponentialCutoff p R))
      (ofGaussian z B) ≐ sample p z R B := by
  have actual := (GaussianBoundedConstantProductName.sample_at (Γ := Γ) exponentialF p (headMass R)
    (GaussianGammaC7Name.head z R B) (exponentialData z R B)).eqTrans
      (qmul_congr (GaussianGammaEulerHead.program_at z B (two*R)) (exponential_sample_polynomial p z R B))
  have polynomial := (GaussianRationalPolynomialProduct.product_evaluation (Γ := Γ) _ _ _ _ _
    (GaussianGammaEulerHeadPolynomial.polynomial_length (two*R))
    (GaussianGammaFiniteCoefficientPolynomial.exponential_length (coefficientPrecision p R) R (degreeCutoff p R) (exponentialCutoff p R))).eqTrans
      (qmul_congr (GaussianGammaEulerHeadPolynomial.original_head_evaluation z B (two*R) hB) (.eqRefl _))
  exact polynomial.eqTrans actual.eqSymm

theorem exponential_sample_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    bounded (ap2 exponentialF p (exponentialData z R B)) (pw (num 3) (numericalRadius R)) one :=
  bound_congr (GaussianRadiusExponentialName.sample_at _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _
      (GaussianRadiusExponentialName.query_bound _ _ _ p (exponential_input z R B h)))

theorem sample_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    bounded (sample p z R B) (majorant R) one :=
  bound_congr (GaussianBoundedConstantProductName.sample_at _ _ _ _ _).eqSymm (.eqRefl _)
    (show Γ ⊢[PRAAx] one*one ≐ one by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one)
      (GaussianGammaC7Name.head_bound z R B h) (exponential_sample_bound (outerClock p R) z R B h))

theorem outer_clock_later (p R : PTm n) : Γ ⊢[PRAAx] le p (outerClock p R) :=
  le_add_right p (GaussianFastValueCut.normalizer (headMass R))
theorem exponent_clock_later (p R : PTm n) : Γ ⊢[PRAAx] le p (exponentClock p R) :=
  le_trans (outer_clock_later p R)
    (le_trans (le_of_eq_add (d := num 4+(numericalRadius R+two)*exponentialCutoff p R)
      (by unfold inputClock GaussianRadiusExponentialName.inputPrecision exponentialCutoff; ipra_ring))
      (le_add_right (inputClock p R) (GaussianFastValueCut.normalizer (R+one))))
theorem coefficient_precision_cofinal (p R : PTm n) : Γ ⊢[PRAAx] le p (coefficientPrecision p R) :=
  le_trans (exponent_clock_later p R) (GaussianGammaSynchronousExponentName.gamma_clock_later _ _)
theorem degree_cutoff_cofinal (p R : PTm n) : Γ ⊢[PRAAx] le p (degreeCutoff p R) :=
  le_trans (exponent_clock_later p R) (GaussianGammaZetaTailSeries.cutoff_cofinal _ _)
theorem exponential_cutoff_cofinal (p R : PTm n) : Γ ⊢[PRAAx] le p (exponentialCutoff p R) := by
  have e := (GaussianRadiusExponentialName.index_congr (Γ := Γ) (numericalRadius R) (zero_add (outerClock p R)).eqSymm).eqTrans
    (GaussianRadiusExponentialName.index_add (numericalRadius R) zero (outerClock p R))
  exact le_trans (outer_clock_later p R) (le_congr (.eqRefl _) e.eqSymm (le_add_left _ _))

theorem actual_cofinal_Gamma_polynomial_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular _ _ _ Prf.hyp0))
theorem actual_cofinal_polynomials_are_original_C7_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent nameF GaussianGammaC7Name.nameF
      (data (var 0) (var 1) (var 2)) (GaussianGammaC7Name.data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_C7_identity _ _ _ Prf.hyp0))
theorem actual_cofinal_Gamma_polynomial_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ evaluate
      (GaussianGammaFiniteCoefficientPolynomial.polynomial (coefficientPrecision (var 0) (var 2)) (var 2)
        (degreeCutoff (var 0) (var 2)) (exponentialCutoff (var 0) (var 2))) (ofGaussian (var 1) (var 3)) ≐
          sample (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (actual_polynomial_observation _ _ _ _ Prf.hyp0))
theorem actual_Gamma_polynomial_cutoffs_cofinal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 0) (coefficientPrecision (var 0) (var 1)) ⋏
      (le (var 0) (degreeCutoff (var 0) (var 1)) ⋏ le (var 0) (exponentialCutoff (var 0) (var 1)))) :=
  closeUniv 2 (.andI (coefficient_precision_cofinal _ _) (.andI (degree_cutoff_cofinal _ _) (exponential_cutoff_cofinal _ _)))

end LeanProofs.IPRA.Analysis.GaussianGammaCofinalCoefficientName
