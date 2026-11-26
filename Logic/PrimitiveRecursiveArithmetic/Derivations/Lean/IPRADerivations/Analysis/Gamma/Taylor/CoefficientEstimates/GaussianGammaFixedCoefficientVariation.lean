import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputPrecisionNorm
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputStaticNorm
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianPolynomialExponentialCoefficientVariation
import IPRADerivations.Analysis.FiniteOperations.FiniteSums.GaussianFiniteSumL1Variation
import IPRADerivations.Analysis.Gamma.Taylor.CoefficientEstimates.GaussianGammaFiniteCoefficientStability

/-!
# Precision variation of the original fixed finite Gamma coefficient

Original input sample errors propagate through the actual factorial
exponential and actual Euler-head Cauchy sum. All numerical envelopes
are computed from the original finite programs; in particular the
factorial variation budget is retained before its integral clock cap.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFixedCoefficientVariation

open_ipra
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalL1 (qL1)
open GaussianCoefficientL1 (coefficientNorm qL1_congr)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open GaussianRationalSyntheticDivision (qone qsub_congr canonicalCoefficients)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaInputPrecisionNorm (radiusNumerator radiusDenominator denominator_positive)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianGammaFiniteCoefficientStability (fixedCoefficient)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalArgmin (rationalLE)
open RationalArithmetic (multiply)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (q R e : PTm n) : PTm n := GaussianGammaExponentCoefficientPolynomial.polynomial q (two*R) e
def exponential (q R e : PTm n) : PTm n := GaussianRationalPolynomialExponential.polynomial (input q R e) (degree e) e
def inputEnvelope (R : PTm n) : PTm n := two*R+two
def factorialBudget (R e : PTm n) : PTm n := GaussianPolynomialExponentialCoefficientVariation.variationBudget (inputEnvelope R) e
def integralBudget (R e : PTm n) : PTm n := (numeratorOf (factorialBudget R e)).pos
def headBudget (R : PTm n) : PTm n := pw two (two*R)
def exponentialFactor (R e : PTm n) : PTm n := integralBudget R e*(two*succ (degree e))
def rowFactor (R e : PTm n) : PTm n := headBudget R*exponentialFactor R e
def modulus (R e : PTm n) : PTm n := succ e*rowFactor R e
ipra_subst input
ipra_subst exponential
ipra_subst inputEnvelope
ipra_subst factorialBudget
ipra_subst integralBudget [numeratorOf]
ipra_subst headBudget
ipra_subst exponentialFactor
ipra_subst rowFactor
ipra_subst modulus

theorem rational_integral_upper (a : PTm n) : Γ ⊢[PRAAx] rationalLE a (natCode (numeratorOf a).pos) := by
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _ (RationalRepresentations.represents_self a)
    (natCode_represents _) (RationalArgmin.denominator_positive a) (le_refl one)
  apply zle_of_toZ ((numeratorOf a).pos*LeanProofs.IPRA.PTm.monus (denominatorOf a) one+(numeratorOf a).neg)
  have den := natEq (eq_add_of_le (Γ := Γ) (RationalArgmin.denominator_positive a))
  change ZT.toZ Γ (numeratorOf a*ZT.ofNat one)+
    Groth.ι (IPRA.Q.mk Γ ((numeratorOf a).pos*LeanProofs.IPRA.PTm.monus (denominatorOf a) one+(numeratorOf a).neg)) =
      ZT.toZ Γ (ZT.ofNat (numeratorOf a).pos*ZT.ofNat (denominatorOf a))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  ipra_simps
  rw [den]
  ring

theorem exponential_error_norm (p q R e f : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hf : Γ ⊢[PRAAx] le f e) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (exponentCoefficient (exponential p R e) (e*degree e) f)
      (exponentCoefficient (exponential q R e) (e*degree e) f)))
      (fraction (exponentialFactor R e*radiusNumerator p q) (radiusDenominator p q)) := by
  let E := fraction (two*succ (degree e)*radiusNumerator p q) (radiusDenominator p q)
  have actual := GaussianPolynomialExponentialCoefficientVariation.original_coefficient_variation (Γ := Γ)
    (input p R e) (input q R e) (degree e) e (inputEnvelope R) E f
    (GaussianGammaExponentCoefficientPolynomial.polynomial_length _ _ _) (GaussianGammaExponentCoefficientPolynomial.polynomial_length _ _ _)
    (GaussianGammaInputStaticNorm.original_input_norm p R e hR) (GaussianGammaInputStaticNorm.original_input_norm q R e hR)
    (GaussianGammaInputPrecisionNorm.input_precision_norm p q (two*R) e)
    (le_trans hf (le_of_eq_add (d := two) (by unfold degree; ipra_ring)))
  have positive := GaussianRationalL1.nonnegative_of_representation (Γ := Γ) E _ _ (denominator_positive p q)
    (fraction_represents _ _ (denominator_positive p q))
  have cap := RationalArithmetic.multiply_monotone E _ _ positive (rational_integral_upper (Γ := Γ) (factorialBudget R e))
  have capped := RationalArgmin.transitive actual (RationalArgmin.rationalLE_congr
    (RationalAlgebra.multiply_commutative _ _) (RationalAlgebra.multiply_commutative _ _) cap)
  have code : Γ ⊢[PRAAx] multiply (natCode (integralBudget R e)) E ≐
      fraction (exponentialFactor R e*radiusNumerator p q) (radiusDenominator p q) :=
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) (denominator_positive p q)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by unfold exponentialFactor; ipra_ring) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) code capped

theorem head_canonical (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    canonicalCoefficients (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) := by
  have form := RationalIntegerNormalization.positive_form (Γ := Γ)
    (GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R hR)
  have code := (congrAp2 GaussianGammaEulerHeadPolynomial.headF form (.eqRefl zero)).eqTrans
    (GaussianGammaEulerHeadPolynomial.polynomial_succ _)
  exact GaussianRationalMonicReduction.canonical_coefficients_congr code (GaussianRationalPolynomialProduct.product_canonical _ _ _ _)

theorem head_norm (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (GaussianGammaEulerHeadPolynomial.polynomial (two*R))) (natCode (headBudget R)) := by
  have unit := GaussianGammaInputStaticNorm.unit_weighted_norm (Γ := Γ) _ _
    (GaussianGammaEulerHeadPolynomial.polynomial_length (two*R)) (head_canonical R hR)
  have code : Γ ⊢[PRAAx] one*pw (one+one) (two*R) ≐ headBudget R :=
    (one_mul _).eqTrans (congrAp2 powF (.eqRefl (two*R)) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr unit (GaussianPositiveExponentialMajorant.natCode_congr code)
    (GaussianGammaEulerHeadPolynomial.original_head_coefficient_mass one (two*R))

/-- The row estimate uses only the degree and norm of the common head. -/
theorem row_error_of_head (P D p q R e i : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hLength : Γ ⊢[PRAAx] length P ≐ succ D)
    (hNorm : Γ ⊢[PRAAx] rationalLE (coefficientNorm P) (natCode (headBudget R))) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub
      (GaussianRationalLowCoefficientConvolution.term P (exponential p R e)
        D (e*degree e) e i)
      (GaussianRationalLowCoefficientConvolution.term P (exponential q R e)
        D (e*degree e) e i)))
      (fraction (rowFactor R e*radiusNumerator p q) (radiusDenominator p q)) := by
  let j := LeanProofs.IPRA.PTm.monus D i
  let k := LeanProofs.IPRA.PTm.monus (e*degree e) (LeanProofs.IPRA.PTm.monus e i)
  have hDegree := GaussianGammaFiniteCoefficientStability.output_degree_bound (Γ := Γ) e e e (le_refl e)
  have hf := GaussianRationalMonicReconstruction.monus_le_left (Γ := Γ) e i
  have hi := le_trans hf hDegree
  have codes := qsub_congr (Γ := Γ) (exponent_inside (exponential p R e) (e*degree e) _ hi)
    (exponent_inside (exponential q R e) (e*degree e) _ hi)
  have expBound := RationalArgmin.rationalLE_congr (qL1_congr codes) (.eqRefl _)
    (exponential_error_norm p q R e _ hR hf)
  have hEntry : Γ ⊢[PRAAx] lt j (length P) :=
    lt_congr (.eqRefl _) hLength.eqSymm
      ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))
  have headBound := RationalArgmin.transitive (GaussianCoefficientNormEntries.coefficient_entry_bound _ _ hEntry) hNorm
  have product := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply (Γ := Γ)
    (entry P j) (qsub (entry (exponential p R e) k) (entry (exponential q R e) k)))
      (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ (GaussianRationalL1.qL1_nonnegative _)
        (GaussianRationalSyntheticBounds.natCode_nonnegative _) headBound expBound)
  have code : Γ ⊢[PRAAx] multiply (natCode (headBudget R))
      (fraction (exponentialFactor R e*radiusNumerator p q) (radiusDenominator p q)) ≐
      fraction (rowFactor R e*radiusNumerator p q) (radiusDenominator p q) :=
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) (denominator_positive p q)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by unfold rowFactor; ipra_ring) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr
    (qL1_congr (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _)).eqSymm code product

theorem row_error (p q R e i : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub
      (GaussianRationalLowCoefficientConvolution.term (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) (exponential p R e)
        (succ (two*R)) (e*degree e) e i)
      (GaussianRationalLowCoefficientConvolution.term (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) (exponential q R e)
        (succ (two*R)) (e*degree e) e i)))
      (fraction (rowFactor R e*radiusNumerator p q) (radiusDenominator p q)) :=
  row_error_of_head (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) (succ (two*R)) p q R e i hR
    (GaussianGammaEulerHeadPolynomial.polynomial_length _) (head_norm R hR)

/-- Sum the same row estimate for any common head with the original norm bound. -/
theorem cauchy_error_of_head (P D p q R e : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hLength : Γ ⊢[PRAAx] length P ≐ succ D)
    (hNorm : Γ ⊢[PRAAx] rationalLE (coefficientNorm P) (natCode (headBudget R))) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub
      (GaussianRationalLowCoefficientConvolution.cauchySum P (exponential p R e)
        D (e*degree e) e)
      (GaussianRationalLowCoefficientConvolution.cauchySum P (exponential q R e)
        D (e*degree e) e)))
      (fraction (modulus R e*radiusNumerator p q) (radiusDenominator p q)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have lengthShift : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift P) ≐ succ (Syn.shift D) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,PTm.subst_succ,Syn.shift] using hLength.shift
  have normShift : Γ.map Fm.shift ⊢[PRAAx] rationalLE (coefficientNorm (Syn.shift P))
      (natCode (headBudget (Syn.shift R))) := by
    simpa only [Fm.shift,RationalArgmin.subst_rationalLE,GaussianCoefficientL1.subst_coefficientNorm,
      GaussianRationalSyntheticBounds.subst_natCode,subst_headBudget,Syn.shift] using hNorm.shift
  have rows : Γ ⊢[PRAAx] GaussianFiniteSumL1Variation.termsError
      GaussianRationalLowCoefficientConvolution.termBody GaussianRationalLowCoefficientConvolution.termBody (succ e)
      (GaussianRationalLowCoefficientConvolution.data P (exponential p R e) D (e*degree e) e)
      (GaussianRationalLowCoefficientConvolution.data P (exponential q R e) D (e*degree e) e)
      (fraction (rowFactor R e*radiusNumerator p q) (radiusDenominator p q)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (succ e)) :: Γ.map Fm.shift
    have codes := qsub_congr (Γ := Δ)
      (GaussianRationalLowCoefficientConvolution.term_at (Syn.shift P)
        (exponential (Syn.shift p) (Syn.shift R) (Syn.shift e)) (Syn.shift D) (Syn.shift e*degree (Syn.shift e)) (Syn.shift e) (var 0))
      (GaussianRationalLowCoefficientConvolution.term_at (Syn.shift P)
        (exponential (Syn.shift q) (Syn.shift R) (Syn.shift e)) (Syn.shift D) (Syn.shift e*degree (Syn.shift e)) (Syn.shift e) (var 0))
    simpa only [Δ,GaussianFiniteSumL1Variation.termsError,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,
      subst_exponential,PTm.subst_mul,PTm.subst_succ,PTm.subst_zero,
      GaussianGammaReciprocalDegreeCells.subst_degree,GaussianEuclideanDistanceName.subst_fraction,subst_rowFactor,
      GaussianGammaInputPrecisionNorm.subst_radiusNumerator,GaussianGammaInputPrecisionNorm.subst_radiusDenominator] using
      RationalArgmin.rationalLE_congr (qL1_congr codes).eqSymm (.eqRefl _)
        (row_error_of_head (Syn.shift P) (Syn.shift D) (Syn.shift p) (Syn.shift q)
          (Syn.shift R) (Syn.shift e) (var 0) hs.wk lengthShift.wk normShift.wk)
  have sum := GaussianFiniteSumL1Variation.sum_error _ _ _ _ _ _ rows
  have code : Γ ⊢[PRAAx] multiply (natCode (succ e)) (fraction (rowFactor R e*radiusNumerator p q) (radiusDenominator p q)) ≐
      fraction (modulus R e*radiusNumerator p q) (radiusDenominator p q) :=
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) (denominator_positive p q)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by unfold modulus; ipra_ring) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) code sum

theorem cauchy_error (p q R e : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub
      (GaussianRationalLowCoefficientConvolution.cauchySum (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) (exponential p R e)
        (succ (two*R)) (e*degree e) e)
      (GaussianRationalLowCoefficientConvolution.cauchySum (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) (exponential q R e)
        (succ (two*R)) (e*degree e) e)))
      (fraction (modulus R e*radiusNumerator p q) (radiusDenominator p q)) :=
  cauchy_error_of_head (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) (succ (two*R)) p q R e hR
    (GaussianGammaEulerHeadPolynomial.polynomial_length _) (head_norm R hR)

theorem fixed_coefficient_distance (p q R e : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (he : Γ ⊢[PRAAx] le e (succ (two*R))) : Γ ⊢[PRAAx]
    distanceBounded (fixedCoefficient p R e) (fixedCoefficient q R e)
      (modulus R e*radiusNumerator p q) (radiusDenominator p q) := by
  have hD := GaussianGammaFiniteCoefficientStability.output_degree_bound (Γ := Γ) e e e (le_refl e)
  have codes := qsub_congr (Γ := Γ)
    (GaussianRationalLowCoefficientConvolution.product_exponent (GaussianGammaEulerHeadPolynomial.polynomial (two*R))
      (exponential p R e) (succ (two*R)) (e*degree e) e he hD)
    (GaussianRationalLowCoefficientConvolution.product_exponent (GaussianGammaEulerHeadPolynomial.polynomial (two*R))
      (exponential q R e) (succ (two*R)) (e*degree e) e he hD)
  exact GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (denominator_positive p q)
    (RationalArgmin.rationalLE_congr (qL1_congr codes).eqSymm (.eqRefl _) (cauchy_error p q R e hR))

theorem canonical_coefficient_distance (p q e : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (fixedCoefficient p (succ e) e) (fixedCoefficient q (succ e) e)
      (modulus (succ e) e*radiusNumerator p q) (radiusDenominator p q) :=
  fixed_coefficient_distance p q (succ e) e (zero_lt_succ e)
    (le_of_eq_add (d := e+succ two) (by ipra_ring))

theorem original_fixed_Gamma_coefficient_precision_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (distanceBounded (fixedCoefficient (var 0) (succ (var 2)) (var 2)) (fixedCoefficient (var 1) (succ (var 2)) (var 2))
      (modulus (succ (var 2)) (var 2)*radiusNumerator (var 0) (var 1)) (radiusDenominator (var 0) (var 1))) :=
  closeUniv 3 (canonical_coefficient_distance _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaFixedCoefficientVariation
