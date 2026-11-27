import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalProperness
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProductDerivativeName
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.FiniteFactors.GaussianBarnesCanonicalHeadDerivativeFractionProperness
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponentialStability

/-!
# The original degree-zero Barnes Taylor name

At zero displacement the exponent increment has constant coefficient
zero. Its stored exponential has constant coefficient one at every
cutoff. The remaining head coefficient and the original central
exponential are exactly the existing Barnes value factorization.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeZero

open_ipra
open ComplexLogarithmRemainder (add zeroCode)
open GaussianBarnesCanonicalBaseProductShift (powerBody powerProduct)
open GaussianBarnesCanonicalCenteredExponentialShift (baseData base_regular)
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer buffer_zero)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (cutoff precision)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalTaylorProduct (headPolynomial headDegree)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameConjugation (equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalHorner
  (canonical_unique evaluate hornerF horner_succ ofGaussian ofGaussian_canonical ofGaussian_represents
    qmul qmul_canonical qzero zero_represents)
open GaussianRationalLowCoefficientConvolution (coefficient_cauchy exponent_inside term term_at termBody)
open GaussianRationalMonicReduction (evaluate_congr singleton_lookup)
open GaussianRationalNaturalScale (natScale_as_product natScale_congr natScale_one_canonical naturalPoint)
open GaussianRationalPolynomialExponential (stage_zero)
open GaussianRationalPolynomialExponentialProductTruncation (exponentialPrefix)
open GaussianRationalPolynomialExponentialStability (finite_exponential_cutoff)
open GaussianRationalSyntheticCoefficientValues (qmul_recode_left)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_right qone qzero_canonical)
open GaussianReciprocalHorner (qadd_zero_right qmul_one_right)
open GaussianTranslatedNonconstant (recode recode_canonical)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "K" => GaussianBarnesCanonicalTaylorProductCoefficientName.nameF
local notation "kd" => GaussianBarnesCanonicalTaylorProductCoefficientName.data
local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "SC" => GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientF
local notation "sd" => GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData
local notation "E" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.exponentF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data

private theorem evaluate_zero (P N : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N) :
    Γ ⊢[PRAAx] evaluate P qzero ≐ recode (entry P N) :=
  (congrAp3 hornerF hP (.eqRefl P) (.eqRefl qzero)).eqTrans
    ((horner_succ P qzero N).eqTrans (qadd_congr (qmul_zero_right _) (.eqRefl _)))

private theorem head_at_zero (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] evaluate (headPolynomial z R B) qzero ≐ powerProduct z B (initial R) := by
  let q := ofGaussian z B
  let w := ofGaussian zeroCode B
  have hz : Γ ⊢[PRAAx] w ≐ qzero :=
    canonical_unique _ _ zeroCode B (ofGaussian_canonical _ _ hB) qzero_canonical hB
      (ofGaussian_represents _ _ hB) (zero_represents B)
  have shift := GaussianBarnesCanonicalHeadPolynomialDerivative.argument_add z zeroCode B hB
  have center : Γ ⊢[PRAAx] ofGaussian (add z zeroCode) B ≐ q :=
    shift.eqSymm.eqTrans ((qadd_congr (.eqRefl q) hz).eqTrans (qadd_zero_right q (ofGaussian_canonical _ _ hB)))
  exact (evaluate_congr (.eqRefl _) hz.eqSymm).eqTrans
    ((GaussianBarnesCanonicalCenteredHead.original_evaluation z zeroCode B (initial R) hB).eqTrans
      (GaussianBarnesCanonicalHeadDerivativeFractionProperness.original_power_equal _ _ B B _ hB hB center))

private theorem exponential_constant (P m : PTm n) (h₀ : Γ ⊢[PRAAx] entry P m ≐ qzero) :
    Γ ⊢[PRAAx] entry (exponentialPrefix P m m m) m ≐ qone := by
  let Q := GaussianRationalPolynomialExponential.polynomial P m m
  have base : Γ ⊢[PRAAx] GaussianRationalPolynomialExponentialStability.coefficient P m m zero zero ≐ qone :=
    (exponent_inside _ _ _ (zero_le _)).eqTrans
      ((entry_congr (stage_zero _ _ _) ((monus_zero _).eqTrans (zero_mul m))).eqTrans (singleton_lookup qone))
  exact (entry_congr (.eqRefl _) (monus_zero m).eqSymm).eqTrans
    ((GaussianPolynomialLowPrefix.original_reader Q (m*m) m zero (zero_le m)).eqTrans
      ((exponent_inside Q (m*m) zero (zero_le _)).eqSymm.eqTrans
        ((finite_exponential_cutoff P m m zero h₀ (zero_le m) (zero_le m)).eqTrans base)))

private theorem singleton_convolution (P Q N M : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalLowCoefficientConvolution.cauchySum P Q N M zero ≐ qmul (entry P N) (entry Q M) := by
  let a := GaussianRationalLowCoefficientConvolution.data P Q N M zero
  have row : Γ ⊢[PRAAx] term P Q N M zero zero ≐ qmul (entry P N) (entry Q M) :=
    qmul_congr (entry_congr (.eqRefl _) (monus_zero N))
      (entry_congr (.eqRefl _) ((congrMonus (.eqRefl M) (monus_zero zero)).eqTrans (monus_zero M)))
  exact GaussianRationalFiniteSum.sum_singleton termBody a
    ((term_at P Q N M zero zero).eqTrans row) (qmul_canonical _ _)

theorem coefficient_at_zero (q z R B r M : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] productCoefficient q z R B r M zero ≐ powerProduct z B (initial R) := by
  let P := headPolynomial z R B
  let N := headDegree R
  let m := previous M
  let A := buffer q z R B r M
  let Q := exponentialPrefix A m m m
  have exp₀ := exponential_constant (Γ := Γ) A m (buffer_zero q z R B r M)
  have hP : Γ ⊢[PRAAx] length P ≐ succ N :=
    GaussianBarnesCanonicalCenteredHead.polynomial_length z B (initial R)
  have c := GaussianRationalPolynomialExponentialProductTruncation.coefficient (Γ := Γ) P A N m m zero (zero_le m)
  have row := coefficient_cauchy (Γ := Γ) P Q N m zero (zero_le N) (zero_le m)
  have head := (qmul_recode_left (Γ := Γ) (entry P N) qone).eqSymm.eqTrans
    (qmul_one_right _ (recode_canonical (entry P N)))
  exact c.eqTrans (row.eqTrans ((singleton_convolution P Q N m).eqTrans
    ((qmul_congr (.eqRefl _) exp₀).eqTrans (head.eqTrans
      ((evaluate_zero P N hP).eqSymm.eqTrans (head_at_zero z R B hB))))))

theorem coefficient_cross (z R B M : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent K C (kd z R B M zero) (powerProduct z B (initial R)) := by
  apply equal_samples_cross K C _ _
    (GaussianBarnesCanonicalTaylorProductCoefficientName.regular z R B M zero hz (zero_le _)) (constant_regular _)
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  let p : PTm (n+1) := var 0
  let k := GaussianBarnesCanonicalTaylorProductCoefficientName.clock p (sh z) (sh R) (sh B) (sh M) zero
  have hB : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [sh,Fm.shift,Syn.shift] using hz.andE₁.shift
  have atZero := (GaussianBarnesCanonicalTaylorProductCoefficientName.sample_at p (sh z) (sh R) (sh B) (sh M) zero).eqTrans
    (coefficient_at_zero (precision k (sh R)) (sh z) (sh R) (sh B) (cutoff k (sh R) (sh M)) (sh M) hB)
  simpa only [sh,p,Syn.shift,GaussianBarnesCanonicalTaylorProductCoefficientName.subst_data,
    GaussianBarnesCanonicalBaseProductShift.subst_powerProduct,GaussianBarnesCanonicalLogSchedule.subst_initial,
    ConciseIPRA.PTm.subst_zero] using
    atZero.eqTrans (constant_at p (powerProduct (sh z) (sh B) (initial (sh R)))).eqSymm

theorem value_cross (z R B M : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent F V (fd z R B M zero) (vd z R B) := by
  let h := powerProduct z B (initial R)
  let a : PTm n := naturalPoint (fact zero)
  let e := baseData z R B
  have hr := constant_regular (Γ := Γ) h
  have ar := constant_regular (Γ := Γ) a
  have er := base_regular z R B hz
  have kr := GaussianBarnesCanonicalTaylorProductCoefficientName.regular z R B M zero hz (zero_le _)
  have sr := GaussianBarnesCanonicalTaylorProductDerivativeName.coefficient_regular z R B M zero hz (zero_le _)
  have hc := GaussianRationalFiniteProduct.product_canonical (Γ := Γ) powerBody (initial R)
    (GaussianBarnesCanonicalPolynomialShift.data z B)
  have oneFact : Γ ⊢[PRAAx] qmul a h ≐ h :=
    (natScale_as_product (fact zero) h).eqSymm.eqTrans
      ((natScale_congr (LeanProofs.IPRA.Analysis.ExponentialSeries.fact_zero' (Γ := Γ)) (.eqRefl h)).eqTrans
        (natScale_one_canonical h hc))
  have factor : Γ ⊢[PRAAx] crossEquivalent SC C (sd z R B M zero) h :=
    cross_trans _ _ _ _ _ _ (multiply_cross C C K C a a (kd z R B M zero) h ar ar kr hr
      (cross_refl C a ar) (coefficient_cross z R B M hz))
      (GaussianGammaDigammaTwoShiftNamedSize.constant_product a h h oneFact)
  have product : Γ ⊢[PRAAx] crossEquivalent F (multiplyF E C) (fd z R B M zero) (multiplyData E C e h) :=
    multiply_cross E E SC C e e (sd z R B M zero) h er er sr hr (cross_refl E e er) factor
  exact cross_trans _ _ _ _ _ _ product
    (cross_trans _ _ _ _ _ _ (GaussianNameRingLaws.multiply_commutative E C e h er hr)
      (cross_symm _ _ _ _ (GaussianBarnesCanonicalSingleExponential.factorization z R B hz)))

theorem radius_cross (z R S B M : PTm n) (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source z S B) :
    Γ ⊢[PRAAx] crossEquivalent F F (fd z R B M zero) (fd z S B M zero) :=
  cross_trans _ _ _ _ _ _ (value_cross z R B M hR)
    (cross_trans _ _ _ _ _ _ (GaussianBarnesCanonicalProperness.independent_radii z R S B hR hS)
      (cross_symm _ _ _ _ (value_cross z S B M hS)))

theorem actual_Barnes_zero_factorial_Taylor_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let M := var 3
     source z R B ⟶ crossEquivalent F V (fd z R B M zero) (vd z R B)) :=
  closeUniv 4 (.impI (value_cross _ _ _ _ Prf.hyp0))

theorem actual_Barnes_zero_factorial_Taylor_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let S := var 2
     let B := var 3
     let M := var 4
     source z R B ⟶ source z S B ⟶ crossEquivalent F F (fd z R B M zero) (fd z S B M zero)) :=
  closeUniv 5 (.impI (.impI (radius_cross _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeZero
