import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalExponentTaylorCoefficientMassGap
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalExponentTaylorMass
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorProduct
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianPolynomialExponentialCoefficientVariation
import IPRADerivations.Analysis.FiniteOperations.GaussianFiniteSumL1Variation
import IPRADerivations.Analysis.Polynomials.Products.GaussianPolynomialProductLeftPadding
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianPolynomialNormBuffers

/-!
# Retained coefficients of the original Barnes Taylor product

The finite exponential coefficient error uses the actual exponent buffer
difference. Convolution with the kept-power polynomial then
controls the original degree-truncated Taylor product at every retained
degree. Leading zero padding preserves the original coefficient reader.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductCoefficientCauchy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer buffer_length)
open GaussianBarnesCanonicalExponentTaylorMass (massCap mass)
open GaussianBarnesCanonicalExponentTaylorCoefficientMassGap (late_mass_gap massError)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (prefactorGain cutoff)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalTaylorProduct (headPolynomial headDegree)
open GaussianCoefficientL1 (coefficientNorm qL1_congr)
open GaussianCoefficientNameBounds (unit)
open GaussianFiniteSumL1Variation (termsError)
open GaussianPolynomialExponentialCoefficientVariation (variationBudget)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside term termBody term_at cauchySum)
open GaussianRationalL1 (qL1 qL1_nonnegative)
open GaussianRationalMetric (qsub)
open GaussianRationalPolynomialBuffers (leftPad)
open GaussianRationalSyntheticBounds (natCode natCode_nonnegative)
open GaussianRationalSyntheticDivision (qsub_congr)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (multiply)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "PP" => GaussianRationalPolynomialExponential.polynomial
local notation "ExpoPrefix" => GaussianRationalPolynomialExponentialProductTruncation.exponentialPrefix
local notation "Product" => GaussianRationalPolynomialProduct.product
local notation "cd" => GaussianRationalLowCoefficientConvolution.data

def exponential (q z R B r M K : PTm n) : PTm n := PP (buffer q z R B r M) (previous M) K
def exponentialError (p R M K : PTm n) : PTm n := multiply (variationBudget (massCap R M) K) (massError p M)

def exponentPrefix (q z R B r M : PTm n) : PTm n := ExpoPrefix (buffer q z R B r M) (previous M) (previous M) (previous M)
def paddedHead (z R B e : PTm n) : PTm n := leftPad (headPolynomial z R B) e
def paddedDegree (R e : PTm n) : PTm n := e+headDegree R

def headCap (z R B : PTm n) : PTm n :=
  GaussianRationalPolynomialExponentialRecomposition.coefficientBudget (headPolynomial z R B)

def rowError (p z R B M : PTm n) : PTm n :=
  multiply (natCode (headCap z R B)) (exponentialError p R M (previous M))

def productError (p z R B M e : PTm n) : PTm n := multiply (natCode (succ e)) (rowError p z R B M)

def productCoefficient (q z R B r M e : PTm n) : PTm n :=
  entry (GaussianBarnesCanonicalTaylorProduct.polynomial z R B (buffer q z R B r M) (previous M) (previous M))
    (monus (previous M) e)

@[simp] theorem subst_exponentPrefix {l : ℕ} (σ : Fin n → PTm l) (q z R B r M : PTm n) :
    Syn.subst σ (exponentPrefix q z R B r M) = exponentPrefix (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ M) := by simp [exponentPrefix]

@[simp] theorem subst_paddedHead {l : ℕ} (σ : Fin n → PTm l) (z R B e : PTm n) :
    Syn.subst σ (paddedHead z R B e) = paddedHead (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ e) := by
  simp [paddedHead,headPolynomial]

@[simp] theorem subst_paddedDegree {l : ℕ} (σ : Fin n → PTm l) (R e : PTm n) :
    Syn.subst σ (paddedDegree R e) = paddedDegree (Syn.subst σ R) (Syn.subst σ e) := by simp [paddedDegree,headDegree]

@[simp] theorem subst_rowError {l : ℕ} (σ : Fin n → PTm l) (p z R B M : PTm n) :
    Syn.subst σ (rowError p z R B M) = rowError (Syn.subst σ p) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ M) := by
  simp [rowError,headCap,headPolynomial,GaussianRationalPolynomialExponentialRecomposition.coefficientBudget,
    exponentialError,massCap,GaussianBarnesCanonicalExponentTaylorMass.coefficientCap,
    GaussianBarnesCanonicalExponentTaylorMass.linearCap,GaussianBarnesCanonicalExponentTaylorMass.squareCap,
    GaussianBarnesCanonicalExponentTaylorMass.stirlingCap,GaussianBarnesCanonicalExponentTaylorMass.quadraticCap,
    GaussianBarnesCanonicalExponentTaylorMass.halfCap,GaussianBarnesCanonicalExponentTaylorCoefficientMassGap.massError,
    GaussianBarnesCanonicalPrefactor.negativeHalf,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,
    RationalSupMetric.numeratorOf,pw,one,two]

theorem exponential_gap (p q t z R B r s M K e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q)) (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s) :
    Γ ⊢[PRAAx] rationalLE
      (qL1 (qsub (exponentCoefficient (exponential q z R B r M K) (K*previous M) e)
        (exponentCoefficient (exponential t z R B s M K) (K*previous M) e))) (exponentialError p R M K) :=
  GaussianPolynomialExponentialCoefficientVariation.original_coefficient_variation
    (buffer q z R B r M) (buffer t z R B s M) (previous M) K (massCap R M) (massError p M) e
    (buffer_length q z R B r M) (buffer_length t z R B s M) (mass q z R B r M hz) (mass t z R B s M hz)
    (late_mass_gap p q t z R B r s M hz hq ht hr hs) he

private theorem prefix_reader (q z R B r M e : PTm n) (he : Γ ⊢[PRAAx] le e (previous M)) :
    let N := previous M
    Γ ⊢[PRAAx] entry (exponentPrefix q z R B r M) (monus N e) ≐ exponentCoefficient (exponential q z R B r M N) (N*N) e := by
  let N := previous M
  have hm : Γ ⊢[PRAAx] le N (N*N) :=
    le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N (zero_lt_succ (succ M)))
  exact (GaussianPolynomialLowPrefix.original_reader (exponential q z R B r M N) (N*N) N e he).eqTrans
    (exponent_inside _ _ _ (le_trans he hm)).eqSymm

theorem padded_head_length (z R B e : PTm n) : Γ ⊢[PRAAx] length (paddedHead z R B e) ≐ succ (paddedDegree R e) :=
  GaussianPolynomialProductLeftPadding.factor_length _ _ _ (GaussianBarnesCanonicalCenteredHead.polynomial_length z B (initial R))

theorem coefficient_reader (q z R B r M e : PTm n) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] productCoefficient q z R B r M e ≐
      cauchySum (paddedHead z R B e) (exponentPrefix q z R B r M) (paddedDegree R e) (previous M) e := by
  let N := previous M
  let P := headPolynomial z R B
  let E := exponentPrefix q z R B r M
  let K := headDegree R
  have raw := GaussianRationalPolynomialExponentialProductTruncation.coefficient (Γ := Γ)
    P (buffer q z R B r M) K N N e he
  have padded := GaussianPolynomialProductLeftPadding.original_entry P E K N e e
    (GaussianBarnesCanonicalCenteredHead.polynomial_length z B (initial R))
    (GaussianRationalPolynomialExponentialProductTruncation.exponential_prefix_length _ _ _ _)
    (le_trans he (le_add_left _ _))
  exact raw.eqTrans (padded.eqSymm.eqTrans
    (GaussianRationalLowCoefficientConvolution.coefficient_cauchy (paddedHead z R B e) E (paddedDegree R e) N e (le_add_right _ _) he))

private theorem product_row_gap (p q t z R B r s M e i : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q)) (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s) :
    Γ ⊢[PRAAx] rationalLE
      (qL1 (qsub (term (paddedHead z R B e) (exponentPrefix q z R B r M) (paddedDegree R e) (previous M) e i)
        (term (paddedHead z R B e) (exponentPrefix t z R B s M) (paddedDegree R e) (previous M) e i))) (rowError p z R B M) := by
  let N := previous M
  let P := paddedHead z R B e
  let C := exponentPrefix q z R B r M
  let D := exponentPrefix t z R B s M
  let j := monus e i
  let k := monus N j
  let a := entry P (monus (paddedDegree R e) i)
  let b := entry C k
  let c := entry D k
  have hj := le_trans (GaussianRationalMonicReconstruction.monus_le_left e i) he
  have code := qsub_congr (prefix_reader q z R B r M j hj) (prefix_reader t z R B s M j hj)
  have ef : Γ ⊢[PRAAx] rationalLE (qL1 (qsub b c)) (exponentialError p R M N) :=
    rationalLE_congr (qL1_congr code).eqSymm (.eqRefl _) (exponential_gap p q t z R B r s M N j hz hj hq ht hr hs)
  have hi : Γ ⊢[PRAAx] lt (monus (paddedDegree R e) i) (length P) :=
    lt_congr (.eqRefl _) (padded_head_length z R B e).eqSymm
      ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))
  have mass : Γ ⊢[PRAAx] rationalLE (coefficientNorm P) (natCode (headCap z R B)) :=
    rationalLE_congr (GaussianPolynomialNormBuffers.norm_padding (headPolynomial z R B) e).eqSymm (.eqRefl _)
      (GaussianRationalPolynomialExponentialRecomposition.computed_mass (headPolynomial z R B))
  have hb := RationalArgmin.transitive (GaussianCoefficientNormEntries.coefficient_entry_bound _ _ hi) mass
  have product := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply (Γ := Γ) a (qsub b c))
    (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ (qL1_nonnegative _) (natCode_nonnegative _) hb ef)
  exact rationalLE_congr (qL1_congr (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference a b c)).eqSymm (.eqRefl _) product

theorem late_product_gap (p q t z R B r s M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q)) (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s) :
    Γ ⊢[PRAAx] rationalLE
      (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B s M e))) (productError p z R B M e) := by
  let P := paddedHead z R B e
  let K := paddedDegree R e
  let N := previous M
  let x := cd P (exponentPrefix q z R B r M) K N e
  let y := cd P (exponentPrefix t z R B s M) K N e
  have rows : Γ ⊢[PRAAx] termsError termBody termBody (succ e) x y (rowError p z R B M) := by
    refine .allI (.impI ?_)
    let a (u : PTm n) := Syn.shift u
    let Δ := lt (var 0) (succ (a e)) :: Γ.map Fm.shift
    have hz' : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using hz.shift.wk
    have he' : Δ ⊢[PRAAx] le (a e) (previous (a M)) := by simpa [Δ,a,Fm.shift,Syn.shift] using he.shift.wk
    have hq' : Δ ⊢[PRAAx] le (prefactorGain (a R)*unit (a p)) (unit (a q)) := by
      simpa [Δ,a,Fm.shift,Syn.shift,prefactorGain,GaussianBarnesCanonicalExponentTaylorCoefficientCauchy.linearGain,
        GaussianBarnesCanonicalPrefactorLipschitz.halfGain,GaussianBarnesCanonicalPrefactor.negativeHalf,one,two] using hq.shift.wk
    have ht' : Δ ⊢[PRAAx] le (prefactorGain (a R)*unit (a p)) (unit (a t)) := by
      simpa [Δ,a,Fm.shift,Syn.shift,prefactorGain,GaussianBarnesCanonicalExponentTaylorCoefficientCauchy.linearGain,
        GaussianBarnesCanonicalPrefactorLipschitz.halfGain,GaussianBarnesCanonicalPrefactor.negativeHalf,one,two] using ht.shift.wk
    have hr' : Δ ⊢[PRAAx] le (cutoff (a p) (a R) (a M)) (a r) := by
      simpa [Δ,a,Fm.shift,Syn.shift,cutoff,GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.tailGain,two] using hr.shift.wk
    have hs' : Δ ⊢[PRAAx] le (cutoff (a p) (a R) (a M)) (a s) := by
      simpa [Δ,a,Fm.shift,Syn.shift,cutoff,GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.tailGain,two] using hs.shift.wk
    have code := qsub_congr (Γ := Δ)
      (term_at (paddedHead (a z) (a R) (a B) (a e)) (exponentPrefix (a q) (a z) (a R) (a B) (a r) (a M))
        (paddedDegree (a R) (a e)) (previous (a M)) (a e) (var 0))
      (term_at (paddedHead (a z) (a R) (a B) (a e)) (exponentPrefix (a t) (a z) (a R) (a B) (a s) (a M))
        (paddedDegree (a R) (a e)) (previous (a M)) (a e) (var 0))
    simpa only [termsError,Δ,a,P,K,N,x,y,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,
      subst_exponentPrefix,subst_paddedHead,subst_paddedDegree,GaussianBarnesCanonicalHigherRows.subst_previous,subst_rowError,
      ConciseIPRA.PTm.subst_succ] using rationalLE_congr (qL1_congr code).eqSymm (.eqRefl _)
        (product_row_gap (a p) (a q) (a t) (a z) (a R) (a B) (a r) (a s) (a M) (a e) (var 0)
          hz' he' hq' ht' hr' hs')
  exact rationalLE_congr
    (qL1_congr (qsub_congr (coefficient_reader q z R B r M e he) (coefficient_reader t z R B s M e he))).eqSymm
    (.eqRefl _) (GaussianFiniteSumL1Variation.sum_error termBody termBody (succ e) x y (rowError p z R B M) rows)

theorem actual_Barnes_fixed_order_Taylor_product_coefficient_Cauchy_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let p := var 0
     let q := var 1
     let t := var 2
     let z := var 3
     let R := var 4
     let B := var 5
     let r := var 6
     let s := var 7
     let M := var 8
     let e := var 9
     (source z R B ⋏ le e (previous M)) ⟶
       ((le (prefactorGain R*unit p) (unit q) ⋏ le (prefactorGain R*unit p) (unit t)) ⋏
         (le (cutoff p R M) r ⋏ le (cutoff p R M) s)) ⟶
       rationalLE (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B s M e)))
         (productError p z R B M e)) :=
  closeUniv 10 (.impI (.impI (late_product_gap _ _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductCoefficientCauchy
