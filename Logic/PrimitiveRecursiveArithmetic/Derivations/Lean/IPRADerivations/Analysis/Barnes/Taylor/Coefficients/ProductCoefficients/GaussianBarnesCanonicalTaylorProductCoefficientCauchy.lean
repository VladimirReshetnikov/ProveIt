import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorCoefficientMassGap
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorMass
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProduct
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianPolynomialExponentialCoefficientVariation
import IPRADerivations.Analysis.FiniteOperations.FiniteSums.GaussianFiniteSumL1Variation
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

open_ipra
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
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside termBody term_at cauchySum)
open GaussianRationalL1 (qL1 qL1_nonnegative)
open GaussianRationalMetric (qsub)
open GaussianRationalPolynomialBuffers (leftPad)
open GaussianRationalSyntheticBounds (natCode natCode_nonnegative)
open GaussianRationalSyntheticDivision (qsub_congr)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (multiply)

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

@[simp] theorem subst_headCap {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (headCap z R B) = headCap (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [headCap,headPolynomial,GaussianRationalPolynomialExponentialRecomposition.coefficientBudget,
    RationalSupMetric.numeratorOf]

@[simp] theorem subst_exponentialError {l : ℕ} (σ : Fin n → PTm l) (p R M K : PTm n) :
    Syn.subst σ (exponentialError p R M K) =
      exponentialError (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ K) := by
  simp [exponentialError,massError,massCap,GaussianBarnesCanonicalExponentTaylorMass.coefficientCap,
    GaussianBarnesCanonicalExponentTaylorMass.linearCap,GaussianBarnesCanonicalExponentTaylorMass.squareCap,
    GaussianBarnesCanonicalExponentTaylorMass.stirlingCap,GaussianBarnesCanonicalExponentTaylorMass.quadraticCap,
    GaussianBarnesCanonicalExponentTaylorMass.halfCap,GaussianBarnesCanonicalPrefactor.negativeHalf,
    GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,pw,one,two]

@[simp] theorem subst_rowError {l : ℕ} (σ : Fin n → PTm l) (p z R B M : PTm n) :
    Syn.subst σ (rowError p z R B M) = rowError (Syn.subst σ p) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ M) := by simp [rowError]

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

theorem padded_head_coefficient_bound (z R B e i : PTm n) :
    Γ ⊢[PRAAx] rationalLE (qL1 (entry (paddedHead z R B e) (monus (paddedDegree R e) i)))
      (natCode (headCap z R B)) := by
  let P := paddedHead z R B e
  have hi : Γ ⊢[PRAAx] lt (monus (paddedDegree R e) i) (length P) :=
    lt_congr (.eqRefl _) (padded_head_length z R B e).eqSymm
      ((succ_monus_succ _ _).eqTrans (Common.monus_le_self _ _))
  have mass : Γ ⊢[PRAAx] rationalLE (coefficientNorm P) (natCode (headCap z R B)) :=
    rationalLE_congr (GaussianPolynomialNormBuffers.norm_padding (headPolynomial z R B) e).eqSymm (.eqRefl _)
      (GaussianRationalPolynomialExponentialRecomposition.computed_mass (headPolynomial z R B))
  exact RationalArgmin.transitive (GaussianCoefficientNormEntries.coefficient_entry_bound _ _ hi) mass

/-- Propagate a uniform finite exponential coefficient error through the
original centered-head convolution at the retained degree. -/
theorem product_gap_of_exponential_bounds (q t z R B r s M e H E : PTm n)
    (he : Γ ⊢[PRAAx] le e (previous M))
    (bounds :
      let sh (u : PTm n) := Syn.shift u
      let Δ := lt (var 0) (succ (sh e)) :: Γ.map Fm.shift
      let N := previous (sh M)
      ∀ j : PTm (n+1), (Δ ⊢[PRAAx] le j N) →
        (Δ ⊢[PRAAx] rationalLE
          (qL1 (entry (paddedHead (sh z) (sh R) (sh B) (sh e))
            (monus (paddedDegree (sh R) (sh e)) (var 0)))) (natCode (sh H)) ⋏
          rationalLE (qL1 (qsub (exponentCoefficient (exponential (sh q) (sh z) (sh R) (sh B) (sh r) (sh M) N) (N*N) j)
            (exponentCoefficient (exponential (sh t) (sh z) (sh R) (sh B) (sh s) (sh M) N) (N*N) j))) (sh E))) :
    Γ ⊢[PRAAx] rationalLE
      (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B s M e)))
      (multiply (natCode (succ e)) (multiply (natCode H) E)) := by
  let P := paddedHead z R B e
  let K := paddedDegree R e
  let N := previous M
  let x := cd P (exponentPrefix q z R B r M) K N e
  let y := cd P (exponentPrefix t z R B s M) K N e
  let error := multiply (natCode H) E
  have rows : Γ ⊢[PRAAx] termsError termBody termBody (succ e) x y error := by
    refine .allI (.impI ?_)
    let sh (u : PTm n) := Syn.shift u
    let i : PTm (n+1) := var 0
    let Δ := lt i (succ (sh e)) :: Γ.map Fm.shift
    let j := monus (sh e) i
    let L := previous (sh M)
    let D := paddedDegree (sh R) (sh e)
    let HP := paddedHead (sh z) (sh R) (sh B) (sh e)
    let C := exponentPrefix (sh q) (sh z) (sh R) (sh B) (sh r) (sh M)
    let F := exponentPrefix (sh t) (sh z) (sh R) (sh B) (sh s) (sh M)
    let a := entry HP (monus D i)
    let b := entry C (monus L j)
    let c := entry F (monus L j)
    have he' : Δ ⊢[PRAAx] le (sh e) L := by simpa [Δ,sh,i,L,Fm.shift,Syn.shift] using he.shift.wk
    have hj := le_trans (Common.monus_le_self (sh e) i) he'
    have row := bounds j hj
    have read := qsub_congr (prefix_reader (sh q) (sh z) (sh R) (sh B) (sh r) (sh M) j hj)
      (prefix_reader (sh t) (sh z) (sh R) (sh B) (sh s) (sh M) j hj)
    have gap : Δ ⊢[PRAAx] rationalLE (qL1 (qsub b c)) (sh E) :=
      rationalLE_congr (qL1_congr read).eqSymm (.eqRefl _) row.andE₂
    have scaled := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply (Γ := Δ) a (qsub b c))
      (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ (qL1_nonnegative _) (natCode_nonnegative _)
        row.andE₁ gap)
    have code := (qsub_congr (Γ := Δ) (term_at HP C D L (sh e) i) (term_at HP F D L (sh e) i)).eqTrans
      (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference a b c)
    simpa only [termsError,Δ,sh,i,P,K,N,x,y,error,L,D,HP,C,F,Syn.shift,
      GaussianRationalLowCoefficientConvolution.subst_data,subst_exponentPrefix,subst_paddedHead,subst_paddedDegree,
      GaussianBarnesCanonicalHigherRows.subst_previous,ConciseIPRA.PTm.subst_succ,
      GaussianRationalSyntheticBounds.subst_natCode,RationalArithmetic.subst_multiply] using
      rationalLE_congr (qL1_congr code).eqSymm (.eqRefl _) scaled
  exact rationalLE_congr
    (qL1_congr (qsub_congr (coefficient_reader q z R B r M e he) (coefficient_reader t z R B s M e he))).eqSymm
    (.eqRefl _) (GaussianFiniteSumL1Variation.sum_error termBody termBody (succ e) x y error rows)

theorem late_product_gap_with_head (p q t z R B r s M e H : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q)) (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s)
    (head :
      let sh (u : PTm n) := Syn.shift u
      let Δ := lt (var 0) (succ (sh e)) :: Γ.map Fm.shift
      Δ ⊢[PRAAx] rationalLE (qL1 (entry (paddedHead (sh z) (sh R) (sh B) (sh e))
        (monus (paddedDegree (sh R) (sh e)) (var 0)))) (natCode (sh H))) :
    Γ ⊢[PRAAx] rationalLE
      (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B s M e)))
      (multiply (natCode (succ e)) (multiply (natCode H) (exponentialError p R M (previous M)))) := by
  refine product_gap_of_exponential_bounds q t z R B r s M e H (exponentialError p R M (previous M)) he ?_
  intro sh Δ N j hj
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.wk
  have clock_budget {w : PTm n} (h : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit w)) :
      Δ ⊢[PRAAx] le (prefactorGain (sh R)*unit (sh p)) (unit (sh w)) := by
    simpa [Δ,sh,Fm.shift,Syn.shift,prefactorGain,GaussianBarnesCanonicalExponentTaylorCoefficientCauchy.linearGain,
      GaussianBarnesCanonicalPrefactorLipschitz.halfGain,GaussianBarnesCanonicalPrefactor.negativeHalf,one,two] using h.shift.wk
  have tail_budget {w : PTm n} (h : Γ ⊢[PRAAx] le (cutoff p R M) w) :
      Δ ⊢[PRAAx] le (cutoff (sh p) (sh R) (sh M)) (sh w) := by
    simpa [Δ,sh,Fm.shift,Syn.shift,cutoff,GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.tailGain,two] using h.shift.wk
  refine .andI head ?_
  simpa only [Δ,sh,N,Syn.shift,subst_exponentialError,GaussianBarnesCanonicalHigherRows.subst_previous] using
    exponential_gap (sh p) (sh q) (sh t) (sh z) (sh R) (sh B) (sh r) (sh s) (sh M) N j hz' hj
      (clock_budget hq) (clock_budget ht) (tail_budget hr) (tail_budget hs)

theorem late_product_gap (p q t z R B r s M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q)) (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s) :
    Γ ⊢[PRAAx] rationalLE
      (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B s M e))) (productError p z R B M e) := by
  refine late_product_gap_with_head p q t z R B r s M e (headCap z R B) hz he hq ht hr hs ?_
  dsimp only
  simpa only [Syn.shift,subst_headCap] using padded_head_coefficient_bound (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift e) (var 0)

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
