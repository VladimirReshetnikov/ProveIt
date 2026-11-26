import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorFixedCutoff
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProductCoefficientCauchy

/-!
# Retiming the actual Barnes Taylor product at a fixed finite cutoff

The fixed-cutoff exponent mass estimate propagates through the original
finite exponential and the original centered-head convolution. The
coefficient estimate only requires late prefactor samples.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductFixedCutoff

open_ipra
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer buffer_length)
open GaussianBarnesCanonicalExponentTaylorCoefficientCauchy (linearGain)
open GaussianBarnesCanonicalExponentTaylorCoefficientMassGap (massError)
open GaussianBarnesCanonicalExponentTaylorMass (massCap mass)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (prefactorGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProduct (headPolynomial)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy
  (exponential exponentialError exponentPrefix paddedHead paddedDegree headCap rowError productError productCoefficient
    padded_head_length coefficient_reader subst_exponentPrefix subst_paddedHead subst_paddedDegree subst_rowError)
open GaussianCoefficientL1 (coefficientNorm qL1_congr)
open GaussianCoefficientNameBounds (unit)
open GaussianFiniteSumL1Variation (termsError)
open GaussianRationalL1 (qL1 qL1_nonnegative)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside term termBody term_at)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticBounds (natCode natCode_nonnegative)
open GaussianRationalSyntheticDivision (qsub_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem exponential_gap (p q t z R B r M K e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t)) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (exponentCoefficient (exponential q z R B r M K) (K*previous M) e)
      (exponentCoefficient (exponential t z R B r M K) (K*previous M) e))) (exponentialError p R M K) :=
  GaussianPolynomialExponentialCoefficientVariation.original_coefficient_variation
    (buffer q z R B r M) (buffer t z R B r M) (previous M) K (massCap R M) (massError p M) e
    (buffer_length q z R B r M) (buffer_length t z R B r M) (mass q z R B r M hz) (mass t z R B r M hz)
    (GaussianBarnesCanonicalExponentTaylorFixedCutoff.late_mass_gap p q t z R B r M hz hq ht) he

private theorem exponential_prefix_reader (q z R B r M e : PTm n) (he : Γ ⊢[PRAAx] le e (previous M)) :
    let N := previous M
    Γ ⊢[PRAAx] entry (exponentPrefix q z R B r M) (monus N e) ≐
      exponentCoefficient (exponential q z R B r M N) (N*N) e := by
  let N := previous M
  have hm : Γ ⊢[PRAAx] le N (N*N) :=
    le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N (zero_lt_succ (succ M)))
  exact (GaussianPolynomialLowPrefix.original_reader (exponential q z R B r M N) (N*N) N e he).eqTrans
    (exponent_inside _ _ _ (le_trans he hm)).eqSymm

private theorem row_gap (p q t z R B r M e i : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t)) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (term (paddedHead z R B e) (exponentPrefix q z R B r M) (paddedDegree R e) (previous M) e i)
      (term (paddedHead z R B e) (exponentPrefix t z R B r M) (paddedDegree R e) (previous M) e i))) (rowError p z R B M) := by
  let N := previous M
  let P := paddedHead z R B e
  let C := exponentPrefix q z R B r M
  let D := exponentPrefix t z R B r M
  let j := monus e i
  let a := entry P (monus (paddedDegree R e) i)
  let b := entry C (monus N j)
  let c := entry D (monus N j)
  have hj := le_trans (GaussianRationalMonicReconstruction.monus_le_left e i) he
  have codes := qsub_congr (exponential_prefix_reader q z R B r M j hj) (exponential_prefix_reader t z R B r M j hj)
  have expGap : Γ ⊢[PRAAx] rationalLE (qL1 (qsub b c)) (exponentialError p R M N) :=
    rationalLE_congr (qL1_congr codes).eqSymm (.eqRefl _) (exponential_gap p q t z R B r M N j hz hj hq ht)
  have hi : Γ ⊢[PRAAx] lt (monus (paddedDegree R e) i) (length P) :=
    lt_congr (.eqRefl _) (padded_head_length z R B e).eqSymm
      ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))
  have headMass : Γ ⊢[PRAAx] rationalLE (coefficientNorm P) (natCode (headCap z R B)) :=
    rationalLE_congr (GaussianPolynomialNormBuffers.norm_padding (headPolynomial z R B) e).eqSymm (.eqRefl _)
      (GaussianRationalPolynomialExponentialRecomposition.computed_mass (headPolynomial z R B))
  have ha := RationalArgmin.transitive (GaussianCoefficientNormEntries.coefficient_entry_bound _ _ hi) headMass
  have product := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply (Γ := Γ) a (qsub b c))
    (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ (qL1_nonnegative _) (natCode_nonnegative _) ha expGap)
  exact rationalLE_congr (qL1_congr (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference a b c)).eqSymm
    (.eqRefl _) product

theorem late_product_gap (p q t z R B r M e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t)) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B r M e))) (productError p z R B M e) := by
  let P := paddedHead z R B e
  let K := paddedDegree R e
  let N := previous M
  let x := GaussianRationalLowCoefficientConvolution.data P (exponentPrefix q z R B r M) K N e
  let y := GaussianRationalLowCoefficientConvolution.data P (exponentPrefix t z R B r M) K N e
  have rows : Γ ⊢[PRAAx] termsError termBody termBody (succ e) x y (rowError p z R B M) := by
    refine .allI (.impI ?_)
    let a (u : PTm n) := Syn.shift u
    let Δ := lt (var 0) (succ (a e)) :: Γ.map Fm.shift
    have hz' : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using hz.shift.wk
    have he' : Δ ⊢[PRAAx] le (a e) (previous (a M)) := by simpa [Δ,a,Fm.shift,Syn.shift] using he.shift.wk
    have shift_budget {w : PTm n} (h : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit w)) :
        Δ ⊢[PRAAx] le (prefactorGain (a R)*unit (a p)) (unit (a w)) := by
      simpa [Δ,a,Fm.shift,Syn.shift,prefactorGain,linearGain,GaussianBarnesCanonicalPrefactorLipschitz.halfGain,
        GaussianBarnesCanonicalPrefactor.negativeHalf,one,two] using h.shift.wk
    have codes := qsub_congr (Γ := Δ)
      (term_at (paddedHead (a z) (a R) (a B) (a e)) (exponentPrefix (a q) (a z) (a R) (a B) (a r) (a M))
        (paddedDegree (a R) (a e)) (previous (a M)) (a e) (var 0))
      (term_at (paddedHead (a z) (a R) (a B) (a e)) (exponentPrefix (a t) (a z) (a R) (a B) (a r) (a M))
        (paddedDegree (a R) (a e)) (previous (a M)) (a e) (var 0))
    simpa only [termsError,Δ,a,P,K,N,x,y,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,
      subst_exponentPrefix,subst_paddedHead,subst_paddedDegree,GaussianBarnesCanonicalHigherRows.subst_previous,subst_rowError,
      ConciseIPRA.PTm.subst_succ] using rationalLE_congr (qL1_congr codes).eqSymm (.eqRefl _)
        (row_gap (a p) (a q) (a t) (a z) (a R) (a B) (a r) (a M) (a e) (var 0) hz' he' (shift_budget hq) (shift_budget ht))
  exact rationalLE_congr
    (qL1_congr (qsub_congr (coefficient_reader q z R B r M e he) (coefficient_reader t z R B r M e he))).eqSymm
    (.eqRefl _) (GaussianFiniteSumL1Variation.sum_error termBody termBody (succ e) x y (rowError p z R B M) rows)

theorem actual_Barnes_fixed_cutoff_Taylor_product_coefficient_Cauchy_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let q := var 1
     let t := var 2
     let z := var 3
     let R := var 4
     let B := var 5
     let r := var 6
     let M := var 7
     let e := var 8
     (source z R B ⋏ (le e (previous M) ⋏ (le (prefactorGain R*unit p) (unit q) ⋏ le (prefactorGain R*unit p) (unit t)))) ⟶
       rationalLE (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B r M e))) (productError p z R B M e)) :=
  closeUniv 9 (.impI (late_product_gap (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductFixedCutoff
