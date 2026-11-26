import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorGrid
import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifferenceGridError
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# Literal Barnes observations and one scaled Taylor grid

At every grid index use the same finite scalar observation to scale the
stored polynomial. A bounded sum pays for each row's actual product
normalization. The finite Taylor comparison supplies the analytic error.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridObservations

open_ipra
open ComplexLogarithmRemainder (bounded)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData finite_regular)
open GaussianBarnesCanonicalFiniteWeightedTaylorValue (nameF)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyData multiplyModulus)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator)
open GaussianPolynomialForwardDifferenceGrid (point samples sample_lookup)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianRationalCoefficientScaling (scaled evaluation_linearity)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (evaluate ofGaussian positive_product qmul qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "S" => finiteNameF
local notation "C" => constantF
local notation "literal" => GaussianBarnesCanonicalFiniteTaylorGrid.literalData
local notation "polynomial" => GaussianBarnesCanonicalFiniteTaylorGrid.polynomial
local notation "gridData" => GaussianBarnesCanonicalFiniteTaylorGrid.gridData
local notation "TaylorNumerator" => GaussianBarnesCanonicalFiniteWeightedTaylorValue.numerator
local notation "TaylorDenominator" => GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator

private def literalParams (t z h R B r : PTm n) : PTm n := pairT t (pairT z (pairT h (pairT R (pairT B r))))

private def literalBody : PTm 2 :=
  let u : PTm 2 := var 1
  let a := sndT u
  let b := sndT a
  let c := sndT b
  let d := sndT c
  ap2 V (fstT u) (literal (fstT a) (fstT b) (fstT c) (fstT d) (sndT d) (var 0))

def literalGrid (t z h R B r e : PTm n) : PTm n := sequence literalBody (succ e) (literalParams t z h R B r)

def scaledPolynomial (s p z R B H r M e : PTm n) : PTm n :=
  scaled (polynomial p z R B H r M e) (ap2 S s (finiteData z (R+one) B r))

def polynomialGrid (s p z h R B H r M e : PTm n) : PTm n :=
  samples (scaledPolynomial s p z R B H r M e) (succ e) qzero (ofGaussian h B)

private def capBody : PTm 2 := multiplyModulus S C (fstT (var 1)) (entry (sndT (var 1)) (var 0))+one

def cap (x P e : PTm n) : PTm n := ap2 (sumF capBody) (succ e) (pairT x P)

def observationCap (p z h R B H r M e : PTm n) : PTm n :=
  cap (finiteData z (R+one) B r) (samples (polynomial p z R B H r M e) (succ e) qzero (ofGaussian h B)) e

def numerator_from_rate (t s p z h R B H r M e A : PTm n) : PTm n :=
  A*unit t*unit s+TaylorDenominator p (R+one) B M*(unit s+(one+observationCap p z h R B H r M e)*unit t)

def numerator (t s p z h R B H r M e : PTm n) : PTm n :=
  numerator_from_rate t s p z h R B H r M e (TaylorNumerator p z (R+one) B (e*H) M)

def denominator (t s p R B M : PTm n) : PTm n := rateDenominator (TaylorDenominator p (R+one) B M) t s

@[simp] private theorem subst_literal {m : ℕ} (σ : Fin n → PTm m) (z h R B r j : PTm n) :
    Syn.subst σ (literal z h R B r j) =
      literal (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ j) := by
  simp [GaussianBarnesCanonicalFiniteTaylorGrid.literalData]

@[simp] private theorem subst_finite {m : ℕ} (σ : Fin n → PTm m) (z R B r : PTm n) :
    Syn.subst σ (finiteData z R B r) = finiteData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) :=
  by simp [finiteData,GaussianBarnesCanonicalFiniteCentralExponential.prefixExpData,
    GaussianBarnesCanonicalSingleExponential.prefixData,GaussianBarnesCanonicalSingleExponential.prefactorExponentData,
    GaussianGammaFiniteApproximantName.exponentialInputData]

@[simp] private theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (p z R B H r M e : PTm n) :
    Syn.subst σ (polynomial p z R B H r M e) = polynomial (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ r) (Syn.subst σ M) (Syn.subst σ e) := by
  simp [GaussianBarnesCanonicalFiniteTaylorGrid.polynomial,GaussianBarnesCanonicalFiniteWeightedTaylorValue.polynomial,
    GaussianBarnesCanonicalTaylorProduct.polynomial,GaussianBarnesCanonicalTaylorProduct.headPolynomial,
    GaussianBarnesCanonicalTaylorProduct.headDegree,GaussianBarnesCanonicalHeadPolynomial.degree,
    GaussianBarnesCanonicalExponentTaylorBallSchedule.precision,GaussianBarnesCanonicalExponentTaylorBallSchedule.uniformCost,
    GaussianBarnesCanonicalExponentTaylorBallSchedule.stepClockCap,GaussianBarnesCanonicalExponentTaylorBallSchedule.polynomialClockCap,
    GaussianBarnesCanonicalExponentTaylorBallSchedule.squareClockCap,GaussianBarnesCanonicalExponentTaylorBallSchedule.squareCap,
    GaussianBarnesCanonicalPrefactor.negativeHalf,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,one,two]

@[simp] private theorem subst_leadingNumerator {m : ℕ} (σ : Fin n → PTm m) (p z R B H M : PTm n) :
    Syn.subst σ (TaylorNumerator p z R B H M) =
      TaylorNumerator (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ M) := by
  simp [GaussianBarnesCanonicalFiniteWeightedTaylorValue.numerator,
    GaussianBarnesCanonicalFiniteWeightedTaylorValue.numerator_with_caps,
    GaussianBarnesCanonicalFiniteExponentTaylor.scheduledNumerator,GaussianBarnesCanonicalFiniteExponentTaylor.scheduledDenominator,
    GaussianBarnesCanonicalCorrectedMercator.numerator,GaussianBarnesCanonicalCorrectedMercatorCofinal.analyticDenominator,
    GaussianBarnesCanonicalCorrectedMercator.scaleDenominator,GaussianBarnesCanonicalWeightedTaylorBall.headMass,
    GaussianBarnesCanonicalTaylorProduct.headPolynomial,GaussianBarnesCanonicalTaylorProduct.headDegree,
    GaussianBarnesCanonicalHeadPolynomial.degree,GaussianRationalPolynomialExponentialRecomposition.coefficientBudget,
    RationalSupMetric.numeratorOf,
    GaussianBarnesCanonicalTaylorRecomposition.error,GaussianBarnesCanonicalTaylorRecomposition.capGain,
    GaussianNamedRateComposition.leadingNumerator,one,two,pw]

@[simp] private theorem subst_leadingDenominator {m : ℕ} (σ : Fin n → PTm m) (p R B M : PTm n) :
    Syn.subst σ (TaylorDenominator p R B M) =
      TaylorDenominator (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ M) := by
  simp [GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator,
    GaussianBarnesCanonicalFiniteExponentTaylor.scheduledDenominator,
    GaussianBarnesCanonicalCorrectedMercatorCofinal.analyticDenominator,GaussianBarnesCanonicalCorrectedMercator.scaleDenominator,
    GaussianBarnesCanonicalTaylorRecomposition.denominator,GaussianNamedRateComposition.leadingDenominator,pw]

@[simp] theorem subst_literalGrid {m : ℕ} (σ : Fin n → PTm m) (t z h R B r e : PTm n) :
    Syn.subst σ (literalGrid t z h R B r e) = literalGrid (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ e) := by simp [literalGrid,literalParams]

@[simp] theorem subst_scaledPolynomial {m : ℕ} (σ : Fin n → PTm m) (s p z R B H r M e : PTm n) :
    Syn.subst σ (scaledPolynomial s p z R B H r M e) = scaledPolynomial (Syn.subst σ s) (Syn.subst σ p)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ r) (Syn.subst σ M) (Syn.subst σ e) :=
  by simp [scaledPolynomial]

@[simp] theorem subst_polynomialGrid {m : ℕ} (σ : Fin n → PTm m) (s p z h R B H r M e : PTm n) :
    Syn.subst σ (polynomialGrid s p z h R B H r M e) = polynomialGrid (Syn.subst σ s) (Syn.subst σ p)
      (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H)
      (Syn.subst σ r) (Syn.subst σ M) (Syn.subst σ e) := by simp [polynomialGrid]

@[simp] theorem subst_numerator_from_rate {m : ℕ} (σ : Fin n → PTm m) (t s p z h R B H r M e A : PTm n) :
    Syn.subst σ (numerator_from_rate t s p z h R B H r M e A) =
      numerator_from_rate (Syn.subst σ t) (Syn.subst σ s) (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ h)
        (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ r) (Syn.subst σ M) (Syn.subst σ e) (Syn.subst σ A) :=
  by simp [numerator_from_rate,observationCap,cap]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (t s p z h R B H r M e : PTm n) :
    Syn.subst σ (numerator t s p z h R B H r M e) = numerator (Syn.subst σ t) (Syn.subst σ s) (Syn.subst σ p)
      (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H)
      (Syn.subst σ r) (Syn.subst σ M) (Syn.subst σ e) := by simp [numerator]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (t s p R B M : PTm n) :
    Syn.subst σ (denominator t s p R B M) =
      denominator (Syn.subst σ t) (Syn.subst σ s) (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ M) :=
  by simp [denominator]

theorem literal_at (t z h R B r e j : PTm n) (hj : Γ ⊢[PRAAx] lt j (succ e)) :
    Γ ⊢[PRAAx] entry (literalGrid t z h R B r e) j ≐ ap2 V t (literal z h R B r j) := by
  let a := pairT z (pairT h (pairT R (pairT B r)))
  let b := pairT h (pairT R (pairT B r))
  let c := pairT R (pairT B r)
  let d := pairT B r
  have t₀ := snd_pair (Γ := Γ) t a
  have t₁ := (congrSnd t₀).eqTrans (snd_pair z b)
  have t₂ := (congrSnd t₁).eqTrans (snd_pair h c)
  have t₃ := (congrSnd t₂).eqTrans (snd_pair R d)
  refine (sequence_decode literalBody (x := literalParams t z h R B r) hj).eqTrans ?_
  ipra_congr (ap2 V (var 0) (literal (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) : PTm 7) with
    [fst_pair t a, (congrFst t₀).eqTrans (fst_pair z b), (congrFst t₁).eqTrans (fst_pair h c),
      (congrFst t₂).eqTrans (fst_pair R d), (congrFst t₃).eqTrans (fst_pair B r),
      (congrSnd t₃).eqTrans (snd_pair B r), .eqRefl j] using [literalBody,literalParams,inst2,a,b,c,d]

theorem cost_le_cap (x P e j : PTm n) (hj : Γ ⊢[PRAAx] lt j (succ e)) :
    Γ ⊢[PRAAx] le (multiplyModulus S C x (entry P j)+one) (cap x P e) := by
  have input := entry_congr (snd_pair (Γ := Γ) x P) (.eqRefl j)
  have cost : Γ ⊢[PRAAx] multiplyModulus S C (fstT (pairT x P)) (entry (sndT (pairT x P)) j) ≐
      multiplyModulus S C x (entry P j) := by
    ipra_congr (multiplyModulus S C (var 0) (var 1) : PTm 2) with [fst_pair x P,input]
  have body : Γ ⊢[PRAAx] inst2 capBody j (pairT x P) ≐ multiplyModulus S C x (entry P j)+one := by
    simpa [capBody,inst2,one] using congrAdd cost (.eqRefl one)
  exact le_congr body (.eqRefl _) (term_le_sum capBody (x := pairT x P) hj)

theorem denominator_positive (t s p R B M : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (denominator t s p R B M) :=
  GaussianNamedInverseRate.denominator_positive _ _ _
    (GaussianBarnesCanonicalFiniteTaylorGrid.denominator_positive p R B M hB)

theorem scaled_polynomial_length (s p z R B H r M e : PTm n) :
    Γ ⊢[PRAAx] length (scaledPolynomial s p z R B H r M e) ≐ succ (previous M) :=
  (GaussianRationalCoefficientScaling.scaled_length _ _).eqTrans
    (GaussianBarnesCanonicalFiniteWeightedTaylorValue.polynomial_length p z (R+one) B (e*H) r M)

private theorem compose_row (u v w A D t s L K : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hL : Γ ⊢[PRAAx] le L K)
    (h₁ : Γ ⊢[PRAAx] distanceBounded u v (rateNumerator A D t s) (rateDenominator D t s))
    (h₂ : Γ ⊢[PRAAx] distanceBounded v w L (unit s)) :
    Γ ⊢[PRAAx] distanceBounded u w (A*unit t*unit s+D*(unit s+(one+K)*unit t)) (rateDenominator D t s) := by
  let E := rateDenominator D t s
  let T := unit t
  let U := unit s
  let N := A*T*U+D*(U+(one+K)*T)
  let M := rateNumerator A D t s+L*(D*T)
  have hE : Γ ⊢[PRAAx] le one E := GaussianNamedInverseRate.denominator_positive D t s hD
  have next : Γ ⊢[PRAAx] distanceBounded v w (L*(D*T)) E :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive s) hE
      (le_of_eq_add (d := zero) (by dsimp only [E,T,rateDenominator]; ipra_ring)) h₂
  have fit : Γ ⊢[PRAAx] le M N := by
    dsimp only [M,N,rateNumerator,T,U]
    let 𝔞 := fun u : PTm n => Groth.ι (IPRA.Q.mk Γ u)
    ipra_le (𝔞 D*𝔞 (unit t))*sl hL
  exact distance_radius_mono _ _ _ _ _ _ hE hE (mul_le_mul_right E fit)
    (distance_triangle_same _ _ _ _ _ _ hE h₁ next)

theorem row_error_from_rate (t s p z h R B H r M e j A : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hj : Γ ⊢[PRAAx] lt j (succ e))
    (hrate : Γ ⊢[PRAAx] GaussianNamedInverseRate.independentRate V nameF (literal z h R B r j)
      (gridData p z h R B H r M e j) A (TaylorDenominator p (R+one) B M)) :
    Γ ⊢[PRAAx] distanceBounded (entry (literalGrid t z h R B r e) j) (entry (polynomialGrid s p z h R B H r M e) j)
      (numerator_from_rate t s p z h R B H r M e A) (denominator t s p R B M) := by
  let P := polynomial p z R B H r M e
  let x := finiteData z (R+one) B r
  let k := ofGaussian h B
  let w := point qzero k j
  let alphas := samples P (succ e) qzero k
  let v := entry alphas j
  let u := ap2 S s x
  let L := multiplyModulus S C x v+one
  let K := observationCap p z h R B H r M e
  let d := TaylorDenominator p (R+one) B M
  let y := gridData p z h R B H r M e j
  let ℓ := literal z h R B r j
  let v' := entry (polynomialGrid s p z h R B H r M e) j
  have hj' := Common.le_of_lt_succ hj
  have hd : Γ ⊢[PRAAx] le one d := GaussianBarnesCanonicalFiniteTaylorGrid.denominator_positive p R B M hz.andE₁
  have hz' : Γ ⊢[PRAAx] source z (R+one) B :=
    .andI hz.andE₁ (ComplexLogarithmRemainder.bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))
  have read := GaussianBarnesCanonicalFiniteTaylorGrid.grid_sample p z h R B H r M e j hj'
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 V t ℓ) (ap2 nameF s y) (rateNumerator A d t s) (rateDenominator d t s) :=
    rate_at _ _ _ _ _ _ t s hrate
  have product := GaussianNameRingLaws.multiply_sample_error S C x v s
    (finite_regular z (R+one) B r hz') (constant_regular v)
  have eval : Γ ⊢[PRAAx] qmul u (ap2 C s v) ≐ v' :=
    (qmul_congr (.eqRefl u) ((constant_at s v).eqTrans (sample_lookup P (succ e) qzero k j hj))).eqTrans
      ((evaluation_linearity P u w).eqSymm.eqTrans (sample_lookup (scaled P u) (succ e) qzero k j hj).eqSymm)
  have second : Γ ⊢[PRAAx] distanceBounded (ap2 nameF s y) v' L (unit s) :=
    distance_congr (congrAp2 nameF (.eqRefl s) read).eqSymm eval (.eqRefl _) (.eqRefl _) product
  exact distance_congr (literal_at t z h R B r e j hj).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (compose_row _ _ _ A d t s L K hd (cost_le_cap x alphas e j hj) first second)

theorem row_error (t s p z h R B H r M e j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B)
    (hj : Γ ⊢[PRAAx] lt j (succ e)) :
    Γ ⊢[PRAAx] distanceBounded (entry (literalGrid t z h R B r e) j) (entry (polynomialGrid s p z h R B H r M e) j)
      (numerator t s p z h R B H r M e) (denominator t s p R B M) :=
  row_error_from_rate t s p z h R B H r M e j _ hz hj
    (GaussianBarnesCanonicalFiniteTaylorGrid.rate p z h R B H r M e j hz hh hsmall (Common.le_of_lt_succ hj))

theorem row_bound (t s p z h R B H r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B) :
    Γ ⊢[PRAAx] rowBound (literalGrid t z h R B r e) (polynomialGrid s p z h R B H r M e) (succ e)
      (numerator t s p z h R B H r M e) (denominator t s p R B M) := by
  refine .allI (.impI ?_)
  let a (v : PTm n) := Syn.shift v
  let j : PTm (n+1) := var 0
  let Δ := lt j (succ (a e)) :: Γ.map Fm.shift
  have z' : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by
    simpa [Δ,a,j,Fm.shift,Syn.shift] using hz.shift.wk
  have h' : Δ ⊢[PRAAx] bounded (a h) (a H) := by
    simpa [Δ,a,j,Fm.shift,Syn.shift] using hh.shift.wk
  have small' : Δ ⊢[PRAAx] le ((a e*stepDivisor (a R))*a H) (a B) := by
    simpa [Δ,a,j,Fm.shift,Syn.shift] using hsmall.shift.wk
  have hi : Δ ⊢[PRAAx] lt j (succ (a e)) := Prf.hyp0
  simpa [a,j,Δ,Syn.shift] using row_error (a t) (a s) (a p) (a z) (a h) (a R) (a B) (a H)
    (a r) (a M) (a e) j z' h' small' hi

theorem actual_Barnes_finite_Taylor_grid_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (let t := var 0
     let s := var 1
     let p := var 2
     let z := var 3
     let h := var 4
     let R := var 5
     let B := var 6
     let H := var 7
     let r := var 8
     let M := var 9
     let e := var 10
     source z R B ⟶ bounded h H ⟶ le ((e*stepDivisor R)*H) B ⟶
       rowBound (literalGrid t z h R B r e) (polynomialGrid s p z h R B H r M e) (succ e)
         (numerator t s p z h R B H r M e) (denominator t s p R B M)) :=
  closeUniv 11 (.impI (.impI (.impI (row_bound _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridObservations
