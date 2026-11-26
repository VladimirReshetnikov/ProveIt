import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorFirstGridRate
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorEvenGridReadback
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalFixedTaylorDerivativeZero
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceQuotientApproximation
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceQuotientProperness

/-!
# The first derivative of the original fixed Barnes product

The literal quotient and the degree-one name both read the same first
rows of the fixed-cutoff Taylor grid, with separately paid observation
errors. The resulting rate retains the exact quotient and coefficient
programs at independent precisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 720000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorFirstDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded_add bounded_mono normSq scale)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData finite_regular)
open GaussianBarnesCanonicalFiniteTaylorDiskGridLimit (clockGain)
open GaussianBarnesCanonicalFiniteTaylorEvenGridReadback (prefactorClock)
open GaussianBarnesCanonicalFiniteTaylorFirstGridRate (rowCost step_size)
open GaussianBarnesCanonicalFiniteTaylorGrid (polynomial shifted_point)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid literal_at scaledPolynomial)
open GaussianBarnesCanonicalFixedTaylorDerivativeName (readbackGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianL1 (norm1 normSq_le_norm1_square)
open GaussianNameEquivalence (cross_at cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at)
open GaussianPolynomialForwardDifferenceGrid (point)
open GaussianRationalCoefficientScaling (scaled_lookup)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale_congr natScale_one_canonical natScale_zero)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Analysis.Products (fact)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (monus num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "vd" => GaussianBarnesCanonicalProduct.literalData
local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "G" => GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finiteF
local notation "gd" => GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finiteData
local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data
local notation "precision" => GaussianBarnesCanonicalExponentTaylorBallSchedule.precision

def literalQuotientData (z h R B r : PTm n) : PTm n :=
  qd V V (vd (add z h) (R+one) B (initial (R+one)+r)) (vd z (R+one) B (initial (R+one)+r)) h B

def gain (R : PTm n) : PTm n := GaussianBarnesCanonicalFiniteTaylorFirstGridRate.gain R+num 3

def baseClock (B : PTm n) : PTm n := exponent B zero
def coefficientClock (z R B : PTm n) : PTm n := exponent (readbackGain z (R+one) B one) (baseClock B)
def polynomialClock (z R B : PTm n) : PTm n :=
  prefactorClock (coefficientClock z R B) z R B zero one+exponent (num 4*B*clockGain R) (baseClock B)

def linearCoefficient (q z R B H r : PTm n) : PTm n :=
  GaussianBarnesCanonicalTaylorProductDerivativeName.finiteCoefficient (precision q (R+one) (two*H)) z (R+one) B r zero one

def coefficientCost (q z R B H r : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyModulus finiteNameF constantF (finiteData z (R+one) B r)
    (linearCoefficient q z R B H r)+one

def observationClock (z h R B r : PTm n) : PTm n :=
  let q := polynomialClock z R B
  exponent (num 4*B*rowCost q z h R B r+num 6*B+(one+coefficientCost q z R B (norm1 h) r)) (baseClock B)

@[simp] private theorem subst_prefactorRadius {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (GaussianBarnesCanonicalDiskBound.prefactorRadius R) =
      GaussianBarnesCanonicalDiskBound.prefactorRadius (Syn.subst σ R) := by
  let expression {l : ℕ} (v : PTm l) : PTm l :=
    let a := GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
    let b := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF zero
    (two*(v*a)+two)+(two*(v+(v*v)*(one+b))+two)
  change Syn.subst σ (expression R) = expression (Syn.subst σ R)
  simp [expression,one,two]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (gain R) = gain (Syn.subst σ R) := by
  simp [gain,GaussianBarnesCanonicalFiniteTaylorFirstGridRate.gain,GaussianBarnesCanonicalFiniteTaylorDiskGridLimit.analyticGain,
    GaussianBarnesCanonicalFiniteTaylorFirstPolynomial.quadraticCap,GaussianBarnesCanonicalFiniteCentralDiskBound.cap,
    GaussianBarnesCanonicalCentralUniformBound.prefixCap,GaussianBarnesCanonicalCentralUniformBound.prefixArgumentCap,
    GaussianBarnesCanonicalCentralUniformBound.correctionCap,GaussianBarnesCanonicalFactor.exponentRadius,one,two]

@[simp] theorem subst_literalQuotientData {m : ℕ} (σ : Fin n → PTm m) (z h R B r : PTm n) :
    Syn.subst σ (literalQuotientData z h R B r) = literalQuotientData (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) := by simp [literalQuotientData,one]

@[simp] private theorem subst_fixed_data {m : ℕ} (σ : Fin n → PTm m) (z R B r J e : PTm n) :
    Syn.subst σ (fd z R B r J e) = fd (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ r) (Syn.subst σ J) (Syn.subst σ e) := by
  simp [GaussianBarnesCanonicalFixedTaylorDerivativeName.data,GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData,
    finiteData,GaussianBarnesCanonicalFiniteCentralExponential.prefixExpData,GaussianBarnesCanonicalSingleExponential.prefixData,
    GaussianBarnesCanonicalSingleExponential.prefactorExponentData,GaussianGammaFiniteApproximantName.exponentialInputData]

theorem wide_sources (z h R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hs : Γ ⊢[PRAAx] le ((two*stepDivisor R)*norm1 h) B) :
    Γ ⊢[PRAAx] source z (R+one) B ⋏ source (add z h) (R+one) B := by
  have hH := le_trans (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (norm1 h) (le_succ_self one))) (step_size h R B hs)
  have wide : Γ ⊢[PRAAx] le (R*B+B) ((R+one)*B) := le_of_eq_add (d := zero) (by ipra_ring)
  exact .andI (.andI hz.andE₁ (bounded_mono hz.andE₂ (le_trans (le_add_right _ _) wide)))
    (.andI hz.andE₁ (bounded_mono (bounded_add hz.andE₂ (normSq_le_norm1_square h)) (le_trans
      (le_congr (add_comm _ _) (add_comm _ _) (add_le_add_right (R*B) hH)) wide)))

private theorem budget_base (B : PTm n) : Γ ⊢[PRAAx] le B (unit (baseClock B)) :=
  le_congr ((congrMul (.eqRefl B) (pw_zero two)).eqTrans (Common.mul_one_right B)) (.eqRefl _)
    (query_budget B zero)

private theorem node_error (t z h R B r j w : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hs : Γ ⊢[PRAAx] le ((two*stepDivisor R)*norm1 h) B) (hj : Γ ⊢[PRAAx] lt j (succ two))
    (hw : Γ ⊢[PRAAx] source w (R+one) B) (he : Γ ⊢[PRAAx] ofGaussian (add z (scale j h)) B ≐ ofGaussian w B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 V t (vd w (R+one) B (initial (R+one)+r)))
      (entry (literalGrid t z h R B r two) j) two (unit t) := by
  let v := add z (scale j h)
  let N := initial (R+one)+r
  have delta := GaussianBarnesCanonicalFiniteTaylorGrid.step_bound h (norm1 h) two j
    (normSq_le_norm1_square h) (Common.le_of_lt_succ hj)
  have hv : Γ ⊢[PRAAx] source v (R+one) B := .andI hz.andE₁
    (bounded_mono (bounded_add hz.andE₂ (bounded_mono delta (step_size h R B hs)))
      (le_of_eq_add (d := zero) (by ipra_ring)))
  have eq := GaussianBarnesCanonicalFiniteProperness.prefix_cross w v (R+one) (R+one) B B N hw hv he.eqSymm
  have d := cross_at V V (vd w (R+one) B N) (vd v (R+one) B N) t t eq
  have raw := distance_congr (.eqRefl _) (literal_at t z h R B r two j hj).eqSymm (.eqRefl _) (.eqRefl _) d
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive t)) (unit_positive t)
    (le_of_eq_add (d := zero) (by ipra_ring)) raw

private theorem literal_readback (p t z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) (hs : Γ ⊢[PRAAx] le ((two*stepDivisor R)*norm1 h) B)
    (ht : Γ ⊢[PRAAx] le (num 6*(B*B)) (unit t)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (QF V V) p (literalQuotientData z h R B r))
      (GaussianBarnesCanonicalFiniteTaylorFirstGridRate.quotient t z h R B r)
      (norm1 h*unit p+B) (B*unit p) := by
  let S := R+one
  let N := initial S+r
  let x := vd (add z h) S B N
  let y := vd z S B N
  let W := literalGrid t z h R B r two
  let T := unit t
  let P := unit p
  let H := norm1 h
  have hb := hz.andE₁
  have hT := unit_positive (Γ := Γ) t
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have dom := wide_sources z h R B hz hs
  have front : Γ ⊢[PRAAx] ofGaussian (add z (scale one h)) B ≐ ofGaussian (add z h) B :=
    (shifted_point z h B one hb).eqTrans ((qadd_congr (.eqRefl _) (natScale_one_canonical _ (ofGaussian_canonical _ _ hb))).eqTrans
      (GaussianBarnesCanonicalHeadPolynomialDerivative.argument_add z h B hb))
  have base : Γ ⊢[PRAAx] ofGaussian (add z (scale zero h)) B ≐ ofGaussian z B :=
    (shifted_point z h B zero hb).eqTrans ((qadd_congr (.eqRefl _) (natScale_zero _)).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (ofGaussian_canonical _ _ hb)))
  have bound := GaussianNamedDifferenceQuotientApproximation.finite_error V V p t t x y h B
    (entry W one) (entry W zero) two T two T
    (.andI (GaussianBarnesCanonicalProduct.literal_regular _ _ _ _ dom.andE₂)
      (.andI (GaussianBarnesCanonicalProduct.literal_regular _ _ _ _ dom.andE₁) (.andI hb hn))) hT hT
    (node_error t z h R B r one (add z h) hz hs (le_succ_self two) dom.andE₂ front)
    (node_error t z h R B r zero z hz hs (zero_lt_succ two) dom.andE₁ base)
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianNamedDifferenceQuotientApproximation.denominator_positive _ _ _ _ _ hT hT)
    (positive_product _ _ hb (unit_positive p))
    (by
      dsimp only [GaussianNamedDifferenceQuotientApproximation.numerator,GaussianNamedDifferenceQuotientApproximation.denominator]
      ipra_le 𝔞(P)*𝔞(P)*𝔞(T)*𝔞(T)*𝔞(T)*(sl ht+𝔞(T)*sl hH)) bound

private theorem linear_value (t q z R B H r : PTm n) :
    Γ ⊢[PRAAx] entry (scaledPolynomial t q z R B H r zero two) one ≐
      qmul (ap2 finiteNameF t (finiteData z (R+one) B r)) (linearCoefficient q z R B H r) := by
  let S := R+one
  let w := precision q S (two*H)
  let a := productCoefficient w z S B r zero one
  let P := polynomial q z R B H r zero two
  let x := ap2 finiteNameF t (finiteData z S B r)
  have hLen : Γ ⊢[PRAAx] length P ≐ succ two :=
    GaussianBarnesCanonicalFiniteWeightedTaylorValue.polynomial_length q z S B (two*H) r zero
  have hIndex : Γ ⊢[PRAAx] lt one (length P) := lt_congr (.eqRefl _) hLen.eqSymm (le_succ_self two)
  have ix : Γ ⊢[PRAAx] entry P one ≐ a :=
    entry_congr (.eqRefl _) (show Γ ⊢[PRAAx] monus (two : PTm n) one ≐ one from
      (succ_monus_succ _ _).eqTrans (monus_zero one)).eqSymm
  have factorial : Γ ⊢[PRAAx] fact (one : PTm n) ≐ one :=
    (fact_succ zero zero).eqTrans ((congrMul (LeanProofs.IPRA.Analysis.ExponentialSeries.fact_zero' (Γ := Γ))
      (.eqRefl one)).eqTrans (one_mul one))
  have ac : Γ ⊢[PRAAx] GaussianRationalHorner.canonical a :=
    GaussianRationalHorner.canonical_congr ix.eqSymm (GaussianRationalSyntheticDivision.canonical_coefficient_at P one
      (GaussianRationalPolynomialExponentialProductTruncation.polynomial_canonical _ _ _ _ _) hIndex)
  have fa := (natScale_congr factorial (.eqRefl a)).eqTrans (natScale_one_canonical a ac)
  exact (scaled_lookup P x one hIndex).eqTrans
    (qmul_congr (.eqRefl x) (ix.eqTrans fa.eqSymm))

private theorem coefficient_readback (u t k q z h R B r J : PTm n) (hz : Γ ⊢[PRAAx] source z (R+one) B)
    (hH : Γ ⊢[PRAAx] le one (norm1 h)) (hk : Γ ⊢[PRAAx] le (readbackGain z (R+one) B one*B) (unit k))
    (hq : Γ ⊢[PRAAx] le (prefactorClock k z R B zero one) q)
    (ht : Γ ⊢[PRAAx] le ((one+coefficientCost q z R B (norm1 h) r)*B) (unit t)) :
    Γ ⊢[PRAAx] distanceBounded (entry (scaledPolynomial t q z R B (norm1 h) r zero two) one)
      (ap2 F u (fd z (R+one) B r J one)) (two*norm1 h*unit u+B) (B*unit u) := by
  let H := norm1 h
  let S := R+one
  let K := unit k
  let T := unit t
  let U := unit u
  let w := precision q S (two*H)
  let x := finiteData z S B r
  let a := linearCoefficient q z R B H r
  let y := gd w z S B r zero one
  let b := fd z S B r J one
  let C := coefficientCost q z R B H r
  let E := K*U*T
  let A := readbackGain z S B one
  have hB := hz.andE₁
  have hK := unit_positive (Γ := Γ) k
  have hE := GaussianNamedInverseRate.denominator_positive K u t hK
  let M := fd z S B r zero one
  have hb : Γ ⊢[PRAAx] le one (previous J) := zero_lt_succ (succ J)
  have hM : Γ ⊢[PRAAx] le one (previous (zero : PTm n)) := le_succ_self one
  have ready : Γ ⊢[PRAAx] GaussianBarnesCanonicalFixedTaylorCoefficientName.ready k z S B zero one w := by
    have paid := query_budget (Γ := Γ) (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.prefactorGain S)
      (GaussianBarnesCanonicalTaylorProductCoefficientName.clock k z S B zero one)
    exact le_trans paid (unit_monotone (le_trans hq (le_add_right q _)))
  have fixed := GaussianBarnesCanonicalFixedTaylorDerivativeName.readback_rate k w z S B r zero one hz hM ready
  have exactOrder := GaussianBarnesCanonicalTaylorDerivativeOrderInvariance.fixed_cross z S B r J zero one hz hb hM
  have regular := GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finite_regular w z S B r zero one hz
  have moved := GaussianNamedRateTransport.transport F G F G M y b y A K hK fixed exactOrder (cross_refl G y regular)
  have first := rate_at F G b y A K u t moved
  have compute := GaussianNameRingLaws.multiply_sample_error finiteNameF constantF x a t
    (finite_regular z S B r hz) (constant_regular a)
  have last : Γ ⊢[PRAAx] distanceBounded (ap2 G t y) (entry (scaledPolynomial t q z R B H r zero two) one) C T :=
    distance_congr (.eqRefl _) ((qmul_congr (.eqRefl _) (constant_at t a)).eqTrans
      (linear_value t q z R B H r).eqSymm) (.eqRefl _) (.eqRefl _) compute
  have widened : Γ ⊢[PRAAx] distanceBounded (ap2 G t y) _ (C*K*U) E :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive t) hE
      (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) last
  have joined := distance_triangle_same _ _ _ _ _ _ hE first widened
  apply distance_symmetric _ _ _ _ (positive_product _ _ hB (unit_positive u))
  exact distance_radius_mono _ _ _ _ _ _ hE (positive_product _ _ hB (unit_positive u))
    (by
      change Γ ⊢[PRAAx] le ((A*U*T+K*(U+T)+C*K*U)*(B*U)) ((two*H*U+B)*(K*U*T))
      have payK : Γ ⊢[PRAAx] le (A*B) K := hk
      have payT : Γ ⊢[PRAAx] le ((one+C)*B) T := ht
      have hOne : Γ ⊢[PRAAx] le one H := hH
      ipra_le 𝔞(U)*𝔞(U)*𝔞(T)*sl payK+𝔞(K)*𝔞(U)*𝔞(U)*sl payT+
        2*𝔞(K)*𝔞(U)*𝔞(U)*𝔞(T)*sl hOne) joined

theorem observations (p u z h R B r J : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) (hs : Γ ⊢[PRAAx] le ((two*stepDivisor R)*norm1 h) B) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (QF V V) p (literalQuotientData z h R B r)) (ap2 F u (fd z (R+one) B r J one))
      (rateNumerator (gain R*norm1 h) B p u) (rateDenominator B p u) := by
  let H := norm1 h
  let K := coefficientClock z R B
  let Q := polynomialClock z R B
  let T := observationClock z h R B r
  let C := rowCost Q z h R B r
  let O := coefficientCost Q z R B H r
  let S := R+one
  let U := unit u
  let P := unit p
  let D := B*P*U
  have hB := hz.andE₁
  have hD := GaussianNamedInverseRate.denominator_positive B p u hB
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have pay := budget_base (Γ := Γ) B
  have payCoeff : Γ ⊢[PRAAx] le (readbackGain z S B one*B) (unit K) :=
    le_trans (Common.mul_le_mul (le_refl _) pay) (query_budget _ _)
  have payQ : Γ ⊢[PRAAx] le (num 4*(B*B)*clockGain R) (unit Q) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (Common.mul_le_mul (le_refl (num 4*B*clockGain R)) pay))
      (le_trans (query_budget _ _) (unit_monotone (le_add_left _ _)))
  have payT : Γ ⊢[PRAAx] le ((num 4*B*C+num 6*B+(one+O))*B) (unit T) :=
    le_trans (Common.mul_le_mul (le_refl _) pay) (query_budget _ _)
  have payRows : Γ ⊢[PRAAx] le (num 4*(B*B)*C) (unit T) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right B (le_trans (le_add_right _ _) (le_add_right _ _)))) payT
  have payLiteral : Γ ⊢[PRAAx] le (num 6*(B*B)) (unit T) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right B (le_trans (le_add_left _ _) (le_add_right _ _)))) payT
  have payReadback : Γ ⊢[PRAAx] le ((one+O)*B) (unit T) := le_trans (mul_le_mul_right B (le_add_left _ _)) payT
  have readLiteral := literal_readback p T z h R B r hz hn hs payLiteral
  have grid := GaussianBarnesCanonicalFiniteTaylorFirstGridRate.to_linear T Q z h R B r hz hn hs payQ payRows
  have readCoeff := coefficient_readback u T K Q z h R B r J (wide_sources z h R B hz hs).andE₁
    hH payCoeff (le_add_right _ _) payReadback
  have first := distance_radius_mono _ _ _ _ ((H*P+B)*U) D (positive_product _ _ hB (unit_positive p)) hD
    (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) readLiteral
  have middle := distance_radius_mono _ _ _ _ ((GaussianBarnesCanonicalFiniteTaylorFirstGridRate.gain R*H)*P*U) D hB hD
    (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) grid
  have last := distance_radius_mono _ _ _ _ ((two*H*U+B)*P) D (positive_product _ _ hB (unit_positive u)) hD
    (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) readCoeff
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [gain,rateNumerator,H,P,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first (distance_triangle_same _ _ _ _ _ _ hD middle last))

theorem rate (z h R B r J : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) (hs : Γ ⊢[PRAAx] le ((two*stepDivisor R)*norm1 h) B) :
    Γ ⊢[PRAAx] independentRate (QF V V) F (literalQuotientData z h R B r) (fd z (R+one) B r J one) (gain R*norm1 h) B := by
  refine .allI (.allI ?_)
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Syn.shift,Fm.shift] using hz.shift.shift
  have hn' : Δ ⊢[PRAAx] le one (normSq (sh h)) := by simpa [Δ,sh,Syn.shift,Fm.shift] using hn.shift.shift
  have hs' : Δ ⊢[PRAAx] le ((two*stepDivisor (sh R))*norm1 (sh h)) (sh B) :=
    by simpa [Δ,sh,Syn.shift,Fm.shift,two,one] using hs.shift.shift
  simpa [independentRate,sh,Δ,Syn.shift,one] using
    observations (var 1) (var 0) (sh z) (sh h) (sh R) (sh B) (sh r) (sh J) hz' hn' hs'

theorem actual_Barnes_fixed_literal_first_derivative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let z := var 0
       let h := var 1
       let R := var 2
       let B := var 3
       let r := var 4
       let J := var 5
       (source z R B ⋏ le one (normSq h) ⋏ le ((two*stepDivisor R)*norm1 h) B) ⟶
         independentRate (QF V V) F (literalQuotientData z h R B r) (fd z (R+one) B r J one) (gain R*norm1 h) B) :=
  closeUniv 6 (.impI (rate _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorFirstDerivative
