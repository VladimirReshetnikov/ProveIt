import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryHyperbolic
import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryHyperbolicProductRuleAlgebra
import IPRADerivations.Analysis.Trigonometry.GaussianPiRationalScaleRepresentation
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceQuotientProperness
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport
import IPRADerivations.Analysis.Euler.GaussianEulerCompactModulus

/-!
# The product rule for the original hyperbolic sine product

The literal finite approximants feed the actual normalized increment
and derivative names. The quadratic coefficient is independent of a
common rational rescaling. The same canonical derivative name at the
unscaled base can therefore be used at each scaled unit step.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryHyperbolicProductRule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus multiply_fast product_distance sum_distance)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm point_at)
open GaussianNameRingLaws (multiply_sample_error add_sample_error)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianSineProductImaginaryFirstOrder (step)
open GaussianSineProductImaginaryFirstOrderBound (axis_disk product_bound productBound)
open GaussianSineProductImaginaryHyperbolicProductRuleAlgebra (residualBound)
open GaussianSineProductImaginaryLogDerivative (axisNumerator rationalReal product derivative)
open GaussianSineProductImaginaryCofinalDerivative (sineData cutoff)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "Pi" => GaussianGammaHalfPiName.nameF
local notation "P" => GaussianSineProductName.nameF
local notation "D" => GaussianSineProductImaginaryCofinalDerivative.derivativeF
local notation "dd" => GaussianSineProductImaginaryCofinalDerivative.derivativeData
local notation "Scale" => GaussianPiRationalScale.nameF
local notation "sd" => GaussianPiRationalScale.data false
local notation "Hyper" => GaussianSineProductImaginaryHyperbolic.productF
local notation "hd" => GaussianSineProductImaginaryHyperbolic.productData
local notation "Diff" => GaussianNamedDifference.nameF
local notation "df" => GaussianNamedDifference.data
local notation "rawValue" => GaussianSineProductImaginaryHyperbolicProductRuleAlgebra.value
local notation "rawTangent" => GaussianSineProductImaginaryHyperbolicProductRuleAlgebra.tangent

abbrev source (A B C R : PTm n) : Fm PTm n := GaussianSineProductImaginaryCofinalDerivative.source A B C R

abbrev linearF : PR 2 := multiplyF constantF D
def linearData (A B R : PTm n) : PTm n := multiplyData constantF D (rationalReal A B) (dd A B R)
abbrev sumF : PR 2 := addF P linearF
def sumData (A B R : PTm n) : PTm n := addData (sineData A B R) (linearData A B R)

abbrev derivativeF : PR 2 := multiplyF Pi sumF
def derivativeData (A B R x : PTm n) : PTm n := multiplyData Pi sumF x (sumData A B R)

abbrev incrementF : PR 2 := Diff Hyper Hyper
def incrementData (A B C R x : PTm n) : PTm n := df (hd (A+C) B R x) (hd A B R x)

abbrev weightedF : PR 2 := multiplyF constantF derivativeF
def weightedData (A B C R x : PTm n) : PTm n := multiplyData constantF derivativeF (step B C) (derivativeData A B R x)

def coefficient (R x : PTm n) : PTm n := U Pi x * residualBound R

private def productCost (A B R x : PTm n) : PTm n :=
  (multiplyModulus Scale P (sd A B R x) (sineData A B R)+one)+(two*R*productBound R+(R*U Pi x)*one)

private def linearCost (A B R : PTm n) : PTm n :=
  (multiplyModulus constantF D (rationalReal A B) (dd A B R)+one)+
    R*GaussianSineProductImaginaryCofinalDerivative.derivativeCost A B R

private def sumCost (A B R : PTm n) : PTm n := GaussianNameRingLaws.three+(one+linearCost A B R)

private def derivativeCost (A B R x : PTm n) : PTm n :=
  (multiplyModulus Pi sumF x (sumData A B R)+one)+U Pi x*sumCost A B R

private def weightedCost (A B C R x : PTm n) : PTm n :=
  (multiplyModulus constantF derivativeF (step B C) (derivativeData A B R x)+one)+R*derivativeCost A B R x

private def cost (A B C R x : PTm n) : PTm n :=
  (num 6+(productCost (A+C) B R x+productCost A B R x))+weightedCost A B C R x

@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (A B R x : PTm n) :
    Syn.subst σ (hd A B R x) = hd (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ x) := by
  simp [GaussianSineProductImaginaryHyperbolic.productData]

@[simp] theorem subst_linearData {m : ℕ} (σ : Fin n → PTm m) (A B R : PTm n) :
    Syn.subst σ (linearData A B R) = linearData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) := by simp [linearData]

@[simp] theorem subst_sumData {m : ℕ} (σ : Fin n → PTm m) (A B R : PTm n) :
    Syn.subst σ (sumData A B R) = sumData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) := by simp [sumData]

@[simp] theorem subst_derivativeData {m : ℕ} (σ : Fin n → PTm m) (A B R x : PTm n) :
    Syn.subst σ (derivativeData A B R x) = derivativeData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ x) := by
  simp [derivativeData]

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (A B C R x : PTm n) :
    Syn.subst σ (incrementData A B C R x) =
      incrementData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ R) (Syn.subst σ x) := by simp [incrementData]

@[simp] theorem subst_weightedData {m : ℕ} (σ : Fin n → PTm m) (A B C R x : PTm n) :
    Syn.subst σ (weightedData A B C R x) =
      weightedData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ R) (Syn.subst σ x) := by simp [weightedData]

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (R x : PTm n) :
    Syn.subst σ (coefficient R x) = coefficient (Syn.subst σ R) (Syn.subst σ x) := by simp [coefficient]

@[simp] private theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (A B C R x : PTm n) :
    Syn.subst σ (cost A B C R x) = cost (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ R) (Syn.subst σ x) := by
  simp [cost, productCost, weightedCost, derivativeCost, sumCost, linearCost,
    GaussianSineProductImaginaryCofinalDerivative.derivativeCost, GaussianNameRingLaws.three, productBound, one, two]

private theorem sine_regular (A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN P (sineData A B R) :=
  GaussianSineProductName.name_regular _ _ _ hB (axis_disk A B R hA)

private theorem linear_regular (A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN linearF (linearData A B R) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianSineProductImaginaryCofinalDerivative.derivative_regular A B R hB hA)

private theorem sum_regular (A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN sumF (sumData A B R) :=
  add_fast _ _ _ _ (sine_regular A B R hB hA) (linear_regular A B R hB hA)

theorem derivative_regular (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN derivativeF (derivativeData A B R x) :=
  multiply_fast _ _ _ _ (GaussianGammaHalfPiName.name_regular x) (sum_regular A B R hB hA)

theorem product_regular (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN Hyper (hd A B R x) :=
  multiply_fast _ _ _ _ (GaussianPiRationalScale.regular false A B R x hB hA) (sine_regular A B R hB hA)

private theorem scale_error (A B R p x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 Scale p (sd A B R x))
      (qmul (rationalReal A B) (ap2 Pi p x)) (two*R) (unit p) := by
  let a := rationalReal A B
  let j := GaussianBoundedConstantProductName.clock p R
  have hp := unit_positive (Γ := Γ) p
  have hj := unit_positive (Γ := Γ) j
  have later : Γ ⊢[PRAAx] le p j := le_add_right _ _
  have grow := GaussianExponentialReference.unit_monotone later
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 Pi j x) (ap2 Pi p x) two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hj hp) hp (by ipra_le 𝔞(unit p)*sl grow)
      (point_at Pi x j p (GaussianGammaHalfPiName.name_regular x))
  have ca : Γ ⊢[PRAAx] bounded a R one := GaussianPiRationalScale.point_bound false A B R one hB
    (le_refl one) (le_congr (one_mul _).eqSymm (.eqRefl _) hA)
  exact distance_congr (GaussianBoundedConstantProductName.sample_at Pi p R a x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (bound_congr (multiplication_difference a _ _).eqSymm (mul_comm R two) (one_mul (unit p))
      (bounded_product a _ R one two (unit p) (le_refl one) hp ca near))

private theorem sine_error (A B R p N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hN : Γ ⊢[PRAAx] le (cutoff R p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 P p (sineData A B R)) (product A B N) one (unit p) :=
  distance_symmetric _ _ _ _ (unit_positive p)
    (GaussianSineProductName.cofinal_error _ R B p N hB (axis_disk A B R hA) (le_trans (le_add_right _ _) hN))

private theorem product_error (A B R p N x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hN : Γ ⊢[PRAAx] le (cutoff R p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 Hyper p (hd A B R x)) (rawValue (ap2 Pi p x) A B N)
      (productCost A B R x) (unit p) := by
  let a := rationalReal A B
  let y := sineData A B R
  let s := sd A B R x
  let π := ap2 Pi p x
  have hp := unit_positive (Γ := Γ) p
  have hS := GaussianPiRationalScale.regular false A B R x hB hA
  have hP := sine_regular A B R hB hA
  have ca : Γ ⊢[PRAAx] bounded a R one := GaussianPiRationalScale.point_bound false A B R one hB
    (le_refl one) (le_congr (one_mul _).eqSymm (.eqRefl _) hA)
  have cπ := sample_bound (Γ := Γ) Pi x p (GaussianGammaHalfPiName.name_regular x)
  have cA := bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
    (bounded_product a π R one (U Pi x) one (le_refl one) (le_refl one) ca cπ)
  have cP : Γ ⊢[PRAAx] bounded (ap2 P p y) (productBound R) one :=
    bound_congr (GaussianSineProductName.sample_at (axisNumerator A) R B p).eqSymm (.eqRefl _) (.eqRefl _)
      (product_bound A B R (GaussianSineProductName.cutoff R p) hB hA)
  exact distance_triangle_same _ _ _ _ _ _ hp (multiply_sample_error Scale P s y p hS hP)
    (product_distance (ap2 Scale p s) (qmul a π) (ap2 P p y) (product A B N) (two*R) one (unit p)
      (productBound R) (R*U Pi x) hp (scale_error A B R p x hB hA) (sine_error A B R p N hB hA hN) cP cA)

private theorem product_error_right (F G : PR 2) (x y a b p M K : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (e : Γ ⊢[PRAAx] ap2 F p x ≐ a) (ha : Γ ⊢[PRAAx] bounded a M one)
    (hb : Γ ⊢[PRAAx] distanceBounded (ap2 G p y) b K (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF F G) p (multiplyData F G x y)) (qmul a b)
      ((multiplyModulus F G x y+one)+M*K) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have head := distance_congr (.eqRefl _) (qmul_congr e (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error F G x y p hf hg)
  have tail := bound_congr (multiplication_difference a (ap2 G p y) b).eqSymm (.eqRefl _) (one_mul _)
    (bounded_product a _ M one K (unit p) (le_refl one) hp ha hb)
  exact distance_triangle_same _ _ _ _ _ _ hp head tail

private theorem weighted_error (A B C R p N x : PTm n)
    (h : Γ ⊢[PRAAx] source A B C R) (hN : Γ ⊢[PRAAx] le (cutoff R p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 weightedF p (weightedData A B C R x))
      (qmul (step B C) (rawTangent (ap2 Pi p x) A B N)) (weightedCost A B C R x) (unit p) := by
  let a := rationalReal A B
  let b := step B C
  let π := ap2 Pi p x
  let d := dd A B R
  let y := sineData A B R
  let z := linearData A B R
  have hp := unit_positive (Γ := Γ) p
  have hB := h.andE₁
  have hA := le_trans (le_add_right A C) h.andE₂
  have hC := le_trans (le_add_left C A) h.andE₂
  have hπ := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have ca : Γ ⊢[PRAAx] bounded a R one := GaussianPiRationalScale.point_bound false A B R one hB
    (le_refl one) (le_congr (one_mul _).eqSymm (.eqRefl _) hA)
  have cb : Γ ⊢[PRAAx] bounded b R one := GaussianPiRationalScale.point_bound false C B R one hB
    (le_refl one) (le_congr (one_mul _).eqSymm (.eqRefl _) hC)
  have hD := GaussianSineProductImaginaryCofinalDerivative.derivative_regular A B R hB hA
  have hP := sine_regular A B R hB hA
  have hl := linear_regular A B R hB hA
  have hlRaw : Γ ⊢[PRAAx] distanceBounded (ap2 linearF p z) (qmul a (derivative A B N))
      (linearCost A B R) (unit p) :=
    product_error_right constantF D a d a _ p R _ (constant_regular _) hD (constant_at p a) ca
      (GaussianSineProductImaginaryCofinalDerivative.derivative_at_finite A B R p N hB hA hN)
  have hsRaw : Γ ⊢[PRAAx] distanceBounded (ap2 sumF p (sumData A B R))
      (qadd (product A B N) (qmul a (derivative A B N))) (sumCost A B R) (unit p) :=
    distance_triangle_same _ _ _ _ _ _ hp (add_sample_error P linearF y z p hP hl)
      (sum_distance _ _ _ _ _ _ _ hp (sine_error A B R p N hB hA hN) hlRaw)
  have hdRaw : Γ ⊢[PRAAx] distanceBounded (ap2 derivativeF p (derivativeData A B R x))
      (rawTangent π A B N) (derivativeCost A B R x) (unit p) :=
    product_error_right Pi sumF x (sumData A B R) π _ p (U Pi x) _ hπ (sum_regular A B R hB hA)
      (.eqRefl _) (sample_bound Pi x p hπ) hsRaw
  exact product_error_right constantF derivativeF b (derivativeData A B R x) b _ p R _
    (constant_regular _) (derivative_regular A B R x hB hA) (constant_at p b) cb hdRaw

theorem diagonal (A B C R x p : PTm n) (h : Γ ⊢[PRAAx] source A B C R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 incrementF p (incrementData A B C R x))
      (ap2 weightedF p (weightedData A B C R x))
      (diagonalNumerator (coefficient R x*(C*C)) (B*B) (cost A B C R x) p) (diagonalDenominator (B*B) p) := by
  let N := cutoff R p
  let E := B*B
  let Uₚ := unit p
  let K := productCost (A+C) B R x+productCost A B R x
  let J := weightedCost A B C R x
  let L := coefficient R x*(C*C)
  let H := num 6+K
  have hp := unit_positive (Γ := Γ) p
  have hB := h.andE₁
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hB hB
  have hA := le_trans (le_add_right A C) h.andE₂
  have hnext := product_regular (A+C) B R x hB h.andE₂
  have hbase := product_regular A B R x hB hA
  have hN : Γ ⊢[PRAAx] le (cutoff R p) N := le_refl _
  have lhs := distance_triangle_same _ _ _ _ _ _ hp
    (GaussianNamedDifference.sample_error Hyper Hyper (hd (A+C) B R x) (hd A B R x) p hnext hbase)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp
      (product_error (A+C) B R p N x hB h.andE₂ hN) (product_error A B R p N x hB hA hN))
  have raw := GaussianSineProductImaginaryHyperbolicProductRuleAlgebra.finite_rate (ap2 Pi p x) A B C R N (U Pi x)
    hB h.andE₂ (sample_bound Pi x p (GaussianGammaHalfPiName.name_regular x))
  have rhs := distance_symmetric _ _ _ _ hp (weighted_error A B C R p N x h hN)
  have both := GaussianReconstructionRoots.distance_triangle _ _ _ H Uₚ L E hp hE lhs raw
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ (H*E+L*Uₚ) (Uₚ*E) J Uₚ
    (positive_product _ _ hp hE) hp both rhs
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hE) hp)
    (positive_product _ _ hE hp)
    (le_of_eq_add (d := zero) (by dsimp only [diagonalDenominator,diagonalNumerator,cost,E,Uₚ,K,J,L,H]; ipra_ring))
    joined

theorem independent_rate (A B C R x : PTm n) (h : Γ ⊢[PRAAx] source A B C R) :
    Γ ⊢[PRAAx] independentRate incrementF weightedF (incrementData A B C R x) (weightedData A B C R x)
      (coefficient R x*(C*C)) (B*B) := by
  have hA := le_trans (le_add_right A C) h.andE₂
  refine GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (cost A B C R x)
    (positive_product _ _ h.andE₁ h.andE₁)
    (GaussianNamedDifference.name_regular _ _ _ _ (product_regular (A+C) B R x h.andE₁ h.andE₂)
      (product_regular A B R x h.andE₁ hA))
    (multiply_fast _ _ _ _ (constant_regular _) (derivative_regular A B R x h.andE₁ hA)) (.allI ?_)
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s B) (s C) (s R) := by
    simpa only [Fm.shift,Syn.shift,s,GaussianSineProductImaginaryCofinalDerivative.subst_source] using h.shift
  simpa only [diagonalEnvelope,Syn.shift,s,subst_coefficient,subst_cost,subst_incrementData,subst_weightedData,PTm.subst_mul] using
    diagonal (s A) (s B) (s C) (s R) (s x) (var 0) hs

private theorem scaled_base (A B k R : PTm n) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] le (k*A) (R*(k*B)) :=
  le_congr (mul_comm _ _) (by ipra_ring) (mul_le_mul_right k hA)

theorem product_rescale (A B k R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent Hyper Hyper (hd (k*A) (k*B) R x) (hd A B R x) := by
  have he := GaussianSineProductImaginaryScaling.cofinal_rescale A B k R hB hk hA
  have hs := scaled_base A B k R hA
  have hb := positive_product _ _ hk hB
  exact multiply_cross Scale Scale P P _ _ _ _
    (GaussianPiRationalScale.regular false (k*A) (k*B) R x hb hs) (GaussianPiRationalScale.regular false A B R x hB hA)
    (sine_regular (k*A) (k*B) R hb hs) (sine_regular A B R hB hA)
    (GaussianPiRationalScaleRepresentation.rescale false A B k R x hB hk hA) he.andE₁

theorem derivative_rescale (A B k R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent derivativeF derivativeF (derivativeData (k*A) (k*B) R x) (derivativeData A B R x) := by
  let W := GaussianSineProductImaginaryLogDerivativeTail.nameF
  let wd (a b r : PTm n) := GaussianSineProductImaginaryLogDerivativeTail.data a b r
  have hs := scaled_base A B k R hA
  have hb := positive_product _ _ hk hB
  have he := GaussianSineProductImaginaryScaling.cofinal_rescale A B k R hB hk hA
  have p₁ := sine_regular (k*A) (k*B) R hb hs
  have p₀ := sine_regular A B R hB hA
  have de : Γ ⊢[PRAAx] crossEquivalent D D (dd (k*A) (k*B) R) (dd A B R) :=
    multiply_cross P P W W _ _ (wd (k*A) (k*B) R) (wd A B R) p₁ p₀
      (GaussianSineProductImaginaryLogDerivativeTail.regular (k*A) (k*B) R hb hs)
      (GaussianSineProductImaginaryLogDerivativeTail.regular A B R hB hA) he.andE₁ he.andE₂
  have ae := GaussianSineProductImaginaryScaling.rational_real_rescale A B k hB hk
  have lin : Γ ⊢[PRAAx] crossEquivalent linearF linearF (linearData (k*A) (k*B) R) (linearData A B R) :=
    multiply_cross constantF constantF D D _ _ _ _ (constant_regular _) (constant_regular _)
      (GaussianSineProductImaginaryCofinalDerivative.derivative_regular (k*A) (k*B) R hb hs)
      (GaussianSineProductImaginaryCofinalDerivative.derivative_regular A B R hB hA)
      (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ ae) de
  have sumEq : Γ ⊢[PRAAx] crossEquivalent sumF sumF (sumData (k*A) (k*B) R) (sumData A B R) :=
    GaussianNamedGammaHalfShift.add_cross P P linearF linearF _ _ _ _ p₁ p₀
      (linear_regular (k*A) (k*B) R hb hs) (linear_regular A B R hB hA) he.andE₁ lin
  have hPi := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  exact multiply_cross Pi Pi sumF sumF x x _ _ hPi hPi
    (sum_regular (k*A) (k*B) R hb hs) (sum_regular A B R hB hA)
    (cross_refl Pi x hPi) sumEq

theorem scaled_unit_rate (A B k R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hNext : Γ ⊢[PRAAx] le (k*A+one) (R*(k*B))) :
    Γ ⊢[PRAAx] independentRate incrementF weightedF (df (hd (k*A+one) (k*B) R x) (hd A B R x))
      (multiplyData constantF derivativeF (rationalReal one (k*B)) (derivativeData A B R x))
      (coefficient R x) ((k*B)*(k*B)) := by
  let a := k*A
  let b := k*B
  let t := rationalReal one b
  let y := hd (a+one) b R x
  let z := hd a b R x
  let u := hd A B R x
  have hb : Γ ⊢[PRAAx] le one b := positive_product _ _ hk hB
  have ha : Γ ⊢[PRAAx] le a (R*b) := scaled_base A B k R hA
  have rd := independent_rate a b one R x (.andI hb hNext)
  have p₁ := product_regular (a+one) b R x hb hNext
  have p₀ := product_regular a b R x hb ha
  have p := product_regular A B R x hB hA
  have pe := product_rescale A B k R x hB hk hA
  have de := derivative_rescale A B k R x hB hk hA
  have left : Γ ⊢[PRAAx] crossEquivalent incrementF incrementF (df y u) (df y z) :=
    GaussianNamedDifferenceQuotientProperness.difference_proper _ _ _ _ _ _ _ _ p₁ p₁ p p₀
      (cross_refl Hyper y p₁) (cross_symm _ _ _ _ pe)
  have right : Γ ⊢[PRAAx] crossEquivalent weightedF weightedF
      (multiplyData constantF derivativeF t (derivativeData A B R x)) (weightedData a b one R x) :=
    multiply_cross constantF constantF derivativeF derivativeF _ _ _ _ (constant_regular _) (constant_regular _)
      (derivative_regular A B R x hB hA) (derivative_regular a b R x hb ha)
      (cross_refl constantF t (constant_regular _)) (cross_symm _ _ _ _ de)
  apply GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (positive_product _ _ hb hb) _ left right
  exact GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _ (by ipra_ring) rd

theorem actual_scaled_unit_hyperbolic_product_derivative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let A := var 0
       let B := var 1
       let k := var 2
       let R := var 3
       let x := var 4
       (le one B ⋏ (le one k ⋏ (le A (R*B) ⋏ le (k*A+one) (R*(k*B))))) ⟶
       independentRate incrementF weightedF (df (hd (k*A+one) (k*B) R x) (hd A B R x))
         (multiplyData constantF derivativeF (rationalReal one (k*B)) (derivativeData A B R x))
         (coefficient R x) ((k*B)*(k*B))) :=
  closeUniv 5 (.impI (scaled_unit_rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryHyperbolicProductRule
