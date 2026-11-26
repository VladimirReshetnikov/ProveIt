import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentCompact
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerWeightedHalfDecay
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineDampedAxis

/-!
# Inverse-square domination for the actual weighted Binet observations

The original exponential observation is compared to the reciprocal of
the positive exponential at the monomial cutoff of order j+2. The
power j is the literal time weight of the weighted Binet evaluator.
The remaining inverse square gives a tail majorant independent of the
upper horizon, while the observation allowance remains dyadic.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentDecay

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianBinetKernelRows (inputData)
open GaussianBinetLaplaceDomination (complexClock clock_later)
open GaussianBinetLaplaceIntegrand (input product_at)
open GaussianBinetLaplaceMomentCompact (weight_bound)
open GaussianBinetLaplaceMomentFloor (weight clock observation)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded radius_power)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianEulerWeightedHalfDecay (radius_reciprocal)
open GaussianPositiveRationalExponentialDecay (expF expData inverseData exact_reciprocal_weighted_decay)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "ExpF" => GaussianBinetLaplaceExponential.nameF
local notation "lapData" => GaussianBinetLaplaceExponential.data
local notation "K" => GaussianBinetKernelCofinal.nameF
local notation "invF" => GaussianNameReciprocal.nameF expF

def tailScale (j D : PTm n) : PTm n := fact (j+two)*pw D (j+two)

ipra_subst tailScale [fact, two, one]

private theorem reciprocal_bound (p a b k : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (ap2 invF p (inverseData a b k)) (fact k*pw b k) (pw a k) := by
  let y := ap2 invF p (inverseData a b k)
  let A := pw a k
  let B := pw b k
  let w := radiusPoint A B
  let v := radiusPoint B A
  have hA := GaussianPolynomialPerturbation.power_positive a k ha
  have hB := GaussianPolynomialPerturbation.power_positive b k hb
  have base : Γ ⊢[PRAAx] bounded (qmul w y) (fact k) one :=
    bound_congr (qmul_congr (radius_power a b k hb) (.eqRefl y)) (.eqRefl _) (.eqRefl _)
      (exact_reciprocal_weighted_decay a b k p ha hb)
  have hcan := GaussianNameReciprocal.name_canonical (Γ := Γ) expF zero (expData a b k) p
  have same : Γ ⊢[PRAAx] qmul (qmul w y) v ≐ y :=
    (qmul_commutative (qmul w y) v).eqTrans
      ((qmul_associative v w y).eqSymm.eqTrans
        ((qmul_congr (radius_reciprocal A B hA hB) (.eqRefl y)).eqTrans
          (GaussianPolynomialDeterminantTerms.one_mul_canonical y hcan)))
  exact bound_congr same (.eqRefl _) (one_mul _)
    (bounded_product (qmul w y) v (fact k) one B A (le_refl one) hA base (radius_bounded B A hA))

private theorem power_plus_two (A j : PTm n) : Γ ⊢[PRAAx] pw A (j+two) ≐ pw A j*(A*A) :=
  (pw_add A j two).eqTrans (congrMul (.eqRefl _) ((pw_succ A one).eqTrans (congrMul (pw_one A) (.eqRefl _))))

private theorem leading_budget (j X D A B : PTm n) (hX : Γ ⊢[PRAAx] le one X) :
    let k := j+two
    Γ ⊢[PRAAx] le
      (((fact k*pw (D*B) k)*pw A j)*(A*A))
      ((tailScale j D*(B*B))*(pw (X*A) k*pw B j)) := by
  let k := j+two
  have a := natEq (power_plus_two (Γ := Γ) A j)
  have b := natEq (power_plus_two (Γ := Γ) B j)
  have da := natEq (pw_mul_base (Γ := Γ) X A k)
  have db := natEq (pw_mul_base (Γ := Γ) D B k)
  have hx := GaussianPolynomialPerturbation.power_positive X k hX
  change Γ ⊢[PRAAx] le (((fact k*pw (D*B) k)*pw A j)*(A*A)) _
  apply le_of_eq_add (d := fact k*pw D k*pw A j*(A*A)*pw B j*(B*B)*LeanProofs.IPRA.PTm.monus (pw X k) one)
  have h := natEq (eq_add_of_le hx)
  apply deriveNat
  dsimp only [tailScale]
  ipra_simps
  rw [da,db,a,b]
  linear_combination (𝔞(fact k)*𝔞(pw D k)*𝔞(pw A j)*𝔞(A)*𝔞(A)*𝔞(pw B j)*𝔞(B)*𝔞(B))*h

private theorem weighted_reciprocal_bound (p j X D A B : PTm n) (hX : Γ ⊢[PRAAx] le one X)
    (hD : Γ ⊢[PRAAx] le one D) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded
      (qmul (ap2 invF p (inverseData (X*A) (D*B) (j+two))) (weight j A B))
      (tailScale j D*(B*B)) (A*A) := by
  let k := j+two
  let a := X*A
  let b := D*B
  have ha : Γ ⊢[PRAAx] le one a := positive_product _ _ hX hA
  have hb : Γ ⊢[PRAAx] le one b := positive_product _ _ hD hB
  have hpA := GaussianPolynomialPerturbation.power_positive a k ha
  have hpB := GaussianPolynomialPerturbation.power_positive B j hB
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hpA hpB) (positive_product _ _ hA hA)
    (leading_budget j X D A B hX)
  exact bounded_product _ _ _ _ _ _ hpA hpB (reciprocal_bound p a b k ha hb) (radius_bounded _ _ hpB)

private theorem exponential_near_reciprocal (p j X D R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 ExpF p (lapData X zero D zero R T A B))
      (ap2 invF p (inverseData (X*A) (D*B) j)) (num 4) (unit p) := by
  let V := unit p
  let v := GaussianEulerDecayMesh.observation (X*A) (D*B) p
  let e := ap2 ExpF p (lapData X zero D zero R T A B)
  let d := ap2 invF p (inverseData (X*A) (D*B) j)
  have hV := unit_positive (Γ := Γ) p
  have hVV := positive_product _ _ hV hV
  have hb := positive_product _ _ h.andE₁.andE₁.andE₂ h.andE₂.andE₁
  have ev : Γ ⊢[PRAAx] distanceBounded e v two V :=
    distance_radius_mono _ _ _ _ _ _ hVV hV (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianBinetSineDampedAxis.same_observation p p X D A B R T h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)
  have dv : Γ ⊢[PRAAx] distanceBounded d v two V :=
    distance_radius_mono _ _ _ _ _ _ hVV hV (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianNameEquivalence.cross_at invF decayF _ _ p p
        (GaussianEulerDecayFactorBounds.original_decay_matches_reciprocal (X*A) (D*B) j hb))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same e v d two two V hV ev (distance_symmetric _ _ _ _ hV dv))

theorem observation_inverse_square_bound (p j X D R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] bounded (observation p j X D R T A B)
      (num 4*(A*A)+(tailScale j D*(B*B))*unit p) (unit p*(A*A)) := by
  let r := clock p j T
  let s := complexClock r X zero D zero R T A B
  let x := lapData X zero D zero R T A B
  let k := ap2 K s (inputData A B)
  let e := ap2 ExpF s x
  let y := ap2 invF s (inverseData (X*A) (D*B) (j+two))
  let w := weight j A B
  let z := observation p j X D R T A B
  let z' := qmul (qmul y k) w
  have hs := unit_positive (Γ := Γ) s
  have hp := unit_positive (Γ := Γ) p
  have hB := h.andE₂.andE₁
  have read : Γ ⊢[PRAAx] z ≐ qmul (qmul e k) w :=
    qmul_congr (product_at K r x (inputData A B)) (.eqRefl _)
  have kBound := bounded_radius_mono k one (num 4) one one (by ipra_le 3) (le_refl one) (by ipra_le 3)
    (GaussianBinetKernelCoarseBound.cofinal_at s A B hB)
  have swap (v : PTm n) : Γ ⊢[PRAAx] qmul k v ≐ qmul v k := qmul_commutative _ _
  have nearE := exponential_near_reciprocal s (j+two) X D R T A B h
  have nearK : Γ ⊢[PRAAx] distanceBounded (qmul e k) (qmul y k) (num 4) (unit s) :=
    distance_congr (swap e) (swap y) (one_mul _) (.eqRefl _)
      (multiply_distance k e y one (num 4) (unit s) hs kBound nearE)
  have near := multiply_distance w (qmul e k) (qmul y k) (pw T j) (num 4) (unit s) hs
    (weight_bound j A B T hB h.andE₂.andE₂) nearK
  have retime : Γ ⊢[PRAAx] le (pw T j*unit p) (unit s) :=
    le_trans (GaussianFastValueCut.query_budget _ _)
      (GaussianExponentialReference.unit_monotone (clock_later r X zero D zero R T A B))
  have ds : Γ ⊢[PRAAx] distanceBounded z z' (num 4) (unit p) :=
    distance_radius_mono _ _ _ _ _ _ hs hp
      (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (num 4)) retime))
      (distance_congr ((qmul_commutative w (qmul e k)).eqTrans read.eqSymm)
        (qmul_commutative w (qmul y k)) (.eqRefl _) (.eqRefl _) near)
  have b := weighted_reciprocal_bound s j X D A B h.andE₁.andE₁.andE₁.andE₁ h.andE₁.andE₁.andE₂ hA hB
  have hAA := positive_product _ _ hA hA
  have ek : Γ ⊢[PRAAx] qmul (qmul y w) k ≐ z' :=
    (qmul_associative y w k).eqTrans ((qmul_congr (.eqRefl _) (qmul_commutative w k)).eqTrans
      (qmul_associative y k w).eqSymm)
  have ref : Γ ⊢[PRAAx] bounded z' (tailScale j D*(B*B)) (A*A) :=
    bound_congr ek (by ipra_ring) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ hAA (le_refl one) b kBound)
  exact GaussianReconstructionRoots.norm_from_distance z z' _ _ _ _ hp hAA ds ref

theorem actual_weighted_Binet_inverse_square_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 2) zero (var 3) zero (var 4) (var 5) (var 6) (var 7) ⟶ le one (var 6) ⟶
      bounded (observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (num 4*(var 6*var 6)+(tailScale (var 1) (var 3)*(var 7*var 7))*unit (var 0))
        (unit (var 0)*(var 6*var 6))) :=
  closeUniv 8 (.impI (.impI (observation_inverse_square_bound _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentDecay
