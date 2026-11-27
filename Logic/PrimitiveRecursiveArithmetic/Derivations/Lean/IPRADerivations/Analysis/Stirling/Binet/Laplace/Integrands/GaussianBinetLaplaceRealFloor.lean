import IPRADerivations.Analysis.Stirling.Binet.Laplace.Integrands.GaussianBinetLaplaceDomination
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineDampedAxis
import IPRADerivations.Analysis.Euler.Integration.Decay.CompactBounds.GaussianEulerDecayCompactLower

/-!
# Positive lower bound for the original real Binet integrand on a compact interval

The original normalized product is uniformly within its dyadic observation
allowance of a product of a positive reciprocal-exponential observation
and the actual cofinal kernel observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceRealFloor

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetKernelRows (inputData lowerDenominator)
open GaussianBinetLaplaceDomination (complexClock clock_later kernel_observation_bound)
open GaussianBinetLaplaceIntegrand (cofinalF cofinalData input product_at)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianPositiveRealArithmetic (positive positive_congr)
open GaussianRationalDistanceOrder
  (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "ExpF" => GaussianBinetLaplaceExponential.nameF
local notation "expData" => GaussianBinetLaplaceExponential.data
local notation "K" => GaussianBinetKernelCofinal.nameF
local notation "invF" => GaussianNameReciprocal.nameF GaussianPositiveRationalExponentialDecay.expF
local notation "invData" => GaussianPositiveRationalExponentialDecay.inverseData
local notation "expFloor" => GaussianEuclideanDistanceName.fraction
local notation "kernelFloor" => GaussianPositiveRationalLogarithm.fraction

def floorDenominator (X T : PTm n) : PTm n :=
  pw (num 3) (X*T)*lowerDenominator T zero

/-- The scalar value `3^(-X*T) * 2/(T^2+100)`. -/
def floor (X T : PTm n) : PTm n :=
  expFloor two (floorDenominator X T)

ipra_subst floorDenominator

ipra_subst floor

theorem floor_denominator_positive (X T : PTm n) : Γ ⊢[PRAAx] le one (floorDenominator X T) :=
  positive_product _ _ (GaussianPolynomialPerturbation.power_positive (num 3) (X*T) (by ipra_le 2))
    (GaussianBinetKernelRows.lower_denominator_positive T zero)

theorem cofinal_kernel_floor (p A B T : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hT : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] positive (ap2 K p (inputData A B)) ⋏
      rationalLE (fstT (kernelFloor two (lowerDenominator T zero))) (fstT (ap2 K p (inputData A B))) := by
  have e := GaussianBinetKernelCofinal.sample_at (Γ := Γ) p A B
  have h := GaussianBinetKernelPositive.named_finite_at (succ p) (unit p) A B T hB (unit_positive p) hT
  exact .andI (positive_congr e.eqSymm h.andE₁)
    (rationalLE_congr (.eqRefl _) (congrFst e).eqSymm h.andE₂)

private theorem kernel_radius_two (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 K p (inputData A B)) two one := by
  have hU := unit_positive (Γ := Γ) p
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (by ipra_le 11) hU) (le_refl one) ?_
    (kernel_observation_bound p A B hB)
  ipra_le 12*sl hU+11*𝔞(unit p)

private theorem decay_to_reciprocal (p X D R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 ExpF p (expData X zero D zero R T A B))
      (ap2 invF p (invData (X*A) (D*B) zero)) (num 4) (unit p) := by
  let U := unit p
  let v := GaussianEulerDecayMesh.observation (X*A) (D*B) p
  let e := ap2 ExpF p (expData X zero D zero R T A B)
  let d := ap2 invF p (invData (X*A) (D*B) zero)
  have hU := unit_positive (Γ := Γ) p
  have hUU := positive_product _ _ hU hU
  have hb := positive_product _ _ h.andE₁.andE₁.andE₂ h.andE₂.andE₁
  have ev : Γ ⊢[PRAAx] distanceBounded e v two U :=
    distance_radius_mono _ _ _ _ _ _ hUU hU (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianBinetSineDampedAxis.same_observation p p X D A B R T h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)
  have dv : Γ ⊢[PRAAx] distanceBounded d v two U :=
    distance_radius_mono _ _ _ _ _ _ hUU hU (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianNameEquivalence.cross_at invF decayF _ _ p p
        (GaussianEulerDecayFactorBounds.original_decay_matches_reciprocal (X*A) (D*B) zero hb))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same e v d two two U hU ev (distance_symmetric _ _ _ _ hU dv))

private theorem floor_product (p X D T A B S : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B))
    (hCap : Γ ⊢[PRAAx] le X (S*D)) :
    Γ ⊢[PRAAx] rationalLE (floor S T)
      (fstT (qmul (ap2 invF p (invData (X*A) (D*B) zero)) (ap2 K p (inputData A B)))) := by
  let d := ap2 invF p (invData (X*A) (D*B) zero)
  let k := ap2 K p (inputData A B)
  let W := pw (num 3) (S*T)
  let v := expFloor one W
  let u := fstT (kernelFloor two (lowerDenominator T zero))
  have hW := GaussianPolynomialPerturbation.power_positive (Γ := Γ) (num 3) (S*T) (by ipra_le 2)
  have hvRep := GaussianEuclideanDistanceName.fraction_represents one W hW
  have hv := GaussianRationalL1.nonnegative_of_representation v one W hW hvRep
  have huRep := GaussianGammaHalfSqrtBrackets.fraction_first_represents two (lowerDenominator T zero)
    (GaussianBinetKernelRows.lower_denominator_positive (Γ := Γ) T zero)
  have hDen := floor_denominator_positive (Γ := Γ) S T
  have mulFloor : Γ ⊢[PRAAx] RationalArithmetic.multiply v u ≐ floor S T := by
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (RationalArithmetic.multiply_guard v u)
      (RationalNormalForm.normalize_well_formed _ _ hDen)
      (RationalRepresentations.represents_multiply _ _ _ _ _ _ hvRep huRep)
      (GaussianEuclideanDistanceName.fraction_represents two _ hDen) hDen hDen
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,floorDenominator,W,Q.mk_mul,map_mul]
    ipra_simps
    ring
  have arg : Γ ⊢[PRAAx] le (X*A) ((S*T)*(D*B)) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono hCap hT)
  have hd := GaussianEulerDecayCompactLower.reciprocal_samples_lower (X*A) (D*B) (S*T) p
    (positive_product _ _ hD hB) arg
  have hk := cofinal_kernel_floor p A B T hB hT
  have h₁ := RationalArithmetic.multiply_monotone v u (fstT k) hv hk.andE₂
  have h₂ := RationalArithmetic.multiply_monotone (fstT k) v (fstT d) hk.andE₁.andE₂ hd
  have h₃ := RationalArgmin.transitive h₁
    (rationalLE_congr (RationalAlgebra.multiply_commutative _ _) (RationalAlgebra.multiply_commutative _ _) h₂)
  exact rationalLE_congr mulFloor (GaussianPositiveExponentialProduct.real_product d k hk.andE₁.andE₁).eqSymm h₃

/-- The floor depends on a common cap for the input value, independently
of its rational denominator. It holds at every actual observation clock. -/
theorem sample_floor_with_cap (p X D R T A B S : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) (hCap : Γ ⊢[PRAAx] le X (S*D)) :
    Γ ⊢[PRAAx] upper (floor S T)
      (fstT (ap2 cofinalF p (cofinalData X zero D zero R T A B))) (num 8) (unit p) := by
  let r := complexClock p X zero D zero R T A B
  let x := expData X zero D zero R T A B
  let y := inputData A B
  let e := ap2 ExpF r x
  let k := ap2 K r y
  let d := ap2 invF r (invData (X*A) (D*B) zero)
  let out := ap2 cofinalF p (cofinalData X zero D zero R T A B)
  have hp := unit_positive (Γ := Γ) p
  have hr := unit_positive (Γ := Γ) r
  have hpR : Γ ⊢[PRAAx] le (unit p) (unit r) :=
    GaussianFactorBudget.power_monotone_length two p r (by ipra_le 1) (clock_later p X zero D zero R T A B)
  have read : Γ ⊢[PRAAx] out ≐ qmul e k := product_at K p x y
  have near := GaussianApproximateInverseDistance.multiply_distance k e d two (num 4) (unit r) hr
    (kernel_radius_two r A B h.andE₂.andE₁) (decay_to_reciprocal r X D R T A B h)
  have ordered : Γ ⊢[PRAAx] distanceBounded (qmul d k) out (num 8) (unit r) :=
    distance_congr (GaussianRationalPowerAlgebra.qmul_commutative k d)
      ((GaussianRationalPowerAlgebra.qmul_commutative k e).eqTrans read.eqSymm)
      (by ipra_ring) (.eqRefl _) (distance_symmetric _ _ _ _ hr near)
  have rad := distance_radius_mono _ _ _ _ _ _ hr hp (le_mul_mono (le_refl _) hpR) ordered
  have row := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hp rad)
  exact RationalValueBounds.upper_order_left _ _ _ _ _
    (floor_product r X D T A B S h.andE₁.andE₁.andE₂ h.andE₂.andE₁ h.andE₂.andE₂ hCap) row

theorem numerator_cap (X D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] le X (X*D) :=
  le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl X) hD)

/-- The original numerator provides a cap when no separate one is supplied. -/
theorem sample_floor (p X D R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) :
    Γ ⊢[PRAAx] upper (floor X T)
      (fstT (ap2 cofinalF p (cofinalData X zero D zero R T A B))) (num 8) (unit p) :=
  sample_floor_with_cap p X D R T A B X h (numerator_cap X D h.andE₁.andE₁.andE₂)

theorem actual_positive_real_Binet_integrand_floor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 1) zero (var 2) zero (var 3) (var 4) (var 5) (var 6) ⟶
      upper (floor (var 1) (var 4))
        (fstT (ap2 cofinalF (var 0) (cofinalData (var 1) zero (var 2) zero (var 3) (var 4) (var 5) (var 6))))
        (num 8) (unit (var 0))) :=
  closeUniv 7 (.impI (sample_floor _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceRealFloor
