import IPRADerivations.Analysis.Beta.Endpoints.Upper.GaussianBetaUpperEndpointInverse

/-!
# Original sampled grid endpoint and the actual finite Euler inverse

The original beta grid endpoint keeps its actual compact-product power
clock. Its exact N-scaled sample is the raw product defining the checked
upper endpoint name. Actual multiplication normalization and the proved
upper endpoint inverse give an independent-query error with a computed
dyadic factor. A computed enlargement of the ORIGINAL grid precision
spends that factor and returns the standard 2^-t+2^-q error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaUpperGridEndpoint

open_ipra
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_radius_scale distance_triangle_same)
open GaussianRationalNaturalScale (naturalPoint natScale_as_product natScale_product)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianBetaPrimitiveLinearStep (sample)
open GaussianBetaUpperEndpointName (nameF data endpointConstant)
open GaussianBetaUpperEndpointInverse (source)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gridClock (p z B b N : PTm n) : PTm n := GaussianEulerCompactProductComparison.clock p z B (b*N) b
def scaledEndpoint (p z B b N : PTm n) : PTm n := qmul (naturalPoint N) (sample (gridClock p z B b N) z B (b*N) b N)
def factor (z B b N : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyModulus powerF constantF (powerData z B (b*N) b) (endpointConstant z B b N)+two
def precision (t z B b N : PTm n) : PTm n := GaussianFastValueCut.exponent (factor z B b N) t
def numerator (p q z B b N : PTm n) : PTm n := factor z B b N*unit q+unit p
ipra_subst gridClock
ipra_subst scaledEndpoint [sample, GaussianEulerPowerIncrement.point, GaussianTimeWeightedPolynomialIncrement.value, GaussianBetaPrimitiveLinearStep.argument]
ipra_subst factor
ipra_subst precision
ipra_subst numerator

theorem original_grid_endpoint_raw_product (p z B b N : PTm n) : Γ ⊢[PRAAx]
    scaledEndpoint p z B b N ≐ qmul (ap2 powerF (gridClock p z B b N) (powerData z B (b*N) b)) (endpointConstant z B b N) :=
  (natScale_as_product _ _).eqSymm.eqTrans (natScale_product _ _ _).eqSymm

theorem original_clock_later (p z B b N : PTm n) : Γ ⊢[PRAAx] le p (gridClock p z B b N) :=
  GaussianEulerCompactProductComparison.clock_later _ _ _ _ _

/-- Compare the literal scaled endpoint sample with an independently queried
name known to be cross-equivalent to the upper endpoint. -/
theorem sampled_endpoint_error_of_cross (p q z B b N : PTm n) (g : PR 2) (x : PTm n)
    (power : Γ ⊢[PRAAx] pointCN powerF (powerData z B (b*N) b))
    (cross : Γ ⊢[PRAAx] crossEquivalent nameF g (data z B b N) x) :
    Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N) (ap2 g q x)
      (numerator p q z B b N) (unit p*unit q) := by
  let k := gridClock p z B b N
  let C := endpointConstant z B b N
  let P := powerData z B (b*N) b
  let L := GaussianNameArithmetic.multiplyModulus powerF constantF P C
  let K := unit k
  let U := unit p
  let V := unit q
  have hk := unit_positive (Γ := Γ) k
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hKV := positive_product _ _ hk hq
  have hUV := positive_product _ _ hp hq
  have product : Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N) (ap2 nameF k (data z B b N)) (L+one) K :=
    distance_symmetric _ _ _ _ hk
      (distance_congr (.eqRefl _) ((qmul_congr (.eqRefl _) (constant_at k C)).eqTrans (original_grid_endpoint_raw_product p z B b N).eqSymm)
        (.eqRefl _) (.eqRefl _) (GaussianNameRingLaws.multiply_sample_error powerF constantF P C k power (constant_regular C)))
  have first : Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N) (ap2 nameF k (data z B b N)) ((L+one)*V) (K*V) :=
    distance_radius_scale hk hq product
  have second := GaussianNameEquivalence.cross_at _ _ _ _ k q cross
  have both : Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N) (ap2 g q x)
      (factor z B b N*V+K) (K*V) :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (by unfold factor; dsimp only [L,P,C]; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hKV first second)
  have order : Γ ⊢[PRAAx] le U K := GaussianExponentialReference.unit_monotone (original_clock_later p z B b N)
  have comparison : Γ ⊢[PRAAx] le ((factor z B b N*V+K)*(U*V)) ((factor z B b N*V+U)*(K*V)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (K*U*V) (mul_le_mul_right (factor z B b N*V*V) order))
  exact distance_radius_mono _ _ _ _ _ _ hKV hUV comparison both

theorem sampled_endpoint_error (p q z R B A b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A b N) : Γ ⊢[PRAAx]
    distanceBounded (scaledEndpoint p z B b N) (ap2 eulerF q (eulerData z R B A N))
      (numerator p q z B b N) (unit p*unit q) :=
  sampled_endpoint_error_of_cross p q z B b N eulerF (eulerData z R B A N)
    (GaussianEulerIntegrandName.power_regular z B (b*N) b
      (GaussianBetaUpperEndpointName.power_source z B b N h.andE₁.andE₂.andE₁.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁))
    (GaussianBetaUpperEndpointInverse.original_upper_inverse z R B A b N h.andE₁ h.andE₂.andE₁
      h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂)

theorem precision_budget (t z B b N : PTm n) : Γ ⊢[PRAAx] le (factor z B b N*unit t) (unit (precision t z B b N)) :=
  GaussianFastValueCut.query_budget _ _

/-- The original endpoint precision budget absorbs its exact sample error
factor at any sufficiently late query. -/
theorem retime_endpoint_error (t p q z B b N y : PTm n)
    (hp : Γ ⊢[PRAAx] le (precision t z B b N) p)
    (h : Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N) y (numerator p q z B b N) (unit p*unit q)) :
    Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N) y (unit t+unit q) (unit t*unit q) := by
  let U := unit p
  let V := unit q
  let T := unit t
  have budget : Γ ⊢[PRAAx] le (factor z B b N*T) U :=
    le_trans (precision_budget t z B b N) (GaussianExponentialReference.unit_monotone hp)
  have comparison : Γ ⊢[PRAAx] le (numerator p q z B b N*(T*V)) ((T+V)*(U*V)) :=
    le_congr (by unfold numerator; ipra_ring) (by ipra_ring)
      (add_le_add_right (U*T*V) (mul_le_mul_right (V*V) budget))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
    (positive_product _ _ (unit_positive t) (unit_positive q)) comparison h

theorem retimed_endpoint_error (t q z R B A b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A b N) : Γ ⊢[PRAAx]
    distanceBounded (scaledEndpoint (precision t z B b N) z B b N) (ap2 eulerF q (eulerData z R B A N))
      (unit t+unit q) (unit t*unit q) :=
  retime_endpoint_error t _ q z B b N _ (le_refl _) (sampled_endpoint_error _ q z R B A b N h)

theorem original_grid_upper_endpoint_independent_Euler_inverse_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        distanceBounded (scaledEndpoint (var 0) (var 2) (var 4) (var 6) (var 7))
          (ap2 eulerF (var 1) (eulerData (var 2) (var 3) (var 4) (var 5) (var 7)))
          (numerator (var 0) (var 1) (var 2) (var 4) (var 6) (var 7)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (sampled_endpoint_error _ _ _ _ _ _ _ _ Prf.hyp0))

theorem original_retimed_grid_upper_endpoint_standard_Euler_inverse_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        distanceBounded
          (scaledEndpoint (precision (var 0) (var 2) (var 4) (var 6) (var 7)) (var 2) (var 4) (var 6) (var 7))
          (ap2 eulerF (var 1) (eulerData (var 2) (var 3) (var 4) (var 5) (var 7)))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (retimed_endpoint_error _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaUpperGridEndpoint
