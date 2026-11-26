import IPRADerivations.Analysis.Beta.Endpoints.GaussianBetaAllDegreeEulerInverse
import IPRADerivations.Analysis.Beta.Endpoints.GaussianBetaUpperGridEndpoint

/-!
# Original upper grid comparison at every positive beta degree

The exact original scaled grid endpoint, its factor and its precision
are retained. The finite Euler reciprocal uses the same original producer
with the all-degree certificate computed from the actual beta endpoint.
The numerical error is unchanged, with independent observation precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeUpperEndpoint

open_ipra
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianBetaUpperEndpointName (endpointConstant)
open GaussianBetaUpperGridEndpoint (gridClock scaledEndpoint factor precision numerator original_grid_endpoint_raw_product original_clock_later precision_budget)
open GaussianBetaAllDegreeEulerInverse (nameF data)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A b N : PTm n) : Fm PTm n :=
  GaussianBetaAllDegreeEulerInverse.source z R B A N ⋏ le one b

theorem sampled_endpoint_error (p q z R B A b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A b N) : Γ ⊢[PRAAx]
    distanceBounded (scaledEndpoint p z B b N) (ap2 nameF q (data z B N))
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
  have power := GaussianEulerIntegrandName.power_regular z B (b*N) b
    (GaussianBetaUpperEndpointName.power_source z B b N h.andE₁.andE₁.andE₂.andE₁.andE₁ h.andE₂ h.andE₁.andE₂)
  have product : Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N) (ap2 GaussianBetaUpperEndpointName.nameF k (GaussianBetaUpperEndpointName.data z B b N)) (L+one) K :=
    distance_symmetric _ _ _ _ hk
      (distance_congr (.eqRefl _) ((qmul_congr (.eqRefl _) (constant_at k C)).eqTrans (original_grid_endpoint_raw_product p z B b N).eqSymm)
        (.eqRefl _) (.eqRefl _) (GaussianNameRingLaws.multiply_sample_error powerF constantF P C k power (constant_regular C)))
  have first : Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N) (ap2 GaussianBetaUpperEndpointName.nameF k (GaussianBetaUpperEndpointName.data z B b N)) ((L+one)*V) (K*V) :=
    distance_radius_mono _ _ _ _ _ _ hk hKV (le_of_eq_add (d := zero) (by ipra_ring)) product
  have cross := GaussianBetaAllDegreeEulerInverse.original_upper_inverse z R B A b N h.andE₁ h.andE₂
  have second := GaussianNameEquivalence.cross_at _ _ _ _ k q cross
  have both : Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N) (ap2 nameF q (data z B N))
      (factor z B b N*V+K) (K*V) :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (by unfold factor; dsimp only [L,P,C]; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hKV first second)
  have order : Γ ⊢[PRAAx] le U K := GaussianExponentialReference.unit_monotone (original_clock_later p z B b N)
  have comparison : Γ ⊢[PRAAx] le ((factor z B b N*V+K)*(U*V)) ((factor z B b N*V+U)*(K*V)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (K*U*V) (mul_le_mul_right (factor z B b N*V*V) order))
  exact distance_radius_mono _ _ _ _ _ _ hKV hUV comparison both

theorem upper_error_at (t p q z R B A b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A b N)
    (hp : Γ ⊢[PRAAx] le (precision t z B b N) p) :
    Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N)
      (ap2 nameF q (data z B N)) (unit t+unit q) (unit t*unit q) := by
  let U := unit p
  let Q := unit q
  let T := unit t
  let F := factor z B b N
  have budget : Γ ⊢[PRAAx] le (F*T) U :=
    le_trans (precision_budget t z B b N) (GaussianExponentialReference.unit_monotone hp)
  have leRate : Γ ⊢[PRAAx] le ((numerator p q z B b N)*(T*Q))
      ((T+Q)*(U*Q)) :=
    le_congr (by unfold numerator; ipra_ring) (by ipra_ring)
      (add_le_add_right (U*T*Q) (mul_le_mul_right (Q*Q) budget))
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (positive_product _ _ (unit_positive t) (unit_positive q)) leRate
    (sampled_endpoint_error p q z R B A b N h)

theorem retimed_endpoint_error (t q z R B A b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A b N) :
    Γ ⊢[PRAAx] distanceBounded (scaledEndpoint (precision t z B b N) z B b N)
      (ap2 nameF q (data z B N)) (unit t+unit q) (unit t*unit q) :=
  upper_error_at t _ q z R B A b N h (le_refl _)

theorem all_degree_original_grid_upper_endpoint_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        distanceBounded (scaledEndpoint (var 0) (var 2) (var 4) (var 6) (var 7))
          (ap2 nameF (var 1) (data (var 2) (var 4) (var 7)))
          (numerator (var 0) (var 1) (var 2) (var 4) (var 6) (var 7)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (sampled_endpoint_error _ _ _ _ _ _ _ _ Prf.hyp0))

theorem all_degree_retimed_grid_upper_endpoint_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
          le (precision (var 0) (var 3) (var 5) (var 7) (var 8)) (var 1)) ⟶
        distanceBounded (scaledEndpoint (var 1) (var 3) (var 5) (var 7) (var 8))
          (ap2 nameF (var 2) (data (var 3) (var 5) (var 8)))
          (unit (var 0)+unit (var 2)) (unit (var 0)*unit (var 2))) :=
  closeUniv 9 (.impI (upper_error_at _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeUpperEndpoint
