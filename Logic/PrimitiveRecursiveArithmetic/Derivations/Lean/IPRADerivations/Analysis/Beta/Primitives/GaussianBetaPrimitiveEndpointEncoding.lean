import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveLowerEndpoint
import IPRADerivations.Analysis.Euler.Integration.Parameters.GaussianEulerPowerInputProperness

/-!
# Lower beta endpoints at the actual rational grid encoding

The raw time J/(etaDen*J) keeps its original power program and clocks.
True original power-name properness and one finite Euclidean gap retain
its requested observation error. The polynomial argument is a literal
canonical fraction equality. The unchanged endpoint and exact N-scaled
endpoint therefore retain the lower-cutoff budget, including the actual
argument-dependent clock of the original beta grid telescope.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveEndpointEncoding

open_ipra
open GaussianEulerLowerPowerCoefficients (source)
open GaussianGammaIntegralCutoffs (height etaDen eta_den_positive)
open GaussianBetaPrimitiveLowerEndpoint (rootDen budget numerator denominator eta_factorization root_den_positive precision)
open GaussianBetaPrimitiveLinearStep (argument)
open GaussianEulerPowerIncrement (point)
open GaussianEulerCompactProductComparison (clock)
open GaussianEulerBetaPolynomialPrimitive (primitive)
open GaussianTimeWeightedPolynomialIncrement (value)
open GaussianRationalHorner (qmul evaluate positive_product canonical_unique ofGaussian_represents ofGaussian_canonical represents_congr represents_rescale)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open ComplexLogarithmRemainder (oneCode scale)
open GaussianRootAlgebra (equal equal_of_values re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def endpoint (p z B k A R N J : PTm n) : PTm n :=
  GaussianBetaPrimitiveLinearStep.sample p z B J (etaDen k A R*J) N
def scaledEndpoint (p z B k A R N J : PTm n) : PTm n := qmul (naturalPoint N) (endpoint p z B k A R N J)
def clockScaledEndpoint (p z B k A R N J : PTm n) : PTm n :=
  scaledEndpoint (clock p z B J (etaDen k A R*J)) z B k A R N J

ipra_subst endpoint [GaussianBetaPrimitiveLinearStep.sample, argument, point, value, etaDen, height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst scaledEndpoint
ipra_subst clockScaledEndpoint [etaDen, height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem encoded_power_slack (p s z R B A k J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (point p z B J (etaDen k A R*J))
      (pw (rootDen k A R) (pred A)*unit p+one) (unit p) two s := by
  let P := unit p
  let S := unit s
  let W := pw (rootDen k A R) (pred A)
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have he := eta_den_positive (Γ := Γ) k A R
  have near := GaussianEulerPowerInputProperness.original_power_observations p s z B J (etaDen k A R*J) one (etaDen k A R)
    h.andE₂.andE₁.andE₁ (.andI hJ (positive_product _ _ he hJ)) (.andI (le_refl one) he) (by ipra_ring)
  have old := GaussianBetaPrimitiveLowerEndpoint.original_cutoff_power s z R B A k h
  have result := GaussianReconstructionRoots.norm_from_distance _ _ (P+S) (P*S) (W*S+one) S
    (positive_product _ _ hp hs) hs near old
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hs) hs)
    (positive_product _ _ hp hs) (le_of_eq_add (d := zero) (by dsimp only [P,S,W,unit]; ipra_ring)) result

/-- The actual raw grid encoding retains exactly its own eps_p. -/
theorem encoded_power_bound (p z R B A k J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (point p z B J (etaDen k A R*J)) (pw (rootDen k A R) (pred A)*unit p+one) (unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ two (unit_positive p)
    (encoded_power_slack p (GaussianRationalSlackRemoval.precision (point p z B J (etaDen k A R*J))
      (pw (rootDen k A R) (pred A)*unit p+one) (unit p) two) z R B A k J h hJ)

theorem argument_encoding (k A R N J : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    argument J (etaDen k A R*J) N ≐ argument one (etaDen k A R) N := by
  let D := etaDen k A R*N
  let F := (etaDen k A R*J)*N
  have hd := positive_product (Γ := Γ) _ _ (eta_den_positive k A R) hN
  have hf : Γ ⊢[PRAAx] le one F := positive_product _ _ (positive_product _ _ (eta_den_positive k A R) hJ) hN
  have native : Γ ⊢[PRAAx] equal (scale J oneCode) (scale J (scale one oneCode)) := by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
  exact canonical_unique _ _ (scale J oneCode) F (ofGaussian_canonical _ _ hf) (ofGaussian_canonical _ _ hd) hf
    (ofGaussian_represents _ _ hf)
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_symm native) (by dsimp only [D,F]; ipra_ring)
      (represents_rescale _ _ D J (ofGaussian_represents _ _ hd)))

theorem encoded_primitive_bound (z B k A R N J : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (evaluate (primitive z B N) (argument J (etaDen k A R*J) N)) (budget z B N) one :=
  GaussianRationalUniformFirstOrderPolynomial.value_bound _ _ one (le_refl one)
    (bound_congr (argument_encoding k A R N J hN hJ).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianBetaPrimitiveLowerEndpoint.argument_unit_disk k A R N hN))

theorem encoded_lower_endpoint_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (endpoint p z B k A R N J) (numerator p z B k A R N) (denominator p k A R N) := by
  have hd := positive_product (Γ := Γ) _ _ (eta_den_positive k A R) hN
  have argumentBound : Γ ⊢[PRAAx] bounded (argument J (etaDen k A R*J) N) one (etaDen k A R*N) :=
    bound_congr (argument_encoding k A R N J hN hJ).eqSymm (.eqRefl _) (.eqRefl _)
      (bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point one (etaDen k A R*N) hd).eqSymm
        (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded one _ hd))
  have poly := bounded_product _ _ (budget z B N) one one (etaDen k A R*N) (le_refl one) hd
    (encoded_primitive_bound z B k A R N J hN hJ) argumentBound
  have result := bounded_product _ _ _ _ _ _ (unit_positive p) (positive_product _ _ (le_refl one) hd)
    (encoded_power_bound p z R B A k J h hJ) poly
  exact bound_congr (.eqRefl _) (by unfold numerator; ipra_ring) (by unfold denominator; ipra_ring) result

theorem encoded_scaled_endpoint_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (scaledEndpoint p z B k A R N J) (numerator p z B k A R N) (etaDen k A R*unit p) := by
  have hd := positive_product (Γ := Γ) _ _ (positive_product _ _ hN (eta_den_positive k A R)) (unit_positive p)
  have natural : Γ ⊢[PRAAx] bounded (naturalPoint N) N one :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point N one (le_refl one)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded N one (le_refl one))
  have result := bounded_product _ _ N one _ _ (le_refl one) hd natural (encoded_lower_endpoint_bound p z R B A k N J h hN hJ)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) hd)
    (positive_product _ _ (eta_den_positive k A R) (unit_positive p))
    (le_of_eq_add (d := zero) (by ipra_ring)) result

theorem encoded_dyadic_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (scaledEndpoint p z B k A R N J) (budget z B N*unit p+budget z B N*rootDen k A R)
      (rootDen k A R*unit p) := by
  let d := rootDen k A R
  let E := etaDen k A R
  let M := budget z B N
  let P := unit p
  have compare : Γ ⊢[PRAAx] le ((M*(pw d (pred A)*P+one))*(d*P)) ((M*P+M*d)*(E*P)) := by
    have e := natEq (eta_factorization (Γ := Γ) k A R h.andE₁)
    have growth : Γ ⊢[PRAAx] le (M*d*P) (M*d*P*E) :=
      le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (M*d*P) (eta_den_positive (Γ := Γ) k A R))
    have g := natEq (eq_add_of_le growth)
    apply le_of_eq_add (d := LeanProofs.IPRA.PTm.monus (M*d*P*E) (M*d*P))
    apply deriveNat
    dsimp only [E,d] at g ⊢
    ipra_simps
    rw [e] at g ⊢
    linear_combination g
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (eta_den_positive k A R) (unit_positive p))
    (positive_product _ _ (root_den_positive k A R) (unit_positive p)) compare
    (encoded_scaled_endpoint_bound p z R B A k N J h hN hJ)

/-- Actual argument-dependent grid clock, with the requested outer p
retained in its error budget. -/
theorem original_clock_scaled_endpoint_bound (p z R B A k N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (clockScaledEndpoint p z B k A R N J) (budget z B N*unit p+budget z B N*rootDen k A R)
      (rootDen k A R*unit p) := by
  let q := clock p z B J (etaDen k A R*J)
  let M := budget z B N
  let d := rootDen k A R
  have grow := GaussianExponentialReference.unit_monotone (GaussianEulerCompactProductComparison.clock_later (Γ := Γ) p z B J (etaDen k A R*J))
  have compare : Γ ⊢[PRAAx] le ((M*unit q+M*d)*(d*unit p)) ((M*unit p+M*d)*(d*unit q)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (M*unit q*d*unit p) (mul_le_mul_right (M*d*d) grow))
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (root_den_positive k A R) (unit_positive q))
    (positive_product _ _ (root_den_positive k A R) (unit_positive p)) compare
    (encoded_dyadic_bound q z R B A k N J h hN hJ)

/-- The computed degree-dependent precision from the original endpoint
proof also works at the raw grid encoding and its actual larger clock. -/
theorem constructive_clock_endpoint_small (t z R B A N J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    bounded (clockScaledEndpoint (precision t z B N) z B (precision t z B N) A R N J) one (unit t) := by
  let q := precision t z B N
  let d := rootDen q A R
  let M := budget z B N
  let P := unit (succ t)
  have later : Γ ⊢[PRAAx] le q (height q A R) :=
    le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+LeanProofs.IPRA.PTm.num 10) (by unfold height; ipra_ring)
  have growth : Γ ⊢[PRAAx] le (unit q) d := GaussianExponentialReference.unit_monotone later
  have query : Γ ⊢[PRAAx] le (M*P) (unit q) := GaussianFastValueCut.query_budget _ _
  have first : Γ ⊢[PRAAx] le (M*P*unit q) (d*unit q) :=
    le_trans (mul_le_mul_right (unit q) query) (mul_le_mul_right (unit q) growth)
  have last : Γ ⊢[PRAAx] le (M*P*d) (unit q*d) := mul_le_mul_right d query
  have compare : Γ ⊢[PRAAx] le ((M*unit q+M*d)*P) (two*(d*unit q)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ first last)
  have small : Γ ⊢[PRAAx] bounded (clockScaledEndpoint q z B q A R N J) two P :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (root_den_positive q A R) (unit_positive q))
      (unit_positive (succ t)) compare (original_clock_scaled_endpoint_bound q z R B A q N J h hN hJ)
  exact bounded_radius_mono _ _ _ _ _ (unit_positive (succ t)) (unit_positive t)
    (le_of_eq_add (d := zero) ((congrMul (.eqRefl one) (pw_succ two t)).eqTrans (by unfold unit; ipra_ring))) small

theorem actual_beta_lower_argument_encoding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 3) ⋏ le one (var 4)) ⟶
      argument (var 4) (etaDen (var 0) (var 1) (var 2)*var 4) (var 3) ≐
        argument one (etaDen (var 0) (var 1) (var 2)) (var 3)) :=
  closeUniv 5 (.impI (argument_encoding _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_raw_encoded_beta_lower_endpoint_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ le one (var 6) ⋏ le one (var 7)) ⟶
      bounded (endpoint (var 0) (var 1) (var 3) (var 5) (var 4) (var 2) (var 6) (var 7))
        (numerator (var 0) (var 1) (var 3) (var 5) (var 4) (var 2) (var 6))
        (denominator (var 0) (var 5) (var 4) (var 2) (var 6))) :=
  closeUniv 8 (.impI (encoded_lower_endpoint_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem original_grid_clock_N_scaled_lower_endpoint_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ le one (var 6) ⋏ le one (var 7)) ⟶
      bounded (clockScaledEndpoint (var 0) (var 1) (var 3) (var 5) (var 4) (var 2) (var 6) (var 7))
        (budget (var 1) (var 3) (var 6)*unit (var 0)+budget (var 1) (var 3) (var 6)*rootDen (var 5) (var 4) (var 2))
        (rootDen (var 5) (var 4) (var 2)*unit (var 0))) :=
  closeUniv 8 (.impI (original_clock_scaled_endpoint_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem original_grid_clock_encoded_endpoint_constructively_small_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ le one (var 5) ⋏ le one (var 6)) ⟶
      bounded (clockScaledEndpoint (precision (var 0) (var 1) (var 3) (var 5)) (var 1) (var 3)
        (precision (var 0) (var 1) (var 3) (var 5)) (var 4) (var 2) (var 5) (var 6)) one (unit (var 0))) :=
  closeUniv 7 (.impI (constructive_clock_endpoint_small _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveEndpointEncoding
