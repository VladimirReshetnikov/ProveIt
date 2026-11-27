import IPRADerivations.Analysis.Beta.Primitives.LowerEndpoints.GaussianBetaPrimitiveLowerEndpoint
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsLinear
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerBound

/-!
# Endpoint estimates for the original integration-by-parts boundary

The primitive is the literal time-weighted product of the original power
and decay observations. At the lower cutoff the exact root factor divides
the checked power bound. At an upper integer time, one extra factorial
term in the positive exponential gives an inverse-time bound for the
weighted decay, with the actual observation error tracked separately.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsEndpoints

open_ipra
open GaussianBetaPrimitiveLowerEndpoint (rootDen eta_factorization)
open GaussianEulerIntegrationByPartsLinear (primitive originalProduct decay)
open GaussianEulerPowerIncrement (point)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive)
open GaussianPositiveRationalExponentialDecay (expF inverseData inverseQuery inverse_sample_at degree_in_cutoff)
open GaussianDominantPairAlgebra (radius_bounded)
open GaussianEulerDecayFactorBounds (fraction_is_radius_point original_decay_matches_reciprocal)
open GaussianNameEquivalence (cross_symm cross_diagonal_at)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem lower_endpoint (p z R B A k : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    bounded (primitive p z B one (etaDen k A R)) (num 3*unit p+num 3*rootDen k A R) (rootDen k A R*unit p) := by
  let E := etaDen k A R
  let D := rootDen k A R
  let M := pw D (pred A)
  let U := unit p
  have he : Γ ⊢[PRAAx] le one E := eta_den_positive _ _ _
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hd : Γ ⊢[PRAAx] le one D := unit_positive _
  have dpoint := GaussianEulerDecayIncrement.decay_observation_uniform_bound one E p (le_refl one) he
  have product := bounded_product (point p z B one E) (decay p one E) (M*U+one) U _ one hu (le_refl one)
    (GaussianBetaPrimitiveLowerEndpoint.original_cutoff_power p z R B A k h) dpoint
  have tp := bound_congr (fraction_is_radius_point one E he).eqSymm (.eqRefl _) (.eqRefl _) (radius_bounded one E he)
  have raw := bounded_product _ (originalProduct p z B one E) _ E _ _ he (positive_product _ _ hu (le_refl one)) tp product
  have endpoint : Γ ⊢[PRAAx] bounded (primitive p z B one E) (num 3*(M*U+one)) (E*U) :=
    bound_congr (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (by ipra_ring) raw
  have heq := natEq (eta_factorization (Γ := Γ) k A R h.andE₁)
  have grow : Γ ⊢[PRAAx] le (num 3*D*U) (num 3*D*U*E) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (num 3*D*U) he)
  have cmp : Γ ⊢[PRAAx] le (num 3*(M*U+one)*(D*U)) ((num 3*U+num 3*D)*(E*U)) :=
    le_congr (by
      apply deriveNat
      dsimp only [D,E,M,U]
      ipra_simps
      rw [heq]
      ring) (by ipra_ring) (add_le_add₂ (le_refl (num 3*E*U*U)) grow)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ he hu) (positive_product _ _ hd hu) cmp endpoint

/-- The factorial term is applied before forming the actual inverse. -/
theorem integer_decay_factorial (p T j : PTm n) (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx]
    bounded (decay p T one) (fact j*unit p+two*pw T j) (pw T j*unit p) := by
  let K := GaussianRadiusExponentialName.index (T+j) (inverseQuery p)
  let Y := ap2 (GaussianNameReciprocal.nameF expF) p (inverseData T one j)
  let X := decay p T one
  let P := pw T j
  have hf := GammaEulerMesh.factorial_positive (Γ := Γ) j
  have hp := GaussianPolynomialPerturbation.power_positive T j hT
  have raw := GaussianPositiveExponentialTermBound.original_monomial_lower (Γ := Γ) T one j K (le_refl one)
    (degree_in_cutoff T j (inverseQuery p))
  have low := GaussianRationalLowerBounds.lower_congr (.eqRefl _) (.eqRefl _)
    ((congrMul (.eqRefl (fact j)) (AnalyticNumberTheory.Order.pw_one_base j)).eqTrans (by ipra_ring)) raw
  have bound : Γ ⊢[PRAAx] bounded Y (fact j) P :=
    bound_congr (inverse_sample_at T one j p).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianRationalLowerBounds.inverse_bound _ _ _ hp hf low)
  have law := cross_symm (Γ := Γ) _ _ _ _ (original_decay_matches_reciprocal T one j (le_refl one))
  have near := cross_diagonal_at p law
  exact bound_congr (.eqRefl X) (by ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.norm_from_distance X Y _ _ _ _ (unit_positive p) hp near bound)

theorem upper_endpoint (p z R B T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B) (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx]
    bounded (primitive p z B T one)
      (two*fact (succ (succ R))*unit p+num 4*pw T (succ (succ R))) (T*unit p) := by
  let U := unit p
  let P := pw T R
  let W := pw T (succ R)
  let j := succ (succ R)
  let D := pw T j
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hp : Γ ⊢[PRAAx] le one P := GaussianPolynomialPerturbation.power_positive T R hT
  have hd : Γ ⊢[PRAAx] le one D := GaussianPolynomialPerturbation.power_positive T j hT
  have powerRaw := GaussianEulerUpperPowerBound.original_power_bound p z R B T one (.andI h (.andI (.andI hT (le_refl one)) hT))
  have powerObs : Γ ⊢[PRAAx] bounded (point p z B T one) (P*U+one) U :=
    bound_congr (.eqRefl _) (congrAdd (.eqRefl _) (AnalyticNumberTheory.Order.pw_one_base R))
      ((congrMul (AnalyticNumberTheory.Order.pw_one_base R) (.eqRefl U)).eqTrans (by ipra_ring)) powerRaw
  have powerBound : Γ ⊢[PRAAx] bounded (point p z B T one) (two*P) one := by
    apply bounded_radius_mono _ _ _ _ _ hu (le_refl one) _ powerObs
    exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (P*U)) (positive_product _ _ hp hu))
  have timeBound := bound_congr (Γ := Γ) (fraction_is_radius_point T one (le_refl one)).eqSymm (.eqRefl _) (.eqRefl _)
    (radius_bounded T one (le_refl one))
  have weighted : Γ ⊢[PRAAx] bounded (qmul (GaussianPositiveRationalLogarithm.fraction T one) (point p z B T one)) (two*W) one :=
    bound_congr (.eqRefl _) (by
      have e := natEq (pw_succ (Γ := Γ) T R)
      apply deriveNat
      dsimp only [W,P]
      ipra_simps
      rw [e]
      ring) (by ipra_ring) (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) timeBound powerBound)
  have raw := bounded_product _ (decay p T one) (two*W) one (fact j*U+two*D) (D*U)
    (le_refl one) (positive_product _ _ hd hu) weighted (integer_decay_factorial p T j hT)
  have actual : Γ ⊢[PRAAx] bounded (primitive p z B T one) (two*W*(fact j*U+two*D)) (D*U) :=
    bound_congr (GaussianReciprocalHorner.qmul_associative _ _ _) (.eqRefl _) (by ipra_ring) raw
  have hEq := natEq (pw_succ (Γ := Γ) T (succ R))
  have cmp : Γ ⊢[PRAAx] le ((two*W*(fact j*U+two*D))*(T*U)) ((two*fact j*U+num 4*D)*(D*U)) := by
    apply le_of_eq_add (d := ConciseIPRA.PTm.zero)
    apply deriveNat
    dsimp only [D,W,j,U]
    ipra_simps
    rw [hEq]
    ring
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hd hu) (positive_product _ _ hT hu) cmp actual

theorem original_lower_integration_by_parts_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianEulerLowerPowerCoefficients.source (var 1) (var 2) (var 3) (var 4) ⟶
      bounded (primitive (var 0) (var 1) (var 3) one (etaDen (var 5) (var 4) (var 2)))
        (num 3*unit (var 0)+num 3*rootDen (var 5) (var 4) (var 2))
        (rootDen (var 5) (var 4) (var 2)*unit (var 0))) :=
  closeUniv 6 (.impI (lower_endpoint _ _ _ _ _ _ Prf.hyp0))

theorem original_upper_integration_by_parts_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((GaussianEulerUpperPowerCoefficients.source (var 1) (var 2) (var 3) ⋏ le one (var 4)) ⟶
      bounded (primitive (var 0) (var 1) (var 3) (var 4) one)
        (two*fact (succ (succ (var 2)))*unit (var 0)+num 4*pw (var 4) (succ (succ (var 2))))
        (var 4*unit (var 0))) :=
  closeUniv 5 (.impI (upper_endpoint _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsEndpoints
