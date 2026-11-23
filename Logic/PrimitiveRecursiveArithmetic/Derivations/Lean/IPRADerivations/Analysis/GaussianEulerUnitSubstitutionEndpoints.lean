import IPRADerivations.Analysis.GaussianEulerUnitSubstitutionCompactName
import IPRADerivations.Analysis.GaussianEulerDecayRealSamples
import IPRADerivations.Analysis.GaussianEulerDecayAddition
import IPRADerivations.Analysis.GaussianExponentialSmallPerturbation

/-!
# Original mapped unit endpoints exhaust zero and one

The left endpoint is the original decay at the original upper time
cutoff. Its integer dyadic bound keeps the actual observation error.
The right endpoint is the original decay at the original lower time
cutoff. Every actual finite exponential is within 3/etaDen of one,
so this endpoint estimate needs no observation error at all. A fixed
four-bit cutoff threshold gives exact requested dyadic neighborhoods.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionEndpoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def leftSample (p k A R : PTm n) : PTm n := ap2 decayF p (decayData (top k A R) one)
def rightSample (p k A R : PTm n) : PTm n := ap2 decayF p (decayData one (etaDen k A R))
def cutoff (s : PTm n) : PTm n := GaussianEulerUnitSubstitutionCompactName.stage s
def source (p s k A : PTm n) : Fm PTm n := le one A ⋏ (le (cutoff s) k ⋏ le (cutoff s) p)

@[simp] theorem subst_leftSample {m : ℕ} (σ : Fin n → PTm m) (p k A R : PTm n) :
    Syn.subst σ (leftSample p k A R) = leftSample (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [leftSample,decayData,GaussianGammaFiniteApproximantName.exponentialInputData,
    top,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_rightSample {m : ℕ} (σ : Fin n → PTm m) (p k A R : PTm n) :
    Syn.subst σ (rightSample p k A R) = rightSample (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [rightSample,decayData,GaussianGammaFiniteApproximantName.exponentialInputData,
    etaDen,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (s : PTm n) :
    Syn.subst σ (cutoff s) = cutoff (Syn.subst σ s) := by simp [cutoff]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (p s k A : PTm n) :
    (source p s k A).subst σ = source (Syn.subst σ p) (Syn.subst σ s) (Syn.subst σ k) (Syn.subst σ A) := by simp [source]

/-- This bound holds for every original finite cutoff and every actual
query p. Only the literal input point's small disk is used. -/
theorem original_small_time_near_one (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 decayF p (decayData a b)) qone (num 3*a) b := by
  have finite := GaussianExponentialSmallPerturbation.finite_perturbation (decayPoint a b) a b
    (GaussianRadiusExponentialName.index (GaussianNameBounds.U GaussianGammaCanonicalExponent.constantF (decayPoint a b)) p)
    hb hab (GaussianEulerDecayAddition.decay_point_bounded a b hb)
  exact distance_congr (GaussianEulerDecayRealSamples.original_observation_at p a b).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) finite

theorem original_right_endpoint_bound (p k A R : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (rightSample p k A R) qone (num 3) (etaDen k A R) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (original_small_time_near_one p one (etaDen k A R)
      (GaussianGammaIntegralCutoffs.eta_den_positive k A R) (GaussianGammaIntegralCutoffs.eta_den_positive k A R))

theorem original_left_endpoint_bound (p k A R : PTm n) : Γ ⊢[PRAAx]
    bounded (leftSample p k A R) (unit p+two*unit (top k A R)) (unit (top k A R)*unit p) :=
  GaussianEulerDecayFactorBounds.original_integer_decay_bound (top k A R) p

theorem height_above_index (k A R : PTm n) : Γ ⊢[PRAAx] le k (height k A R) :=
  le_trans (le_add_right k A) (le_trans (le_add_right _ _) (le_add_right _ _))

theorem right_horizon (s k A R : PTm n) (ha : Γ ⊢[PRAAx] le one A)
    (hk : Γ ⊢[PRAAx] le (cutoff s) k) : Γ ⊢[PRAAx] le (unit (cutoff s)) (etaDen k A R) := by
  have scale : Γ ⊢[PRAAx] le (height k A R) (A*height k A R) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (height k A R) ha)
  exact GaussianExponentialReference.unit_monotone (le_trans hk (le_trans (height_above_index k A R) scale))

theorem left_horizon (s k A R : PTm n) (hk : Γ ⊢[PRAAx] le (cutoff s) k) : Γ ⊢[PRAAx]
    le (unit (cutoff s)) (unit (top k A R)) := by
  have scale : Γ ⊢[PRAAx] le (height k A R) (top k A R) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (height k A R) (zero_lt_succ one))
  exact GaussianExponentialReference.unit_monotone (le_trans hk (le_trans (height_above_index k A R) scale))

theorem requested_budget (s : PTm n) : Γ ⊢[PRAAx] le (num 3*unit s) (unit (cutoff s)) :=
  le_trans (le_of_eq_add (d := num 3*unit s) (by ipra_ring))
    (GaussianEulerUnitSubstitutionCompactName.stage_budget s)

/-- The near-one endpoint is uniform over all original observation
queries, while the original lower cutoff alone tends to zero. -/
theorem original_right_exhaustion (p s k A R : PTm n) (ha : Γ ⊢[PRAAx] le one A)
    (hk : Γ ⊢[PRAAx] le (cutoff s) k) : Γ ⊢[PRAAx]
    distanceBounded (rightSample p k A R) qone one (unit s) :=
  distance_radius_mono _ _ _ _ one (unit s) (GaussianGammaIntegralCutoffs.eta_den_positive k A R) (unit_positive s)
    (le_congr (.eqRefl _) (by ipra_ring) (le_trans (requested_budget s) (right_horizon s k A R ha hk)))
    (original_right_endpoint_bound p k A R)

theorem original_left_exhaustion (p s k A R : PTm n)
    (hk : Γ ⊢[PRAAx] le (cutoff s) k) (hp : Γ ⊢[PRAAx] le (cutoff s) p) : Γ ⊢[PRAAx]
    bounded (leftSample p k A R) one (unit s) := by
  let H := unit (cutoff s)
  let U := unit p
  let V := unit (top k A R)
  have hH := unit_positive (Γ := Γ) (cutoff s)
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) (top k A R)
  have hTop : Γ ⊢[PRAAx] le H V := left_horizon s k A R hk
  have hQuery : Γ ⊢[PRAAx] le H U := GaussianExponentialReference.unit_monotone hp
  have coarse := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ (num 3) H
    (positive_product _ _ hV hU) hH (by ipra_le 𝔞 U*sl hTop+2*𝔞 V*sl hQuery)
    (original_left_endpoint_bound p k A R)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ one (unit s) hH (unit_positive s)
    (le_congr (.eqRefl _) (by ipra_ring) (requested_budget (Γ := Γ) s)) coarse

theorem original_endpoints (p q s k A R : PTm n) (hs : Γ ⊢[PRAAx] source p s k A) : Γ ⊢[PRAAx]
    bounded (leftSample p k A R) one (unit s) ⋏ distanceBounded (rightSample q k A R) qone one (unit s) :=
  .andI (original_left_exhaustion p s k A R hs.andE₂.andE₁ hs.andE₂.andE₂)
    (original_right_exhaustion q s k A R hs.andE₁ hs.andE₂.andE₁)

theorem actual_original_unit_mapped_endpoints_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 2) (var 3) (var 4) ⟶
      bounded (leftSample (var 0) (var 3) (var 4) (var 5)) one (unit (var 2)) ⋏
        distanceBounded (rightSample (var 1) (var 3) (var 4) (var 5)) qone one (unit (var 2))) :=
  closeUniv 6 (.impI (original_endpoints _ _ _ _ _ _ Prf.hyp0))

theorem original_small_time_decay_exact_sample_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 2) ⋏ le (var 1) (var 2)) ⟶
      distanceBounded (ap2 decayF (var 0) (decayData (var 1) (var 2))) qone (num 3*var 1) (var 2)) :=
  closeUniv 3 (.impI (original_small_time_near_one _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionEndpoints
