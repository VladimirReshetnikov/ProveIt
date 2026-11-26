import IPRADerivations.Analysis.Euler.Integration.Parameters.GaussianNamedEulerIntegrandParameterContinuity
import IPRADerivations.Analysis.Names.Approximation.GaussianNamedRationalApproximation
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlane

/-!
# Original named Euler integrand: uniform compact time variation

Freeze the same actual observation of the input at both times. Two
proved parameter comparisons and the original encoded time modulus
give a finite auxiliary dyadic error. Exact rational slack removal
leaves the original two independent observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerCompactTimeRate

open_ipra
open GaussianNamedRightHalfPlane (numerator denominator)
open GaussianNamedEulerIntegrandParameterContinuity (radius)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianCompactLogarithmBounds (domain)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gain (f : PR 2) (x E T : PTm n) : PTm n := GaussianEulerCompactModulus.lipschitz (radius f x) E T
def auxiliary (f : PR 2) (x E T : PTm n) : PTm n := two*GaussianNamedEulerIntegrandParameterContinuity.factor f x E T+num 4
def input (f : PR 2) (x E T a b c d A N : PTm n) : Fm PTm n := pointCN f x ⋏
  (le one E ⋏ (domain a b E T ⋏ (domain c d E T ⋏ (le one N ⋏
    distanceBounded (GaussianPositiveRationalLogarithm.fraction a b) (GaussianPositiveRationalLogarithm.fraction c d) A N))))
ipra_subst gain
ipra_subst auxiliary
ipra_subst input

theorem frozen_source (f : PR 2) (x t E : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    GaussianEulerExponentCompactBounds.source (numerator f t x) (radius f x) (denominator f t x) E :=
  .andI (GaussianRationalL1.raw_den_positive _) (.andI hE (GaussianNamedRightHalfPlane.actual_sample_disk f x t hf))

theorem frozen_input (f : PR 2) (x t E T a b : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hE : Γ ⊢[PRAAx] le one E) (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    GaussianNamedEulerIntegrandParameterContinuity.input f x (numerator f t x) (denominator f t x) E T a b one (unit t) :=
  .andI hf (.andI (frozen_source f x t E hf hE) (.andI ht (.andI (unit_positive t)
    (GaussianNamedRationalApproximation.frozen_constant_rate f x t hf))))

/-- Same original frozen parameter at both times, and no alleged
continuity statement supplied for either named output. -/
theorem original_slack (f : PR 2) (p q t x E T a b c d A N : PTm n)
    (h : Γ ⊢[PRAAx] input f x E T a b c d A N) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack
      (qsub (ap2 (GaussianNamedEulerIntegrand.nameF f) p (GaussianNamedEulerIntegrand.data f x a b))
        (ap2 (GaussianNamedEulerIntegrand.nameF f) q (GaussianNamedEulerIntegrand.data f x c d)))
      (rateNumerator (gain f x E T*A) N p q) (rateDenominator N p q) (auxiliary f x E T) t := by
  let G := GaussianNamedEulerIntegrandParameterContinuity.factor f x E T
  let Z := rateDenominator N p q*unit t
  have hN := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have pos : Γ ⊢[PRAAx] le one Z := positive_product _ _ (denominator_positive N p q hN) (unit_positive t)
  have leftRaw := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p t
    (GaussianNamedEulerIntegrandParameterContinuity.original_rate f x (numerator f t x) (denominator f t x) E T a b one (unit t)
      (frozen_input f x t E T a b h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁))
  have rightRaw := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ q t
    (GaussianNamedEulerIntegrandParameterContinuity.original_rate f x (numerator f t x) (denominator f t x) E T c d one (unit t)
      (frozen_input f x t E T c d h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁))
  have middleRaw := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ t t
    (GaussianEulerCompactModulus.original_rate (numerator f t x) (radius f x) (denominator f t x) E T a b c d A N
      (.andI (frozen_source f x t E h.andE₁ h.andE₂.andE₁) (.andI h.andE₂.andE₂.andE₁
        (.andI h.andE₂.andE₂.andE₂.andE₁ (.andI hN h.andE₂.andE₂.andE₂.andE₂.andE₂)))))
  have left := distance_radius_mono _ _ _ _ ((G+one)*(N*unit p*unit q)+N*unit q*unit t) Z
    (denominator_positive (unit t) p t (unit_positive t)) pos
    (le_of_eq_add (d := zero) (by dsimp [G,Z,rateNumerator,rateDenominator]; ipra_ring)) leftRaw
  have middle := distance_radius_mono _ _ _ _ ((gain f x E T*A)*(unit p*unit q*unit t)+two*N*unit p*unit q) Z
    (denominator_positive N t t hN) pos
    (le_of_eq_add (d := zero) (by dsimp [gain,Z,rateNumerator,rateDenominator]; ipra_ring)) middleRaw
  have right := distance_radius_mono _ _ _ _ ((G+one)*(N*unit p*unit q)+N*unit p*unit t) Z
    (denominator_positive (unit t) q t (unit_positive t)) pos
    (le_of_eq_add (d := zero) (by dsimp [G,Z,rateNumerator,rateDenominator]; ipra_ring))
    (distance_symmetric _ _ _ _ (denominator_positive (unit t) q t (unit_positive t)) rightRaw)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp [G,auxiliary,rateNumerator,rateDenominator,unit]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ pos (distance_triangle_same _ _ _ _ _ _ pos left middle) right)

theorem original_observations (f : PR 2) (p q x E T a b c d A N : PTm n)
    (h : Γ ⊢[PRAAx] input f x E T a b c d A N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (GaussianNamedEulerIntegrand.nameF f) p (GaussianNamedEulerIntegrand.data f x a b))
      (ap2 (GaussianNamedEulerIntegrand.nameF f) q (GaussianNamedEulerIntegrand.data f x c d))
      (rateNumerator (gain f x E T*A) N p q) (rateDenominator N p q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (auxiliary f x E T)
    (denominator_positive N p q h.andE₂.andE₂.andE₂.andE₂.andE₁)
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift x) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b)
      (Syn.shift c) (Syn.shift d) (Syn.shift A) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,subst_ap2,
    GaussianNamedEulerIntegrand.subst_data,GaussianNamedInverseRate.subst_rateNumerator,GaussianNamedInverseRate.subst_rateDenominator,
    subst_gain,subst_auxiliary,PTm.subst_mul,Syn.shift] using original_slack f (Syn.shift p) (Syn.shift q) (var 0)
      (Syn.shift x) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift A) (Syn.shift N) hs

theorem original_rate (f : PR 2) (x E T a b c d A N : PTm n)
    (h : Γ ⊢[PRAAx] input f x E T a b c d A N) : Γ ⊢[PRAAx]
    independentRate (GaussianNamedEulerIntegrand.nameF f) (GaussianNamedEulerIntegrand.nameF f)
      (GaussianNamedEulerIntegrand.data f x a b) (GaussianNamedEulerIntegrand.data f x c d) (gain f x E T*A) N := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input f (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T))
      (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianNamedEulerIntegrand.subst_data,subst_gain,PTm.subst_mul,Syn.shift] using
    original_observations f (var 1) (var 0) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T))
      (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift N)) hs

theorem original_named_Euler_compact_time_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      independentRate (GaussianNamedEulerIntegrand.nameF f) (GaussianNamedEulerIntegrand.nameF f)
        (GaussianNamedEulerIntegrand.data f (var 0) (var 3) (var 4)) (GaussianNamedEulerIntegrand.data f (var 0) (var 5) (var 6))
        (gain f (var 0) (var 1) (var 2)*var 7) (var 8)) :=
  closeUniv 9 (.impI (original_rate f _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerCompactTimeRate
