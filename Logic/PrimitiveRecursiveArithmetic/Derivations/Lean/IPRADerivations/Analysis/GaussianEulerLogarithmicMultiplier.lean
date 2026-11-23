import IPRADerivations.Analysis.GaussianEulerCompactModulus
import IPRADerivations.Analysis.GaussianPositiveExponentialMajorant

/-!
# Actual logarithmic factors in compact Euler integrands

The numerical order j is an input to an actual PR3 evaluator. Its row is
the unchanged original Euler observation times the j-th actual rational
power of the unchanged original positive-rational logarithm observation.
Original compact guards derive a uniform row bound and a two-time,
independent-precision variation estimate. No derivative, logarithmic
tail, or output-modulus law is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicMultiplier

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (power bound_congr)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCompactLogarithmBounds (domain)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def logarithmicPower (p j a b : PTm n) : PTm n := power (GaussianPositiveRationalLogarithm.sample p a b) j
def sample (p j z B a b : PTm n) : PTm n := qmul (GaussianEulerIntegrandName.sample p z B a b) (logarithmicPower p j a b)
def fixedData (j z B : PTm n) : PTm n := pairT j (pairT z B)
def evaluatorTerm (p t x : PTm n) : PTm n := sample p (fstT x) (fstT (sndT x)) (sndT (sndT x)) (fstT t) (sndT t)
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def logRadius (E T : PTm n) : PTm n := GaussianCompactLogarithmBounds.radius E T
def eulerMajorant (R E T : PTm n) : PTm n := pw (LeanProofs.IPRA.PTm.num 3) (GaussianEulerExponentCompactBounds.radius R E T)
def logGain (j E T : PTm n) : PTm n := j*pw (logRadius E T) (LeanProofs.IPRA.PTm.pred j)
def majorant (j R E T : PTm n) : PTm n := eulerMajorant R E T*pw (logRadius E T) j
def observationCost (j R E T : PTm n) : PTm n := pw (logRadius E T) j+eulerMajorant R E T*logGain j E T
def lipschitz (j R E T : PTm n) : PTm n := GaussianEulerCompactModulus.lipschitz R E T*pw (logRadius E T) j+eulerMajorant R E T*logGain j E T*E
def numerator (p q j R E T A D : PTm n) : PTm n := lipschitz j R E T*A*unit p*unit q+observationCost j R E T*D*(unit p+unit q)
def source (z R B E T a b : PTm n) : Fm PTm n := GaussianEulerExponentCompactBounds.source z R B E ⋏ domain a b E T

@[simp] theorem subst_logarithmicPower {m : ℕ} (σ : Fin n → PTm m) (p j a b : PTm n) :
    Syn.subst σ (logarithmicPower p j a b) = logarithmicPower (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ a) (Syn.subst σ b) := by simp [logarithmicPower]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p j z B a b : PTm n) :
    Syn.subst σ (sample p j z B a b) = sample (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [sample]
@[simp] theorem subst_fixedData {m : ℕ} (σ : Fin n → PTm m) (j z B : PTm n) :
    Syn.subst σ (fixedData j z B) = fixedData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ B) := by simp [fixedData]
@[simp] theorem subst_evaluatorTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (evaluatorTerm p t x) = evaluatorTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by simp [evaluatorTerm]
@[simp] theorem subst_logRadius {m : ℕ} (σ : Fin n → PTm m) (E T : PTm n) :
    Syn.subst σ (logRadius E T) = logRadius (Syn.subst σ E) (Syn.subst σ T) := by simp [logRadius]
@[simp] theorem subst_eulerMajorant {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (eulerMajorant R E T) = eulerMajorant (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [eulerMajorant]
@[simp] theorem subst_logGain {m : ℕ} (σ : Fin n → PTm m) (j E T : PTm n) :
    Syn.subst σ (logGain j E T) = logGain (Syn.subst σ j) (Syn.subst σ E) (Syn.subst σ T) := by simp [logGain]
@[simp] theorem subst_majorant {m : ℕ} (σ : Fin n → PTm m) (j R E T : PTm n) :
    Syn.subst σ (majorant j R E T) = majorant (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [majorant]
@[simp] theorem subst_observationCost {m : ℕ} (σ : Fin n → PTm m) (j R E T : PTm n) :
    Syn.subst σ (observationCost j R E T) = observationCost (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [observationCost]
@[simp] theorem subst_lipschitz {m : ℕ} (σ : Fin n → PTm m) (j R E T : PTm n) :
    Syn.subst σ (lipschitz j R E T) = lipschitz (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [lipschitz]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p q j R E T A D : PTm n) :
    Syn.subst σ (numerator p q j R E T A D) = numerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ A) (Syn.subst σ D) := by simp [numerator]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B E T a b : PTm n) :
    (source z R B E T a b).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) := by simp [source]

theorem evaluator_at (p t x : PTm n) : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ evaluatorTerm p t x := by
  simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]

theorem original_sample_at (p j z B a b : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p (pairT a b) (fixedData j z B) ≐ sample p j z B a b := by
  refine (evaluator_at p (pairT a b) (fixedData j z B)).eqTrans ?_
  simpa [evaluatorTerm] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![p,fstT (fixedData j z B),fstT (sndT (fixedData j z B)),sndT (sndT (fixedData j z B)),fstT (pairT a b),sndT (pairT a b)])
      (σ' := ![p,j,z,B,a,b]) (fun i => by
        fin_cases i
        exact .eqRefl _
        exact fst_pair _ _
        exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
        exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
        exact fst_pair _ _
        exact snd_pair _ _)

theorem euler_bound (p z R B E T a b : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    bounded (GaussianEulerIntegrandName.sample p z B a b) (eulerMajorant R E T) one := by
  have ex := GaussianEulerExponentCompactBounds.exponent_bound (GaussianEulerIntegrandName.exponentClock p z B a b) z R B E T a b h.andE₁ h.andE₂
  exact bound_congr (GaussianEulerIntegrandName.sample_original_sum p z B a b).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _ ex)

theorem logarithmic_power_bound (p j a b E T : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (logarithmicPower p j a b) (pw (logRadius E T) j) one :=
  GaussianRationalPowerDifference.bounded_power_integer _ _ j (GaussianCompactLogarithmBounds.sample_bound p a b E T hE h)

theorem original_sample_bound (p j z R B E T a b : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b) : Γ ⊢[PRAAx]
    bounded (sample p j z B a b) (majorant j R E T) one :=
  bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ one _ one (le_refl one) (le_refl one)
      (euler_bound p z R B E T a b h) (logarithmic_power_bound p j a b E T h.andE₁.andE₂.andE₁ h.andE₂))

theorem original_sample_canonical (p j z B a b : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (sample p j z B a b) := GaussianRationalHorner.qmul_canonical _ _

theorem original_order_zero (p z B a b : PTm n) : Γ ⊢[PRAAx] sample p zero z B a b ≐ GaussianEulerIntegrandName.sample p z B a b :=
  (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (GaussianRationalReciprocal.power_zero _)).eqTrans
    (GaussianReciprocalHorner.qmul_one_right _ (GaussianEulerIntegrandName.sample_canonical p z B a b))

/-- Both precisions and both actual original logarithm/Euler observations
are retained. The order j is an unrestricted numerical input. -/
theorem original_variation (p q j z R B E T a b c d A D : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.input z R B E T a b c d A D) : Γ ⊢[PRAAx]
    distanceBounded (sample p j z B a b) (sample q j z B c d)
      (numerator p q j R E T A D) (GaussianNamedInverseRate.rateDenominator D p q) := by
  have hD := h.andE₂.andE₂.andE₂.andE₁
  have ha := h.andE₂.andE₁
  have hc := h.andE₂.andE₂.andE₁
  have hz := h.andE₁
  have logs := GaussianCompactLogarithmBounds.original_log_rate a b c d E A D ha.andE₁ hc.andE₁ hD ha.andE₂.andE₁ hc.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂
  have ln := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q logs
  have lp := GaussianRationalPowerDifference.power_distance_bound _ _ (logRadius E T) _ _ j
    (GaussianNamedInverseRate.denominator_positive D p q hD)
    (GaussianCompactLogarithmBounds.sample_bound p a b E T hz.andE₂.andE₁ ha)
    (GaussianCompactLogarithmBounds.sample_bound q c d E T hz.andE₂.andE₁ hc) ln
  have eu := distance_congr (GaussianEulerIntegrandName.sample_at p z B a b).eqSymm
    (GaussianEulerIntegrandName.sample_at q z B c d).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (GaussianEulerCompactModulus.original_rate z R B E T a b c d A D h))
  have both := GaussianNameArithmetic.product_distance _ _ _ _ _ _ _ _ _
    (GaussianNamedInverseRate.denominator_positive D p q hD) eu lp
    (logarithmic_power_bound p j a b E T hz.andE₂.andE₁ ha) (euler_bound q z R B E T c d (.andI hz hc))
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold numerator lipschitz observationCost logGain GaussianRationalPowerDifference.budget GaussianNamedInverseRate.rateNumerator; ipra_ring)
    (.eqRefl _) both

theorem actual_original_Euler_logarithmic_multiplier_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      bounded (sample (var 0) (var 1) (var 2) (var 4) (var 7) (var 8)) (majorant (var 1) (var 3) (var 5) (var 6)) one) :=
  closeUniv 9 (.impI (original_sample_bound _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_Euler_logarithmic_order_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sample (var 0) zero (var 1) (var 2) (var 3) (var 4) ≐ GaussianEulerIntegrandName.sample (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (original_order_zero _ _ _ _ _)

theorem actual_original_Euler_logarithmic_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    (GaussianEulerExponentCompactBounds.input (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⟶
      distanceBounded (sample (var 0) (var 2) (var 3) (var 5) (var 8) (var 9)) (sample (var 1) (var 2) (var 3) (var 5) (var 10) (var 11))
        (numerator (var 0) (var 1) (var 2) (var 4) (var 6) (var 7) (var 12) (var 13))
        (GaussianNamedInverseRate.rateDenominator (var 13) (var 0) (var 1))) :=
  closeUniv 14 (.impI (original_variation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicMultiplier
