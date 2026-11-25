import IPRADerivations.Analysis.GaussianPositiveRationalLogarithm
import IPRADerivations.Analysis.GaussianPositiveExponentialMajorant
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual positive-time complex powers and Euler integrand observations

The time is the original positive natural fraction a/b. The complex
parameter is the native Gaussian fraction z/B. The power exponent is
(z/B-1)*log(a/b), with the genuine positive rational logarithm name.
Adding the constant -a/b and using the unchanged scalarSum program
implements t^(z-1)*exp(-t). Every disk is computed from actual initial
observations. Regularity and the power-times-decay identity follow from
checked original operations, without an integrand-value/rate premise.
Uniform interval bounds, finite derivative bounds and improper tails
are separate analytic obligations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrandName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianRationalHorner (ofGaussian qmul qadd)
open GaussianRationalMetric (qsub qnegative bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev logarithmF : PR 2 := GaussianPositiveRationalLogarithm.logF

def coefficient (z B : PTm n) : PTm n := qsub (ofGaussian z B) GaussianRationalSyntheticDivision.qone
def powerExponentF : PR 2 := multiplyF constantF logarithmF
def powerExponentData (z B a b : PTm n) : PTm n :=
  multiplyData constantF logarithmF (coefficient z B) (GaussianPositiveRationalLogarithm.data a b)
def powerRadius (z B a b : PTm n) : PTm n := GaussianNameBounds.U powerExponentF (powerExponentData z B a b)
def powerF : PR 2 := GaussianRadiusExponentialName.nameF powerExponentF
def powerData (z B a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (powerRadius z B a b) (powerExponentData z B a b)
def decayPoint (a b : PTm n) : PTm n := qnegative (GaussianPositiveRationalLogarithm.fraction a b)
def decayF : PR 2 := GaussianRadiusExponentialName.nameF constantF
def decayData (a b : PTm n) : PTm n :=
  GaussianGammaFiniteApproximantName.exponentialInputData constantF (decayPoint a b)
def exponentF : PR 2 := addF powerExponentF constantF
def exponentData (z B a b : PTm n) : PTm n := addData (powerExponentData z B a b) (decayPoint a b)
def radius (z B a b : PTm n) : PTm n := GaussianNameBounds.U exponentF (exponentData z B a b)
def nameF : PR 2 := GaussianRadiusExponentialName.nameF exponentF
def data (z B a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius z B a b) (exponentData z B a b)
def source (_z B a b : PTm n) : Fm PTm n := le one B ⋏ GaussianPositiveRationalLogarithm.source a b
def productF : PR 2 := multiplyF powerF decayF
def productData (z B a b : PTm n) : PTm n := multiplyData powerF decayF (powerData z B a b) (decayData a b)
def powerClock (p z B a b : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF logarithmF (coefficient z B) (GaussianPositiveRationalLogarithm.data a b)) p

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (coefficient z B) = coefficient (Syn.subst σ z) (Syn.subst σ B) := by simp [coefficient]
@[simp] theorem subst_powerExponentData {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (powerExponentData z B a b) = powerExponentData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [powerExponentData]
@[simp] theorem subst_powerRadius {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (powerRadius z B a b) = powerRadius (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [powerRadius]
@[simp] theorem subst_powerData {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (powerData z B a b) = powerData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [powerData]
@[simp] theorem subst_decayPoint {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (decayPoint a b) = decayPoint (Syn.subst σ a) (Syn.subst σ b) := by simp [decayPoint]
@[simp] theorem subst_exponentData {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (exponentData z B a b) = exponentData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [exponentData]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (radius z B a b) = radius (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [radius]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (data z B a b) = data (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [data]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    (source z B a b).subst σ = source (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [source]
@[simp] theorem subst_powerClock {m : ℕ} (σ : Fin n → PTm m) (p z B a b : PTm n) :
    Syn.subst σ (powerClock p z B a b) = powerClock (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [powerClock]

theorem power_exponent_regular (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) :
    Γ ⊢[PRAAx] pointCN powerExponentF (powerExponentData z B a b) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianPositiveRationalLogarithm.name_regular a b h.andE₂)
theorem exponent_regular (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) :
    Γ ⊢[PRAAx] pointCN exponentF (exponentData z B a b) :=
  add_fast _ _ _ _ (power_exponent_regular z B a b h) (constant_regular _)
theorem power_input (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input powerExponentF (powerRadius z B a b) (powerExponentData z B a b) :=
  GaussianGammaFiniteApproximantName.exponential_input _ _ (power_exponent_regular z B a b h)
theorem exponent_input (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input exponentF (radius z B a b) (exponentData z B a b) :=
  GaussianGammaFiniteApproximantName.exponential_input _ _ (exponent_regular z B a b h)
theorem power_regular (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx] pointCN powerF (powerData z B a b) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (power_input z B a b h)
theorem name_regular (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx] pointCN nameF (data z B a b) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponent_input z B a b h)

theorem power_exponent_at (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 powerExponentF p (powerExponentData z B a b) ≐ qmul (coefficient z B)
      (GaussianPositiveRationalLogarithm.sample (powerClock p z B a b) a b) :=
  (GaussianNameArithmetic.multiply_at constantF logarithmF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem exponent_at (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 exponentF p (exponentData z B a b) ≐ qadd
      (qmul (coefficient z B) (GaussianPositiveRationalLogarithm.sample
        (powerClock (GaussianFastValueCut.exponent two p) z B a b) a b)) (decayPoint a b) :=
  (GaussianNameArithmetic.add_at powerExponentF constantF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qadd_congr
      (power_exponent_at _ z B a b) (constant_at _ _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)))

theorem original_power_times_decay (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent productF nameF (productData z B a b) (data z B a b) :=
  GaussianGammaFoldedApproximantBalance.exponential_product_equivalent powerExponentF constantF exponentF
    (powerRadius z B a b) (GaussianNameBounds.U constantF (decayPoint a b)) (radius z B a b)
    (powerExponentData z B a b) (decayPoint a b) (exponentData z B a b) (power_input z B a b h)
    (GaussianGammaFiniteApproximantName.exponential_input _ _ (constant_regular _)) (exponent_input z B a b h)
    (cross_refl exponentF (exponentData z B a b) (exponent_regular z B a b h))

/-- The actual fixed-arity Euler evaluator receives p, the positive
fraction pair (a,b), and the fixed complex input pair (z,B). -/
def timeData (a b : PTm n) : PTm n := pairT a b
def fixedData (z B : PTm n) : PTm n := pairT z B
def evaluatorTerm (p t x : PTm n) : PTm n := ap2 nameF p (data (fstT x) (sndT x) (fstT t) (sndT t))
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def sample (p z B a b : PTm n) : PTm n := ap3 evaluatorF p (timeData a b) (fixedData z B)
@[simp] theorem subst_evaluatorTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (evaluatorTerm p t x) = evaluatorTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by simp [evaluatorTerm]
@[simp] theorem subst_timeData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (timeData a b) = timeData (Syn.subst σ a) (Syn.subst σ b) := by simp [timeData]
@[simp] theorem subst_fixedData {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (fixedData z B) = fixedData (Syn.subst σ z) (Syn.subst σ B) := by simp [fixedData]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z B a b : PTm n) :
    Syn.subst σ (sample p z B a b) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [sample]

theorem evaluator_at (p t x : PTm n) : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ evaluatorTerm p t x := by
  simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]
theorem sample_at (p z B a b : PTm n) : Γ ⊢[PRAAx] sample p z B a b ≐ ap2 nameF p (data z B a b) := by
  refine (evaluator_at p (timeData a b) (fixedData z B)).eqTrans ?_
  ipra_congr (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4)) : PTm 5) with
    [.eqRefl p, (show _ ⊢[PRAAx] fstT (fixedData z B) ≐ z from fst_pair _ _),
      (show _ ⊢[PRAAx] sndT (fixedData z B) ≐ B from snd_pair _ _),
      (show _ ⊢[PRAAx] fstT (timeData a b) ≐ a from fst_pair _ _),
      (show _ ⊢[PRAAx] sndT (timeData a b) ≐ b from snd_pair _ _)] using [evaluatorTerm]

theorem sample_canonical (p z B a b : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample p z B a b) :=
  GaussianRationalHorner.canonical_congr (sample_at p z B a b) (GaussianRadiusExponentialName.sample_canonical _ _ _ _)
theorem sample_regularity (p q z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (sample p z B a b) (sample q z B a b) (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (sample_at p z B a b).eqSymm (sample_at q z B a b).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.point_at nameF (data z B a b) p q (name_regular z B a b h))
def cutoff (p z B a b : PTm n) : PTm n := GaussianRadiusExponentialName.index (radius z B a b) p
def exponentClock (p z B a b : PTm n) : PTm n := GaussianRadiusExponentialName.inputPrecision (radius z B a b) p
def logarithmClock (p z B a b : PTm n) : PTm n := powerClock (GaussianFastValueCut.exponent two (exponentClock p z B a b)) z B a b

theorem sample_original_sum (p z B a b : PTm n) : Γ ⊢[PRAAx] sample p z B a b ≐
    GaussianRationalPolynomialExponential.scalarSum
      (ap2 exponentF (exponentClock p z B a b) (exponentData z B a b)) (cutoff p z B a b) :=
  (sample_at p z B a b).eqTrans (GaussianRadiusExponentialName.sample_at exponentF (radius z B a b) p (exponentData z B a b))

/-- Literal nested finite observations, retaining the actual exponential
cutoff and every multiplication/addition/logarithm query clock. -/
theorem sample_finite (p z B a b : PTm n) : Γ ⊢[PRAAx] sample p z B a b ≐
    GaussianRationalPolynomialExponential.scalarSum
      (qadd (qmul (coefficient z B) (GaussianPositiveRationalLogarithm.sample (logarithmClock p z B a b) a b))
        (decayPoint a b)) (cutoff p z B a b) :=
  (sample_original_sum p z B a b).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _)
      (exponent_at (exponentClock p z B a b) z B a b))

theorem sample_bound (p z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    bounded (sample p z B a b) (pw (LeanProofs.IPRA.PTm.num 3) (radius z B a b)) one := by
  have query := GaussianRadiusExponentialName.query_bound exponentF (radius z B a b) (exponentData z B a b) p (exponent_input z B a b h)
  have bound := GaussianPositiveExponentialMajorant.disk_bound _ (radius z B a b) (cutoff p z B a b) query
  exact GaussianRationalReciprocal.bound_congr (sample_original_sum p z B a b).eqSymm (.eqRefl _) (.eqRefl _) bound



theorem coefficient_represents (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianRationalHorner.represents (coefficient z B)
      (GaussianRootAlgebra.sub z (ComplexLogarithmRemainder.scale B ComplexLogarithmRemainder.oneCode)) B :=
  GaussianRationalMetric.qsub_represents _ _ _ _ _ hB (GaussianRationalHorner.ofGaussian_represents z B hB)
    (GaussianRationalReciprocal.qone_represents_scaled B)

theorem coefficient_bound (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx] bounded (coefficient z B) (R+one) one :=
  GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_difference _ _ R one one one (le_refl _) (le_refl _)
      (GaussianGammaEulerHead.fraction_disk z R B hB hz) GaussianRationalReciprocal.qone_bounded)

theorem decay_point_bound (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] bounded (decayPoint a b) a one := by
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) ≐ a*a :=
    (ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  have clear := mul_le_mul_right (a*a) (sq_le_sq hb)
  have fractionBound : Γ ⊢[PRAAx] bounded (GaussianPositiveRationalLogarithm.fraction a b) a one :=
    GaussianRationalMetric.bounded_of_cleared _ _ b a one hb (le_refl _) (GaussianRationalHorner.ofGaussian_represents _ _ hb)
      (le_congr (congrMul (.eqRefl (one*one)) norm).eqSymm (by ipra_ring) clear)
  exact GaussianRationalReciprocal.bounded_negative _ a one (le_refl _) fractionBound

/-- A source-input disk bound for the actual exponent observations.
Its logarithm radius is an actual computed term, not a supplied norm law. -/
theorem source_exponent_bound (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    bounded (ap2 exponentF p (exponentData z B a b))
      ((R+one)*GaussianPositiveRationalLogarithm.radius a b+a) one := by
  have actual := GaussianRationalReciprocal.bounded_product _ _ (R+one) one
    (GaussianPositiveRationalLogarithm.radius a b) one (le_refl _) (le_refl _) (coefficient_bound z R B h.andE₁ hz)
    (GaussianPositiveRationalLogarithm.sample_bound (powerClock (GaussianFastValueCut.exponent two p) z B a b) a b h.andE₂)
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ (one*one) a one
    (GaussianRationalHorner.positive_product _ _ (le_refl one) (le_refl one)) (le_refl one)
    actual (decay_point_bound a b h.andE₂.andE₂)
  exact GaussianRationalReciprocal.bound_congr (exponent_at p z B a b).eqSymm (by ipra_ring) (by ipra_ring) sum

theorem actual_Euler_integrand_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular _ _ _ _ Prf.hyp0))
theorem actual_positive_time_power_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN powerF (powerData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (power_regular _ _ _ _ Prf.hyp0))
theorem original_positive_time_power_times_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent productF nameF
      (productData (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_power_times_decay _ _ _ _ Prf.hyp0))
theorem actual_Euler_integrand_evaluator_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 evaluatorF (var 0) (var 1) (var 2) ≐ evaluatorTerm (var 0) (var 1) (var 2)) := closeUniv 3 (evaluator_at _ _ _)
theorem actual_Euler_integrand_sample_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) ≐ ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (sample_at _ _ _ _ _)
theorem actual_Euler_integrand_finite_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) ≐ GaussianRationalPolynomialExponential.scalarSum
      (qadd (qmul (coefficient (var 1) (var 2)) (GaussianPositiveRationalLogarithm.sample
        (logarithmClock (var 0) (var 1) (var 2) (var 3) (var 4)) (var 3) (var 4))) (decayPoint (var 3) (var 4)))
      (cutoff (var 0) (var 1) (var 2) (var 3) (var 4))) := closeUniv 5 (sample_finite _ _ _ _ _)
theorem actual_Euler_integrand_sample_regularity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶ GaussianRationalMetric.distanceBounded
      (sample (var 0) (var 2) (var 3) (var 4) (var 5)) (sample (var 1) (var 2) (var 3) (var 4) (var 5))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (sample_regularity _ _ _ _ _ _ Prf.hyp0))
theorem actual_Euler_integrand_computed_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶ bounded (sample (var 0) (var 1) (var 2) (var 3) (var 4))
      (pw (LeanProofs.IPRA.PTm.num 3) (radius (var 1) (var 2) (var 3) (var 4))) one) :=
  closeUniv 5 (.impI (sample_bound _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrandName
