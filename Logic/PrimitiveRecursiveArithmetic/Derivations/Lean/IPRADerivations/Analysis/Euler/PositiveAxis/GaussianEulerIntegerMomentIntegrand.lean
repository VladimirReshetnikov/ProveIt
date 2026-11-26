import IPRADerivations.Analysis.Euler.GaussianHarmonicIntegerExponential
import IPRADerivations.Analysis.Euler.GaussianEulerParameterExponentialIncrement
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicInputProperness
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaShiftTrajectory

/-!
# Integer moment rows are original shifted Euler integrands

The original parameter-addition law at the native natural N is combined
with the checked original exp(N log t)=t^N theorem. Exact native input
properness binds the result to the same original N-step trajectory.
Every moment order is internal, including zero. No Gamma or integral
moment identity is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegerMomentIntegrand

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (nameF data name_regular)
open GaussianGammaShiftTrajectory (point)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (power)
open GaussianCoefficientNameBounds (unit)
open ComplexLogarithmRemainder (oneCode scale)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (B a b E T : PTm n) : Fm PTm n := le one B ⋏ GaussianHarmonicIntegerExponential.source a b E T
def monomial (N a b : PTm n) : PTm n := power (GaussianPositiveRationalLogarithm.fraction a b) N
def momentF : PR 2 := multiplyF constantF nameF
def momentData (z B N a b : PTm n) : PTm n := multiplyData constantF nameF (monomial N a b) (data z B a b)
def shiftedData (z B N a b : PTm n) : PTm n := data (point z B N) B a b
def clock (p z B N a b : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF nameF (monomial N a b) (data z B a b)) p

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (B a b E T : PTm n) :
    (source B a b E T).subst σ = source (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ E) (Syn.subst σ T) := by simp [source]
@[simp] theorem subst_monomial {m : ℕ} (σ : Fin n → PTm m) (N a b : PTm n) :
    Syn.subst σ (monomial N a b) = monomial (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [monomial]
@[simp] theorem subst_momentData {m : ℕ} (σ : Fin n → PTm m) (z B N a b : PTm n) :
    Syn.subst σ (momentData z B N a b) = momentData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [momentData]
@[simp] theorem subst_shiftedData {m : ℕ} (σ : Fin n → PTm m) (z B N a b : PTm n) :
    Syn.subst σ (shiftedData z B N a b) = shiftedData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [shiftedData]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p z B N a b : PTm n) :
    Syn.subst σ (clock p z B N a b) = clock (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [clock]

theorem time_source (z B a b E T : PTm n) (h : Γ ⊢[PRAAx] source B a b E T) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.source z B a b := .andI h.andE₁ h.andE₂.andE₂.andE₁

theorem native_parameter (z B N : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (point z B N)
    (GaussianEulerParameterExponentialIncrement.shifted z B (scale N oneCode) one) := by
  apply GaussianRootAlgebra.equal_trans (GaussianGammaShiftTrajectory.point_native z B N)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianGammaEulerHeadLower.translated,GaussianEulerParameterExponentialIncrement.shifted,
      GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals ipra_simps; ring

theorem shifted_fraction_equal (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    ofGaussian (point z B N) B ≐ ofGaussian (GaussianEulerParameterExponentialIncrement.shifted z B (scale N oneCode) one) (B*one) :=
  (GaussianGammaFiniteValueProperness.fraction_equal _ _ B hB (native_parameter z B N)).eqTrans
    (GaussianGammaEncodingRescaling.fraction_denominator_congr _ B (B*one) (by ipra_ring))

theorem increment_is_monomial (N a b E T : PTm n) (h : Γ ⊢[PRAAx] GaussianHarmonicIntegerExponential.source a b E T) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEulerParameterExponentialIncrement.exponentialF constantF
      (GaussianEulerParameterExponentialIncrement.exponentialData (scale N oneCode) one a b) (monomial N a b) := by
  change Γ ⊢[PRAAx] crossEquivalent GaussianHarmonicIntegerExponential.originalExpF constantF
    (GaussianHarmonicIntegerExponential.originalData N a b) (monomial N a b)
  exact cross_trans _ _ _ _ _ _ (GaussianHarmonicIntegerExponential.original_integer_exponential N a b E T h)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
      (GaussianHarmonicIntegerExponential.actual_rational_power a b N h.andE₂.andE₁.andE₂).eqSymm)

theorem monomial_bound (N a b E T : PTm n) (h : Γ ⊢[PRAAx] GaussianHarmonicIntegerExponential.source a b E T) : Γ ⊢[PRAAx]
    bounded (monomial N a b) (pw T N) one :=
  GaussianRationalReciprocal.bound_congr (GaussianHarmonicIntegerExponential.actual_rational_power a b N h.andE₂.andE₁.andE₂).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianHarmonicIntegerExponential.rational_power_top_bound N a b E T h)

theorem moment_regular (z B N a b E T : PTm n) (h : Γ ⊢[PRAAx] source B a b E T) : Γ ⊢[PRAAx]
    pointCN momentF (momentData z B N a b) := multiply_fast _ _ _ _ (constant_regular _)
      (name_regular z B a b (time_source z B a b E T h))

/-- The SAME original Euler evaluator at z/B+N is the original t^N
times the original Euler evaluator at z/B, at their actual named clocks. -/
theorem original_pointwise (z B N a b E T : PTm n) (h : Γ ⊢[PRAAx] source B a b E T) : Γ ⊢[PRAAx]
    crossEquivalent nameF momentF (shiftedData z B N a b) (momentData z B N a b) := by
  let Z := GaussianEulerParameterExponentialIncrement.shifted z B (scale N oneCode) one
  let X := data z B a b
  let Y := GaussianEulerParameterExponentialIncrement.exponentialData (scale N oneCode) one a b
  let I := GaussianEulerParameterExponentialIncrement.exponentialF
  let c := monomial N a b
  have ht := time_source z B a b E T h
  have moved : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source Z (B*one) a b :=
    .andI (positive_product _ _ h.andE₁ (le_refl one)) ht.andE₂
  have exactData := GaussianEulerLogarithmicInputProperness.integrand_data_equal _ _ _ _ a b (shifted_fraction_equal z B N h.andE₁)
  have first := GaussianGammaInputProperness.code_data_cross nameF (shiftedData z B N a b) (data Z (B*one) a b)
    (name_regular _ _ _ _ ht) (name_regular _ _ _ _ moved) exactData
  have product := GaussianEulerParameterExponentialIncrement.original_integrand_product z B (scale N oneCode) one a b ht (le_refl one)
  have hx := name_regular z B a b ht
  have hi := GaussianEulerParameterExponentialIncrement.exponential_regular (scale N oneCode) one a b ht.andE₂
  have hc := constant_regular (Γ := Γ) c
  have replace := GaussianGammaAdjacentCutoff.multiply_cross nameF nameF I constantF X X Y c hx hx hi hc
    (cross_refl _ _ hx) (increment_is_monomial N a b E T h.andE₂)
  have swap := GaussianNameRingLaws.multiply_commutative nameF constantF X c hx hc
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ product (cross_trans _ _ _ _ _ _ replace swap))

theorem moment_sample (p z B N a b : PTm n) : Γ ⊢[PRAAx]
    ap2 momentF p (momentData z B N a b) ≐ qmul (monomial N a b) (ap2 nameF (clock p z B N a b) (data z B a b)) :=
  (GaussianNameArithmetic.multiply_at constantF nameF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem original_observations (p q z B N a b E T : PTm n) (h : Γ ⊢[PRAAx] source B a b E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (shiftedData z B N a b)) (ap2 momentF q (momentData z B N a b))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_pointwise z B N a b E T h)

theorem actual_original_Euler_integer_moment_integrand_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 3) (var 4) (var 5) (var 6) ⟶ crossEquivalent nameF momentF
      (shiftedData (var 0) (var 1) (var 2) (var 3) (var 4)) (momentData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 7 (.impI (original_pointwise _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_Euler_integer_moment_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (ap2 momentF (var 0) (momentData (var 1) (var 2) (var 3) (var 4) (var 5)) ≐
      qmul (monomial (var 3) (var 4) (var 5)) (ap2 nameF (clock (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (data (var 1) (var 2) (var 4) (var 5)))) := closeUniv 6 (moment_sample _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerIntegerMomentIntegrand
