import IPRADerivations.Analysis.GaussianArctangentOriginalExponential
import IPRADerivations.Analysis.GaussianBoundedConstantProductName
import IPRADerivations.Analysis.GaussianBoundedIntegerExponentialSample
import IPRADerivations.Analysis.GaussianNamedSincSamples

/-!
# Actual cyclic exponential roots for an internal order

The original full-turn name is multiplied by the literal rational
coefficient r/m. The program raises its exponential to an internal
m-th power via the capped integer-exponential trace. The exact
named identity and its finite-sample residual share the same root
program for all orders and indices.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicExponentialRoots

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentExponentialPeriod (fullTurnF fullTurnData fullTurnRadius original_full_turn_input)
open GaussianBoundedConstantProductName (clock)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRadiusExponentialName (input)
open GaussianNamedSincSamples (common_late_distance)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents positive_product qmul
  represents_congr represents_rescale canonical_unique qzero zero_represents)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_congr natScale_represents natScale_canonical
  natural_point_represents natScale_as_product)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open GaussianRationalReciprocal (qone qone_bounded power bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_symmetric)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_left)
open GaussianReciprocalHorner (qmul_associative)
open GaussianNameEquivalence (crossEquivalent diagonal_at cross_to_diagonal cross_trans)
open GaussianNamedDiagonalRate (cross_of_diagonal_rate diagonalRate)
open GaussianRootAlgebra (equal_refl equal_of_values re_scale im_scale re_one im_one re_zero im_zero)
open ComplexLogarithmRemainder (scale oneCode zeroCode normSq normSq_scale normSq_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (r m : PTm n) : Fm PTm n := le one m ⋏ le r m
def coefficient (r m : PTm n) : PTm n := ofGaussian (scale r oneCode) m
def angleF : PR 2 := GaussianBoundedConstantProductName.nameF fullTurnF
def angleData (r m x : PTm n) : PTm n := GaussianBoundedConstantProductName.data one (coefficient r m) (fullTurnData x)
def rootF : PR 2 := GaussianRadiusExponentialName.nameF angleF
def rootData (r m x : PTm n) : PTm n := GaussianRadiusExponentialName.data fullTurnRadius (angleData r m x)
def sample (p r m x : PTm n) : PTm n := ap2 rootF p (rootData r m x)
def sampleRadius : PTm n := pw (num 3) fullTurnRadius

@[simp] theorem subst_sampleRadius {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (sampleRadius : PTm n) = (sampleRadius : PTm l) := by
  simp [sampleRadius,fullTurnRadius,GaussianArctangentExponentialPeriod.twiceRadius,GaussianArctangentQuarterExponential.radius]

@[simp] theorem subst_source {l : ℕ} (σ : Fin n → PTm l) (r m : PTm n) :
    (source r m).subst σ = source (Syn.subst σ r) (Syn.subst σ m) := by simp [source]
@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (r m : PTm n) :
    Syn.subst σ (coefficient r m) = coefficient (Syn.subst σ r) (Syn.subst σ m) := by
  simp [coefficient,oneCode]
@[simp] theorem subst_angleData {l : ℕ} (σ : Fin n → PTm l) (r m x : PTm n) :
    Syn.subst σ (angleData r m x) = angleData (Syn.subst σ r) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [angleData,fullTurnData,GaussianArctangentExponentialPeriod.twiceData]
@[simp] theorem subst_rootData {l : ℕ} (σ : Fin n → PTm l) (r m x : PTm n) :
    Syn.subst σ (rootData r m x) = rootData (Syn.subst σ r) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [rootData,fullTurnRadius,GaussianArctangentExponentialPeriod.twiceRadius,GaussianArctangentQuarterExponential.radius]
@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (p r m x : PTm n) :
    Syn.subst σ (sample p r m x) = sample (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [sample]

theorem coefficient_bound (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] bounded (coefficient r m) one one := by
  let a := scale r oneCode
  have en : Γ ⊢[PRAAx] normSq a ≐ r*r :=
    (normSq_scale r oneCode).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))
  apply bounded_of_cleared _ a m one one h.andE₁ (le_refl one) (ofGaussian_represents _ _ h.andE₁)
  exact le_congr (en.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring) (le_mul_mono h.andE₂ h.andE₂)

theorem angle_at (p r m x : PTm n) :
    Γ ⊢[PRAAx] ap2 angleF p (angleData r m x) ≐ qmul (coefficient r m) (ap2 fullTurnF (clock p one) (fullTurnData x)) :=
  GaussianBoundedConstantProductName.sample_at _ p one _ _

theorem angle_regular (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] pointCN angleF (angleData r m x) :=
  GaussianBoundedConstantProductName.name_regular _ one _ _
    (.andI (original_full_turn_input x).andE₁ (coefficient_bound r m h))

theorem angle_bound (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] bounded (ap2 angleF p (angleData r m x)) fullTurnRadius one :=
  bound_congr (angle_at p r m x).eqSymm (one_mul _) (one_mul one)
    (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _)
      (coefficient_bound r m h) (GaussianRadiusExponentialName.bounded_samples_at _ _ _ _ (original_full_turn_input x).andE₂))

theorem angle_input (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] input angleF fullTurnRadius (angleData r m x) := by
  refine .andI (angle_regular r m x h) (.allI ?_)
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (Syn.shift r) (Syn.shift m) := by simpa [Fm.shift,Syn.shift,Δ] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,subst_angleData,fullTurnRadius,
    GaussianArctangentExponentialPeriod.twiceRadius,GaussianArctangentQuarterExponential.radius,
    PTm.subst_add,one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Δ] using
    angle_bound (var 0) (Syn.shift r) (Syn.shift m) (Syn.shift x) hs

theorem root_regular (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] pointCN rootF (rootData r m x) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (angle_input r m x h)

theorem sample_bound (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] bounded (sample p r m x) sampleRadius one :=
  bound_congr (GaussianRadiusExponentialName.sample_at _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _
      (GaussianRadiusExponentialName.query_bound _ _ _ _ (angle_input r m x h)))

theorem coefficient_zero (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] coefficient zero m ≐ qzero := by
  have left := ofGaussian_represents (scale (zero : PTm n) oneCode) m hm
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (scale (zero : PTm n) oneCode) zeroCode := by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one,re_zero,im_zero] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ m (ofGaussian_canonical _ _ hm)
    (GaussianRationalSyntheticDivision.qzero_canonical) hm
    (represents_congr (.eqRefl _) e (.eqRefl _) left) (zero_represents _)

theorem sample_zero (p m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] sample p zero m x ≐ qone := by
  let d := angleData zero m x
  have a : Γ ⊢[PRAAx] ap2 angleF (GaussianRadiusExponentialName.inputPrecision fullTurnRadius p) d ≐ qzero :=
    (angle_at _ zero m x).eqTrans ((qmul_congr (coefficient_zero m hm) (.eqRefl _)).eqTrans (qmul_zero_left _))
  exact (GaussianRadiusExponentialName.sample_at angleF fullTurnRadius p d).eqTrans
    ((GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _) a).eqTrans
      (GaussianGammaCanonicalTailExponential.scalar_zero_point _))

theorem clear_coefficient (r m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] natScale m (coefficient r m) ≐ naturalPoint r := by
  let a := scale r oneCode
  have target := represents_rescale (naturalPoint r) a one m (natural_point_represents (Γ := Γ) r)
  exact canonical_unique _ _ _ m (natScale_canonical _ _) (ofGaussian_canonical _ _ (le_refl _)) hm
    (natScale_represents m _ a m hm (ofGaussian_represents _ _ hm))
    (represents_congr (.eqRefl _) (equal_refl _) (one_mul m) target)

def multipleF : PR 2 := GaussianNamedNaturalScale.nameF angleF
def multipleData (r m x : PTm n) : PTm n := GaussianNamedNaturalScale.data m m (angleData r m x)
def multipleRadius (m : PTm n) : PTm n := GaussianNamedNaturalScale.radius m fullTurnRadius
def cycleF : PR 2 := GaussianNamedNaturalScale.nameF fullTurnF
def cycleData (r x : PTm n) : PTm n := GaussianNamedNaturalScale.data r r (fullTurnData x)

@[simp] theorem subst_multipleData {l : ℕ} (σ : Fin n → PTm l) (r m x : PTm n) :
    Syn.subst σ (multipleData r m x) = multipleData (Syn.subst σ r) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [multipleData]
@[simp] theorem subst_cycleData {l : ℕ} (σ : Fin n → PTm l) (r x : PTm n) :
    Syn.subst σ (cycleData r x) = cycleData (Syn.subst σ r) (Syn.subst σ x) := by
  simp [cycleData,fullTurnData,GaussianArctangentExponentialPeriod.twiceData]

theorem multiple_at (p r m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 multipleF p (multipleData r m x) ≐
      natScale r (ap2 fullTurnF (clock (GaussianNamedNaturalScale.clock p m) one) (fullTurnData x)) := by
  let t := GaussianNamedNaturalScale.clock p m
  let w := ap2 fullTurnF (clock t one) (fullTurnData x)
  have scaled : Γ ⊢[PRAAx] natScale m (qmul (coefficient r m) w) ≐ natScale r w :=
    (natScale_as_product _ _).eqTrans ((qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr ((natScale_as_product _ _).eqSymm.eqTrans (clear_coefficient r m hm)) (.eqRefl _)).eqTrans
        (natScale_as_product _ _).eqSymm))
  exact (GaussianNamedNaturalScale.sample_at angleF p m m (angleData r m x)).eqTrans
    ((natScale_congr (.eqRefl _) (angle_at t r m x)).eqTrans scaled)

private theorem multiple_diagonal (p r m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 multipleF p (multipleData r m x))
      (ap2 cycleF p (cycleData r x)) (r*two) (unit p) := by
  let a := clock (GaussianNamedNaturalScale.clock p m) one
  let b := GaussianNamedNaturalScale.clock p r
  let y := fullTurnData x
  have hx := original_full_turn_input (Γ := Γ) x
  have diff := common_late_distance fullTurnF y p a b hx.andE₁
    (le_trans (GaussianNamedNaturalScale.clock_later p m) (le_add_right _ _)) (GaussianNamedNaturalScale.clock_later p r)
  have hd := GaussianNamedNaturalScale.scaled_distance r _ _ two (unit p) fullTurnRadius
    (unit_positive p) diff (GaussianRadiusExponentialName.bounded_samples_at _ _ _ b hx.andE₂)
  exact distance_congr (multiple_at p r m x hm).eqSymm
    (GaussianNamedNaturalScale.sample_at fullTurnF p r r y).eqSymm (.eqRefl _) (.eqRefl _) hd

theorem multiple_input (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] input multipleF (multipleRadius m) (multipleData r m x) :=
  GaussianNamedNaturalScale.exponential_input _ _ _ _ _ (angle_input r m x h) (le_refl _)

theorem cycle_input (r x : PTm n) :
    Γ ⊢[PRAAx] input cycleF (multipleRadius r) (cycleData r x) :=
  GaussianNamedNaturalScale.exponential_input _ _ _ _ _ (original_full_turn_input x) (le_refl _)

theorem multiple_cycle_cross (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] crossEquivalent multipleF cycleF (multipleData r m x) (cycleData r x) := by
  apply cross_of_diagonal_rate _ _ _ _ (r*two) (multiple_input r m x h).andE₁ (cycle_input r x).andE₁
  refine .allI ?_
  have hm : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift,one] using h.andE₁.shift
  simpa only [diagonalRate,Syn.shift,subst_multipleData,subst_cycleData,PTm.subst_mul,two,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    multiple_diagonal (var 0) (Syn.shift r) (Syn.shift m) (Syn.shift x) hm

theorem root_power_cross (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianRadiusExponentialName.nameF multipleF) constantF
      (GaussianRadiusExponentialName.data (multipleRadius m) (multipleData r m x)) qone := by
  have eq := GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (multiple_input r m x h) (cycle_input r x) (multiple_cycle_cross r m x h)
  have pow := GaussianBoundedIntegerExponential.integer_power_cross (Γ := Γ) fullTurnF r fullTurnRadius (fullTurnData x) qone one
    (.andI (original_full_turn_input x) (.andI (GaussianArctangentOriginalExponential.full_turn_cross x) qone_bounded))
  exact cross_trans _ _ _ _ _ _ eq (cross_trans _ _ _ _ _ _ pow
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (GaussianRationalRoundedPower.qone_power r)))

def powerBudget (m : PTm n) : PTm n :=
  GaussianBoundedIntegerExponentialSample.sampleBudget m m fullTurnRadius sampleRadius two+two

@[simp] theorem subst_powerBudget {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (powerBudget m) = powerBudget (Syn.subst σ m) := by
  simp [powerBudget,fullTurnRadius,GaussianArctangentExponentialPeriod.twiceRadius,GaussianArctangentQuarterExponential.radius]

theorem power_residual (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] distanceBounded (power (sample p r m x) m) qone (powerBudget m) (unit p) := by
  let F := GaussianBoundedIntegerExponentialStages.expF angleF
  let d := angleData r m x
  let c := sample p r m x
  let d₁ := GaussianBoundedIntegerExponentialStages.expData m one fullTurnRadius d
  let dₘ := GaussianBoundedIntegerExponentialStages.expData m m fullTurnRadius d
  have hp := unit_positive (Γ := Γ) p
  have hi := angle_input r m x h
  have oneEq := GaussianBoundedIntegerExponentialSample.one_cross angleF m fullTurnRadius d hi h.andE₁
  have base := diagonal_at F rootF d₁ (rootData r m x) p (cross_to_diagonal _ _ _ _ oneEq)
  have powered := GaussianBoundedIntegerExponentialSample.prefix_error angleF p m m fullTurnRadius d c sampleRadius two
    hi (sample_bound p r m x h) base (le_refl _)
  have last : Γ ⊢[PRAAx] distanceBounded (ap2 F p dₘ) qone two (unit p) :=
    distance_congr (.eqRefl _) (constant_at p qone) (.eqRefl _) (.eqRefl _)
    (diagonal_at F constantF dₘ qone p (cross_to_diagonal _ _ _ _ (root_power_cross r m x h)))
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_symmetric _ _ _ _ hp powered) last

theorem actual_cyclic_exponential_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 2) (var 1) ⟶ distanceBounded (power (sample (var 3) (var 2) (var 1) (var 0)) (var 1))
      qone (powerBudget (var 1)) (unit (var 3))) :=
  closeUniv 4 (.impI (power_residual _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCyclicExponentialRoots
