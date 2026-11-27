import IPRADerivations.Analysis.SpecialFunctions.LambertW.GaussianRobinLowerDecomposition
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaFiniteApproximantName

/-!
# Decomposition of the original mesh logarithm name

The original Robin clock is reinterpreted as an observation of each
actual odd name. The exact stored endpoint and the checked scalar
mesh comparison give the same logarithm as the named weighted sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRobinMeshLogDecomposition

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (eb dt st c3)
open GaussianRobinOddExponential (oddF constantF)
open GaussianRobinOddLogarithmName (inputs cutoff stored)
open GaussianRobinLowerDecomposition (exponentPoint lower)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiplyModulus add_fast multiply_fast)
open GaussianNameRingLaws (three add_sample_error multiply_sample_error sum_left_error product_right_error)
open GaussianGeneralFTAConstants (ceilL1 ceil_norm_bound)
open GaussianGammaCanonicalExponent (constant_at constant_regular)
open GaussianGammaFiniteApproximantName (logF log_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (point_at crossEquivalent)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def baseData : PTm n := inputs one c3
def reducedData (N : PTm n) : PTm n := inputs (dt N one) (st N one)
def integerF : PR 2 := multiplyF constantF oddF
def integerData (N : PTm n) : PTm n := multiplyData constantF oddF (exponentPoint N one) baseData
def nameF : PR 2 := addF integerF oddF
def data (N : PTm n) : PTm n := addData (integerData N) (reducedData N)
def index (p N : PTm n) : PTm n := p+pred N
def raw (p N : PTm n) : PTm n :=
  qadd (qmul (exponentPoint N one) (ap2 oddF p baseData)) (ap2 oddF p (reducedData N))
def arithmeticBudget (N : PTm n) : PTm n := three+(multiplyModulus constantF oddF (exponentPoint N one) baseData+one)
def retimeBudget (N : PTm n) : PTm n := ceilL1 (exponentPoint N one)*two+two
def budget (N : PTm n) : PTm n := (arithmeticBudget N+retimeBudget N)+two

ipra_subst baseData [inputs]
ipra_subst reducedData [inputs]
ipra_subst exponentPoint [LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval.eb, LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval.ebB]
ipra_subst data [integerData]
ipra_subst budget [arithmeticBudget, retimeBudget, ceilL1, three, two, one]

theorem base_regular : Γ ⊢[PRAAx] pointCN oddF (baseData : PTm n) :=
  GaussianRobinOddLogarithmName.name_regular one c3
    (.andI (le_of_eq_add (d := two) (by ipra_ring)) (le_of_eq_add (d := one) (by ipra_ring)))
theorem reduced_regular (N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN oddF (reducedData N) :=
  GaussianRobinOddLogarithmName.name_regular _ _ (GaussianRobinLogRangeReduction.reduced_source N one (le_refl _) h)
theorem integer_regular (N : PTm n) :
    Γ ⊢[PRAAx] pointCN integerF (integerData N) :=
  multiply_fast _ _ _ _ (constant_regular _) base_regular
theorem name_regular (N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN nameF (data N) :=
  add_fast _ _ _ _ (integer_regular N) (reduced_regular N h)

theorem clock_exact (p N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GammaMeshRobinLogBridge.robinClock N p ≐ cutoff (index p N) := by
  have e := natEq (LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep.pos_of_one_le h)
  unfold GammaMeshRobinLogBridge.robinClock cutoff index
  apply deriveNat
  ipra_simps
  rw [e]
  ring

private theorem stored_congr (a b : PTm n) {K L : PTm n} (h : Γ ⊢[PRAAx] K ≐ L) :
    Γ ⊢[PRAAx] stored K a b ≐ stored L a b := by
  open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Nz_congr Dz_congr) in
  ipra_congr (RationalGaussianEmbedding.embed (RationalCubeMidpoint.fraction (var 0) (var 1)) : PTm 2) with
    [Nz_congr a b h, Dz_congr a b h] using [stored]

theorem original_lower_at (p N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] lower N one (GammaMeshRobinLogBridge.robinClock N p) ≐ raw (index p N) N := by
  let K := GammaMeshRobinLogBridge.robinClock N p
  let r := index p N
  have bind (a b : PTm n) : Γ ⊢[PRAAx] stored K a b ≐ ap2 oddF r (inputs a b) :=
    (stored_congr a b (clock_exact p N h)).eqTrans (GaussianRobinOddLogarithmName.point_at r a b).eqSymm
  exact (GaussianRobinLowerDecomposition.original_lower_decomposition N one K (le_refl one) h).eqTrans
    (qadd_congr (qmul_congr (.eqRefl _) (bind one c3)) (bind (dt N one) (st N one)))

theorem named_arithmetic_error (p N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data N)) (raw p N) (arithmeticBudget N) (unit p) := by
  let e := exponentPoint N one
  let y := reducedData N
  have first := add_sample_error integerF oddF (integerData N) y p (integer_regular N) (reduced_regular N h)
  have product := multiply_sample_error constantF oddF e baseData p (constant_regular (Γ := Γ) e) base_regular
  have shifted := distance_congr (.eqRefl _)
    (qmul_congr (constant_at p e) (.eqRefl _)) (.eqRefl _) (.eqRefl _) product
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) first
    (sum_left_error _ _ (ap2 oddF p y) _ _ (unit_positive p) shifted)

theorem later_sample (f : PR 2) (p q x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 f q x) two (unit p) := by
  have u := unit_positive (Γ := Γ) p
  have v := unit_positive (Γ := Γ) q
  have hv : Γ ⊢[PRAAx] le (unit p) (unit q) := GaussianBalancedRadiusArithmetic.unit_monotone p q hpq
  have comp := mul_le_mul_right (unit p) (add_le_add₂ hv (le_refl (unit q)))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ u v) u
    (le_congr (.eqRefl _) (by ipra_ring) comp) (point_at f x p q h)

theorem retime_error (p N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (raw p N) (raw (index p N) N) (retimeBudget N) (unit p) := by
  let r := index p N
  let e := exponentPoint N one
  let y := reducedData N
  have hp := unit_positive (Γ := Γ) p
  have hpr : Γ ⊢[PRAAx] le p r := le_add_right _ _
  have a := later_sample oddF p r baseData base_regular hpr
  have b := later_sample oddF p r y (reduced_regular N h) hpr
  have hx := GaussianNameBounds.sample_bound oddF (baseData : PTm n) p (base_regular (Γ := Γ))
  have ah := product_right_error e _ _ two _ _ _ hp a hx (ceil_norm_bound e)
  exact GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hp ah b

theorem mesh_lower_error (p N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 logF p N) (lower N one (GammaMeshRobinLogBridge.robinClock N p)) two (unit p) := by
  let m := GammaMeshRobinLogBridge.meshLogSample p N
  let r := GammaMeshRobinLogBridge.robinLogSample p N
  let y := GammaMeshRobinLogBridge.robinValue N (GammaMeshRobinLogBridge.robinClock N p)
  have up := unit_positive (Γ := Γ) p
  have uq := positive_product _ _ up up
  have error : Γ ⊢[PRAAx] distanceBounded
      (RationalGaussianEmbedding.embed m) (RationalGaussianEmbedding.embed r) (unit p+unit p) (unit p*unit p) :=
    RationalGaussianNameEmbedding.distance_from_radius m r _ _ uq
      (GammaMeshRobinLogBridge.cross_compatibility N p p h)
  have e : Γ ⊢[PRAAx] RationalGaussianEmbedding.embed r ≐ RationalGaussianEmbedding.embed y := by
    ipra_congr (RationalGaussianEmbedding.embed (var 0) : PTm 1) with [GammaMeshRobinLogBridge.robin_log_at p N]
  exact distance_congr (RationalGaussianNameEmbedding.sample_at GammaMeshRobinLogBridge.meshLogF p N).eqSymm
    e (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ uq up (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) error)

theorem mesh_name_error (p N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data N)) (ap2 logF p N) (budget N) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have first := distance_triangle_same _ _ _ _ _ _ hp (named_arithmetic_error p N h) (retime_error p N h)
  have last := distance_congr (.eqRefl _) (original_lower_at p N h) (.eqRefl _) (.eqRefl _) (mesh_lower_error p N h)
  exact distance_triangle_same _ _ _ _ _ _ hp first (distance_symmetric _ _ _ _ hp last)

theorem original_mesh_decomposition (N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent nameF logF (data N) N := by
  refine GaussianNameRingLaws.equivalent_of_envelope nameF logF (data N) N (budget N)
    (name_regular N h) (log_regular N h) (.allI ?_)
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [Syn.shift,subst_data,subst_budget] using mesh_name_error (var 0) (Syn.shift N) hn

theorem original_mesh_log_binary_decomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ crossEquivalent nameF logF (data (var 0)) (var 0)) :=
  closeUniv 1 (.impI (original_mesh_decomposition _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRobinMeshLogDecomposition
