import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.Denominators.GaussianGammaEulerRationalHead
import IPRADerivations.Analysis.Gamma.HalfInteger.EulerProducts.GaussianGammaHalfEulerSquare
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerRealSamples
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingLogDuplication

/-!
# Logarithm of the original finite Euler approximation to Gamma

For positive rational x, the logarithm uses the actual Euler exponent
with its sign reversed and the original positive rational logarithm of
the exact reciprocal head. Exponentiation recovers the original
inverse Euler name and its literal full-head representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLog

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerFullHeadInverse (headInverse)
open GaussianGammaEulerRationalHead (numerator denominator numerator_positive denominator_positive returned_head_fraction)
open GaussianGammaFiniteApproximantName
  (logF logExponentF logExponentData exponentialInputData exponential_input log_exponent_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian_canonical)
open GaussianRationalMetric (qnegative qnegative_canonical)
open GaussianRationalReciprocal (reciprocal_canonical)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingGammaLogarithm (arg)
open GaussianStirlingLogDuplication (exponential_sum exponential_regular)
open GaussianStirlingNames (add_real constant_real fraction_axis multiply_real)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "L" => GaussianPositiveRationalLogarithm.logF
local notation "ld" => GaussianPositiveRationalLogarithm.data
local notation "I" => GaussianGammaEulerFullHeadInverse.nameF
local notation "idData" => GaussianGammaEulerFullHeadInverse.data

abbrev powerF : PR 2 := negativeF logExponentF
def powerData (N a b : PTm n) : PTm n := negativeData (logExponentData (arg a) b N)
def headLogData (N a b : PTm n) : PTm n := ld (denominator N b) (numerator (succ N) a b)
def nameF : PR 2 := addF powerF L
def data (N a b : PTm n) : PTm n := addData (powerData N a b) (headLogData N a b)
def expData (N a b : PTm n) : PTm n := ed nameF (data N a b)

ipra_subst powerData [logExponentData, arg]
ipra_subst headLogData
ipra_subst data
ipra_subst expData [GaussianGammaFiniteApproximantName.exponentialInputData]

theorem head_log_source (N a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (denominator N b) (numerator (succ N) a b) :=
  .andI (denominator_positive N b hb) (numerator_positive (succ N) a b ha)

theorem power_regular (N a b : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN powerF (powerData N a b) :=
  negative_fast _ _ (log_exponent_regular (arg a) b N hN)

theorem name_regular (N a b : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] pointCN nameF (data N a b) :=
  add_fast _ _ _ _ (power_regular N a b hN)
    (GaussianPositiveRationalLogarithm.name_regular _ _ (head_log_source N a b ha hb))

private theorem base_real (N : PTm n) : Γ ⊢[PRAAx] realSamples logF N :=
  .allI (by
    simpa only [realSamples,Syn.shift,logF,RationalGaussianNameEmbedding.sample] using
      Prf.andI (RationalGaussianNameEmbedding.sample_canonical GammaMeshRobinLogBridge.meshLogF (var 0) (Syn.shift N))
        (RationalGaussianNameEmbedding.sample_axis GammaMeshRobinLogBridge.meshLogF (var 0) (Syn.shift N)))

private theorem rational_log_real (A B : PTm n) : Γ ⊢[PRAAx] realSamples L (ld A B) :=
  .allI (by
    simpa only [realSamples,Syn.shift,GaussianPositiveRationalLogarithm.subst_data,GaussianPositiveRationalLogarithm.sample] using
      Prf.andI (GaussianPositiveRationalLogarithm.sample_canonical (var 0) (Syn.shift A) (Syn.shift B))
        (GaussianPositiveRationalLogarithm.sample_axis (var 0) (Syn.shift A) (Syn.shift B)))

theorem power_real (N a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realSamples powerF (powerData N a b) := by
  have h : Γ ⊢[PRAAx] realSamples constantF (qnegative (fraction a b)) :=
    constant_real _ (qnegative_canonical _) (RationalGaussianEmbedding.axis_negative _ (fraction_axis a b hb))
  exact GaussianNamedDampingPowerRealSamples.negative_real _ _
    (multiply_real logF constantF N _ (base_real N) h)

theorem name_real (N a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realSamples nameF (data N a b) :=
  add_real _ _ _ _ (power_real N a b hb) (rational_log_real _ _)

theorem head_inverse_code (N a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] headInverse (arg a) b N ≐ fraction (denominator N b) (numerator (succ N) a b) := by
  let A := numerator (succ N) a b
  let B := denominator N b
  let z := arg a
  let q := GaussianGammaEulerHead.run z b N
  have hs := GaussianStirlingGammaLogarithm.gamma_source a b (.andI ha hb)
  have guard := GaussianGammaEulerFullHeadInverse.extended_guard z a b one b N hs
  have native := GaussianGammaEulerHeadLower.returned_inverse_identity z b one b N hb (le_refl one) hb guard
  have hA := numerator_positive (succ N) a b ha
  have hB := denominator_positive N b hb
  have inv := GaussianGammaHalfEulerSquare.inverse_fraction A B hA hB
  have eq := (qmul_congr (returned_head_fraction N a b hb) (.eqRefl (fraction B A))).eqTrans inv
  exact GaussianEulerBetaProductPascal.inverse_unique q _ _
    (reciprocal_canonical q) (ofGaussian_canonical _ _ hA) native eq

theorem exponential_cross (N a b : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (E nameF) I (expData N a b) (idData (arg a) b N) := by
  let A := numerator (succ N) a b
  let B := denominator N b
  let y := powerData N a b
  let x := headLogData N a b
  let c := fraction B A
  let d := headInverse (arg a) b N
  have hr := GaussianPositiveRationalLogarithm.name_regular B A (head_log_source N a b ha hb)
  have hp := power_regular N a b hN
  have er := exponential_regular L x hr
  have ep := exponential_regular powerF y hp
  have ex := GaussianPositiveRationalLogarithm.exponential_fraction B A (head_log_source N a b ha hb)
  have hd := constant_regular (Γ := Γ) d
  have head := cross_trans _ _ _ _ _ _ ex
    (GaussianGammaWeierstrassApproximant.constant_data_cross c d (head_inverse_code N a b ha hb).eqSymm)
  have product := GaussianGammaAdjacentCutoff.multiply_cross (E powerF) (E powerF) (E L) constantF
    (ed powerF y) (ed powerF y) (ed L x) d ep ep er hd (cross_refl _ _ ep) head
  let radius := GaussianGammaEulerFullHeadInverse.radius (arg a) b N
  let native := GaussianGammaEulerFullHeadInverse.negExpData (arg a) b N
  have nativeInput : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input powerF radius y :=
    GaussianExponentialInverse.negative_input logExponentF radius (logExponentData (arg a) b N)
      (GaussianGammaEulerFullHeadInverse.exponent_input (arg a) b N hN)
  have radii : Γ ⊢[PRAAx] crossEquivalent (E powerF) (E powerF) (ed powerF y) native :=
    GaussianExponentialRadiusIndependence.same_input_cross powerF (GaussianNameBounds.U powerF y) radius y
      (exponential_input _ _ hp) nativeInput
  have replace := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF (E powerF) (E powerF)
    d d (ed powerF y) native hd hd ep (GaussianRadiusExponentialName.name_regular _ _ _ nativeInput)
    (cross_refl _ _ hd) radii
  have swap := GaussianNameRingLaws.multiply_commutative (E powerF) constantF (ed powerF y) d ep hd
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (exponential_sum powerF L y x hp hr))
    (cross_trans _ _ _ _ _ _ product (cross_trans _ _ _ _ _ _ swap replace))

theorem original_euler_inverse_cross (N a b : PTm n) (hN : Γ ⊢[PRAAx] le (two*a) N)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (E nameF) GaussianGammaEulerReciprocalInverse.eulerF (expData N a b)
      (GaussianGammaEulerReciprocalInverse.eulerData (arg a) a b b N) := by
  have hs : Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source (arg a) a b one b N :=
    .andI (GaussianStirlingGammaLogarithm.gamma_source a b (.andI ha hb)) hN
  exact cross_trans _ _ _ _ _ _
    (exponential_cross N a b (GaussianGammaEulerFullHeadInverse.cutoff_positive _ _ _ _ _ _ hs) ha hb)
    (cross_symm _ _ _ _ (GaussianGammaEulerFullHeadInverse.original_factorization _ _ _ _ _ _ hs))

theorem actual_positive_rational_euler_logarithm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 0) ⋏ (le one (var 1) ⋏ le one (var 2))) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2)) ⋏
        (realSamples nameF (data (var 0) (var 1) (var 2)) ⋏
          crossEquivalent (E nameF) I (expData (var 0) (var 1) (var 2)) (idData (arg (var 1)) (var 2) (var 0)))) := by
  refine closeUniv 3 (.impI ?_)
  exact .andI (name_regular _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (.andI (name_real _ _ _ Prf.hyp0.andE₂.andE₂)
      (exponential_cross _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLog
