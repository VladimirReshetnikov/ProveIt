import IPRADerivations.Analysis.GaussianPositiveRationalLogarithmProperness
import IPRADerivations.Analysis.GaussianEulerIntegrandName
import IPRADerivations.Analysis.GaussianRobinMeshExponential
import IPRADerivations.Core.CongruenceTactic

/-!
# Cancellation of the actual two exponential factors at the upper beta endpoint

The unchanged rational-time power at encoded time ((bN)/b) uses
the same logarithm value as the original positive integer mesh name.
Its exponent and the original finite Euler exponent sum to the
negative logarithm of (N). The actual exponential product is
therefore the original exact reciprocal of (N).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaUpperPowerCancellation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (logF logExponentF logExponentData exponentialInputData exponential_input)
open GaussianGammaEulerShift (negativeLogData negativeLogExpData)
open GaussianEulerIntegrandName (coefficient powerExponentF powerExponentData powerRadius powerF powerData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianRationalHorner (qadd qzero positive_product ofGaussian canonical_unique represents_congr)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qmul_zero_left)
open GaussianRationalMatrixFiniteSums (minusOne)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded qnegative qnegative_represents)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem mesh_at_one (Q : PTm n) : Γ ⊢[PRAAx]
    GammaMeshRobinLogBridge.harmonicLog one Q ≐ (RationalGaussianEmbedding.scalarZero : PTm n) := by
  let D := Products.fact (Q*one)
  let A := GammaMeshRobinLogBridge.harmonicNumerator one Q
  have eq : Γ ⊢[PRAAx] Q*one ≐ Q := by ipra_ring
  have sums : Γ ⊢[PRAAx] S (Q*one) D ≐ S Q D := congrAp2 (sumF hB) eq (.eqRefl _)
  have numerator : Γ ⊢[PRAAx] ZT.eq A (ZT.ofNat D*ZT.ofNat zero) := by
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    change Groth.ι (IPRA.Q.mk Γ (S (Q*one) D))-Groth.ι (IPRA.Q.mk Γ (S Q D)) =
      Groth.ι (IPRA.Q.mk Γ D)*Groth.ι (IPRA.Q.mk Γ zero)
    rw [natEq sums]
    simp
  have int := RationalIntegerNormalization.normalize_integer A (ZT.ofNat zero) D (GammaEulerMesh.factorial_positive _) numerator
  have q := RationalIntegerNormalization.normalize_integer (Γ := Γ) (ZT.ofNat zero) (ZT.ofNat zero) (one : PTm n)
    (le_refl one) (by apply ZT.derive; simp only [ZT.toZ_mul,ZT.toZ_ofNat]; ipra_simps; ring)
  exact int.eqTrans q.eqSymm

theorem integer_log_at_one (p : PTm n) : Γ ⊢[PRAAx] ap2 logF p one ≐ (qzero : PTm n) := by
  have e := mesh_at_one (Γ := Γ) (GammaEulerConstantName.mesh p)
  have embed : Γ ⊢[PRAAx] RationalGaussianEmbedding.embed
      (GammaMeshRobinLogBridge.harmonicLog one (GammaEulerConstantName.mesh p)) ≐ RationalGaussianEmbedding.embed RationalGaussianEmbedding.scalarZero := by
    ipra_congr (RationalGaussianEmbedding.embed (var 0) : PTm 1) with [e]
  exact (GaussianGammaFiniteApproximantName.log_sample_at p one).eqTrans (embed.eqTrans RationalGaussianEmbedding.embed_zero)

theorem negative_log_at_one (p : PTm n) : Γ ⊢[PRAAx] ap2 logExponentF p (negativeLogData one) ≐ (qzero : PTm n) := by
  let t := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus logF constantF one minusOne) p
  have e := GaussianNameArithmetic.multiply_at (Γ := Γ) logF constantF one minusOne p
  exact e.eqTrans ((GaussianNameArithmetic.recode_congr
    ((qmul_congr (integer_log_at_one t) (constant_at t minusOne)).eqTrans (qmul_zero_left minusOne))).eqTrans
      (GaussianExponentialReference.recode_fixed _ GaussianRationalSyntheticDivision.qzero_canonical))

def logClock (p : PTm n) : PTm n := GaussianFastValueCut.exponent two p

theorem rational_log_integer_at (p N : PTm n) : Γ ⊢[PRAAx]
    GaussianPositiveRationalLogarithm.sample p N one ≐ ap2 logF (logClock p) N := by
  let t := logClock p
  let u := ap2 logF t N
  have hU : Γ ⊢[PRAAx] GaussianRationalHorner.canonical u :=
    GaussianRationalHorner.canonical_congr (GaussianGammaFiniteApproximantName.log_sample_at t N)
      (RationalGaussianEmbedding.embed_canonical _)
  exact (GaussianPositiveRationalLogarithm.sample_at p N one).eqTrans
    ((GaussianNameArithmetic.recode_congr ((qadd_congr (.eqRefl _) (negative_log_at_one t)).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right u hU))).eqTrans (GaussianExponentialReference.recode_fixed _ hU))

private theorem integer_diagonal (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (GaussianPositiveRationalLogarithm.sample p N one) (ap2 logF p N) two (unit p) := by
  let t := logClock p
  let U := unit p
  let V := unit t
  have l : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have hUV : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone l
  have raw := GaussianNameEquivalence.point_at logF N t p (GaussianGammaFiniteApproximantName.log_regular N hN)
  have cmp : Γ ⊢[PRAAx] le ((V+U)*U) (two*(V*U)) := by
    ipra_le (Groth.ι (IPRA.Q.mk Γ U))*sl hUV
  exact distance_congr (rational_log_integer_at p N).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive p)) (unit_positive p) cmp raw)

theorem rational_log_integer (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent GaussianPositiveRationalLogarithm.logF logF (GaussianPositiveRationalLogarithm.data N one) N := by
  refine GaussianNameEquivalence.diagonal_to_cross _ _ _ _
    (GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl _)))
    (GaussianGammaFiniteApproximantName.log_regular N hN) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift, Syn.shift] using hN.shift
  simpa only [GaussianNameEquivalence.diagonalEquivalent, GaussianPositiveRationalLogarithm.subst_data,
    GaussianPositiveRationalLogarithm.sample, Syn.shift, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, GaussianEuclideanPointDistance.unit] using integer_diagonal (var 0) (Syn.shift N) hs

theorem upper_log (b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent GaussianPositiveRationalLogarithm.logF logF
      (GaussianPositiveRationalLogarithm.data (b*N) b) N :=
  cross_trans _ _ _ _ _ _ (GaussianPositiveRationalLogarithmProperness.original_logarithm_proper
    (b*N) b N one (.andI (positive_product _ _ hb hN) hb) (.andI hN (le_refl _)) (by ipra_ring))
    (rational_log_integer N hN)

theorem coefficient_cancellation (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd (coefficient z B) (qnegative (ofGaussian z B)) ≐ minusOne := by
  let W := ComplexLogarithmRemainder.scale B ComplexLogarithmRemainder.oneCode
  have e := GaussianRationalHorner.qadd_represents _ _ _ _ B hB
    (GaussianEulerIntegrandName.coefficient_represents z B hB)
    (qnegative_represents _ _ _ (GaussianRationalHorner.ofGaussian_represents z B hB))
  have r := qnegative_represents _ _ _ (GaussianRationalReciprocal.qone_represents_scaled (Γ := Γ) B)
  apply canonical_unique _ _ (ComplexLogarithmRemainder.neg W) _ (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalMetric.qnegative_canonical _) hB (hrv := r)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := e)
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_sub,
    GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg]; ring

theorem exponent_sum (z B b N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent (addF powerExponentF logExponentF) logExponentF
      (addData (powerExponentData z B (b*N) b) (logExponentData z B N)) (negativeLogData N) := by
  let J := GaussianPositiveRationalLogarithm.logF
  let x := GaussianPositiveRationalLogarithm.data (b*N) b
  let c := coefficient z B
  let d := qnegative (ofGaussian z B)
  let L := multiplyData logF constantF N c
  let Q := logExponentData z B N
  have j := GaussianPositiveRationalLogarithm.name_regular (b*N) b (.andI (positive_product _ _ hb hN) hb)
  have l := GaussianGammaFiniteApproximantName.log_regular N hN
  have hc := constant_regular (Γ := Γ) c
  have hd := constant_regular (Γ := Γ) d
  have q := GaussianGammaFiniteApproximantName.log_exponent_regular z B N hN
  have left := cross_trans _ _ _ _ _ _
    (multiply_cross constantF constantF J logF c c x N hc hc j l (cross_refl _ _ hc) (upper_log b N hb hN))
    (GaussianNameRingLaws.multiply_commutative constantF logF c N hc l)
  have sum := GaussianNameArithmetic.add_equivalent powerExponentF logExponentF logExponentF logExponentF
    (powerExponentData z B (b*N) b) L Q Q (multiply_fast _ _ _ _ hc j)
    (multiply_fast _ _ _ _ l hc) q q (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ left)
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (cross_refl _ _ q))
  have const := cross_trans _ _ _ _ _ _ (GaussianGammaEulerShift.constant_sum_cross (Γ := Γ) c d)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (coefficient_cancellation z B hB))
  have mul := multiply_cross logF logF (addF constantF constantF) constantF N N (addData c d) minusOne
    l l (add_fast _ _ _ _ hc hd) (constant_regular _) (cross_refl _ _ l) const
  exact cross_trans _ _ _ _ _ _ sum (cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ _ (GaussianNameRingLaws.distributive logF constantF constantF N c d l hc hd)) mul)

theorem original_product (z B b N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF powerF (GaussianRadiusExponentialName.nameF logExponentF)) constantF
      (multiplyData powerF (GaussianRadiusExponentialName.nameF logExponentF)
        (powerData z B (b*N) b) (exponentialInputData logExponentF (logExponentData z B N)))
      (GaussianGammaEulerShiftLimit.reciprocalPoint N) := by
  let x := powerExponentData z B (b*N) b
  let y := logExponentData z B N
  let u := negativeLogData N
  have px := GaussianEulerIntegrandName.power_exponent_regular z B (b*N) b (.andI hB (.andI (positive_product _ _ hb hN) hb))
  have py := GaussianGammaFiniteApproximantName.log_exponent_regular z B N hN
  have pu := GaussianGammaEulerShift.negative_log_regular N hN
  have prod := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent powerExponentF logExponentF logExponentF
    (powerRadius z B (b*N) b) (GaussianNameBounds.U logExponentF y) (GaussianNameBounds.U logExponentF u)
    x y u (exponential_input _ _ px) (exponential_input _ _ py) (exponential_input _ _ pu) (exponent_sum z B b N hB hb hN)
  exact cross_trans _ _ _ _ _ _ prod (GaussianRobinMeshExponential.mesh_exponential_inverse N hN)

theorem original_beta_upper_power_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ le one (var 2) ⋏ le one (var 3)) ⟶
      crossEquivalent (multiplyF powerF (GaussianRadiusExponentialName.nameF logExponentF)) constantF
        (multiplyData powerF (GaussianRadiusExponentialName.nameF logExponentF)
          (powerData (var 0) (var 1) (var 2*var 3) (var 2))
          (exponentialInputData logExponentF (logExponentData (var 0) (var 1) (var 3))))
        (GaussianGammaEulerShiftLimit.reciprocalPoint (var 3))) :=
  closeUniv 4 (.impI (original_product _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaUpperPowerCancellation
