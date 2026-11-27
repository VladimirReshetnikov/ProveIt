import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaLogHarmonicName
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaExponentStep

/-!
# The correction between the folded Gamma exponents

The actual difference of the fixed and cofinal Euler observations gives
a regular correction name. At each common mesh the exact identity
`gamma_N + log N = H_N` cancels the two copies of the cofinal Euler
sample. The errors of the actual name operations give an explicit
diagonal envelope, hence an identity at independent precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFoldedExponentBalance

open_ipra
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiplyModulus)
open GaussianRationalHorner (qadd qmul ofGaussian)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianGammaLogHarmonicName (fixedF fixed_regular)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular harmonicPoint gammaF gamma_regular
  gamma_sample_at differenceF differenceData difference_regular productF productData product_regular)
open GaussianGammaFiniteApproximantName (logF log_regular logExponentF logExponentData log_exponent_regular)
open GaussianNameRingLaws (three point_regular normalized_to_sample add_sample_error multiply_sample_error
  sum_left_error sum_right_error product_left_error through_identity equivalent_of_envelope)
open GaussianGeneralFTAConstants (ceilL1 ceil_norm_bound)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The middle raw value cancels after factoring the common multiplier. -/
theorem finite_product_balance (g a l w : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul (qsub g l) w) (qmul (qsub a g) w) ≐ qmul (qsub a l) w :=
  (GaussianRationalPolynomialBuffers.distribute_right (qsub g l) (qsub a g) w).eqSymm.eqTrans
    (qmul_congr ((GaussianReciprocalHorner.qadd_commutative (qsub g l) (qsub a g)).eqTrans
      (GaussianReconstructionRoots.difference_chain a g l)) (.eqRefl _))

theorem finite_balance (g a l w : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul (qsub g (qadd a l)) w) (qmul (qsub a g) w) ≐ qmul l (qnegative w) := by
  have difference : Γ ⊢[PRAAx] qsub a (qadd a l) ≐ qnegative l :=
    (GaussianRationalDistanceOrder.reversed_difference (qadd a l) a).eqSymm.eqTrans
      ((GaussianInverseBinomialRows.negative_congr
        (GaussianRationalSyntheticCoefficientValues.qadd_sub_recode a l)).eqTrans
        (RationalGaussianEmbedding.negative_recode l))
  have product : Γ ⊢[PRAAx] qmul (qnegative l) w ≐ qmul l (qnegative w) :=
    (GaussianInverseBinomialRows.negative_product l w).eqSymm.eqTrans
      ((GaussianInverseBinomialRows.negative_congr (GaussianRationalPowerAlgebra.qmul_commutative l w)).eqTrans
        ((GaussianInverseBinomialRows.negative_product w l).eqTrans
          (GaussianRationalPowerAlgebra.qmul_commutative (qnegative w) l)))
  exact (finite_product_balance g a (qadd a l) w).eqTrans
    ((qmul_congr difference (.eqRefl _)).eqTrans product)

theorem fixed_and_log_at (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qadd (ap2 fixedF p N) (ap2 logF p N) ≐ harmonicPoint N := by
  let g := GammaEulerConstantName.fixedSample p N
  let l := GammaMeshRobinLogBridge.meshLogSample p N
  have h := GammaMeshRobinLogBridge.fixed_log_samples_sum p N hN
  have e : Γ ⊢[PRAAx] RationalGaussianEmbedding.embed (RationalArithmetic.add g l) ≐ harmonicPoint N := by
    ipra_congr (RationalGaussianEmbedding.embed (var 0) : PTm 1) with
      [h] using [harmonicPoint, GaussianGammaCanonicalExponent.harmonic, GammaMeshRobinLogBridge.harmonicValue,
        RationalCubeMidpoint.fraction]
  exact (qadd_congr (RationalGaussianNameEmbedding.sample_at GammaEulerConstantName.fixedF p N)
      (RationalGaussianNameEmbedding.sample_at GammaMeshRobinLogBridge.meshLogF p N)).eqTrans
    ((RationalGaussianEmbedding.embed_add g l).eqSymm.eqTrans e)

theorem gamma_independent_parameter (p N : PTm n) : Γ ⊢[PRAAx] ap2 gammaF p N ≐ ap2 gammaF p zero := by
  have h := (GammaEulerConstantName.gamma_at (Γ := Γ) p N).eqTrans (GammaEulerConstantName.gamma_at p zero).eqSymm
  have e : Γ ⊢[PRAAx] RationalGaussianEmbedding.embed (GammaEulerConstantName.gammaSample p N) ≐
      RationalGaussianEmbedding.embed (GammaEulerConstantName.gammaSample p zero) := by
    ipra_congr (RationalGaussianEmbedding.embed (var 0) : PTm 1) with [h]
  exact (RationalGaussianNameEmbedding.sample_at GammaEulerConstantName.gammaF p N).eqTrans
    (e.eqTrans (gamma_sample_at p).eqSymm)

def differenceRawF : PR 2 := GaussianFastValueCut.differenceF fixedF gammaF
def correctionDifferenceF : PR 2 := GaussianFastValueCut.nameF differenceRawF
def correctionDifferenceData (N : PTm n) : PTm n := GaussianFastValueCut.nameData (one+one) N
def correctionF : PR 2 := multiplyF correctionDifferenceF constantF
def correctionData (z B N : PTm n) : PTm n :=
  multiplyData correctionDifferenceF constantF (correctionDifferenceData N) (ofGaussian z B)

def sumF : PR 2 := addF productF correctionF
def sumData (z B N : PTm n) : PTm n := addData (productData z B N) (correctionData z B N)

ipra_subst correctionDifferenceData
ipra_subst correctionData
ipra_subst sumData

theorem raw_regular (N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular differenceRawF (one+one) N :=
  GaussianFastValueCut.difference_regular fixedF gammaF one one N (point_regular _ _ (fixed_regular N h))
    (point_regular _ _ (RationalGaussianNameEmbedding.name_regular _ _ (GammaEulerConstantName.gamma_name_regular N)))

theorem difference_fast (N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN correctionDifferenceF (correctionDifferenceData N) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_regular N h)

theorem correction_fast (z B N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN correctionF (correctionData z B N) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (difference_fast N h) (constant_regular _)

theorem sum_fast (z B N : PTm n) (h : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN sumF (sumData z B N) :=
  GaussianNameArithmetic.add_fast _ _ _ _ (product_regular z B N) (correction_fast z B N h)

def pCore (p z B N : PTm n) : PTm n :=
  qmul (qsub (ap2 gammaF p zero) (harmonicPoint N)) (ofGaussian z B)
def correctionCore (p z B N : PTm n) : PTm n :=
  qmul (qsub (ap2 fixedF p N) (ap2 gammaF p zero)) (ofGaussian z B)
def qCore (p z B N : PTm n) : PTm n := qmul (ap2 logF p N) (qnegative (ofGaussian z B))

def pBudget (z B N : PTm n) : PTm n :=
  (multiplyModulus differenceF constantF (differenceData N) (ofGaussian z B)+one)
    +three*ceilL1 (ofGaussian z B)
def correctionBudget (z B N : PTm n) : PTm n :=
  (multiplyModulus correctionDifferenceF constantF (correctionDifferenceData N) (ofGaussian z B)+one)
    +three*ceilL1 (ofGaussian z B)
def qBudget (z B N : PTm n) : PTm n :=
  multiplyModulus logF constantF N (qnegative (ofGaussian z B))+one
def sumBudget (z B N : PTm n) : PTm n := ((three+pBudget z B N)+correctionBudget z B N)+qBudget z B N

ipra_subst qBudget
ipra_subst pBudget [three]
ipra_subst correctionBudget [three]
ipra_subst sumBudget [three]

theorem p_error (p z B N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 productF p (productData z B N)) (pCore p z B N) (pBudget z B N) (unit p) := by
  let w := ofGaussian z B
  let b := qsub (ap2 gammaF p zero) (harmonicPoint N)
  have h := multiply_sample_error (Γ := Γ) differenceF constantF (differenceData N) w p
    (difference_regular N) (constant_regular _)
  have d : Γ ⊢[PRAAx] distanceBounded (ap2 differenceF p (differenceData N)) b three (unit p) :=
    distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p _)) (.eqRefl _) (.eqRefl _)
      (add_sample_error gammaF constantF zero (qnegative (harmonicPoint N)) p gamma_regular (constant_regular _))
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) (constant_at p w)) (.eqRefl _) (.eqRefl _) h)
    (product_left_error _ _ _ _ _ _ _ (unit_positive p) d (ceil_norm_bound w) (ceil_norm_bound b))

theorem correction_error (p z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 correctionF p (correctionData z B N)) (correctionCore p z B N) (correctionBudget z B N) (unit p) := by
  let w := ofGaussian z B
  let b := qsub (ap2 fixedF p N) (ap2 gammaF p zero)
  have h := multiply_sample_error correctionDifferenceF constantF (correctionDifferenceData N) w p
    (difference_fast N hN) (constant_regular _)
  have d : Γ ⊢[PRAAx] distanceBounded (ap2 correctionDifferenceF p (correctionDifferenceData N)) b three (unit p) :=
    distance_congr (.eqRefl _) ((GaussianFastValueCut.difference_at fixedF gammaF p N).eqTrans
      (qsub_congr (.eqRefl _) (gamma_independent_parameter p N))) (by unfold three; ipra_ring) (.eqRefl _)
      (normalized_to_sample _ _ _ _ (raw_regular N hN))
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) (constant_at p w)) (.eqRefl _) (.eqRefl _) h)
    (product_left_error _ _ _ _ _ _ _ (unit_positive p) d (ceil_norm_bound w) (ceil_norm_bound b))

theorem q_error (p z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 logExponentF p (logExponentData z B N)) (qCore p z B N) (qBudget z B N) (unit p) :=
  distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) (constant_at p _)) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error logF constantF N (qnegative (ofGaussian z B)) p (log_regular N hN) (constant_regular _))

theorem core_balance (p z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qadd (pCore p z B N) (correctionCore p z B N) ≐ qCore p z B N :=
  (qadd_congr (qmul_congr (qsub_congr (.eqRefl _) (fixed_and_log_at p N hN).eqSymm) (.eqRefl _)) (.eqRefl _)).eqTrans
    (finite_balance _ _ _ _)

theorem balance_at (p z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 sumF p (sumData z B N)) (ap2 logExponentF p (logExponentData z B N))
      (sumBudget z B N) (unit p) := by
  have u := unit_positive (Γ := Γ) p
  have h := add_sample_error productF correctionF (productData z B N) (correctionData z B N) p
    (product_regular z B N) (correction_fast z B N hN)
  exact through_identity _ _ _ _ _ _ _ u
    (distance_triangle_same _ _ _ _ _ _ u
      (distance_triangle_same _ _ _ _ _ _ u h (sum_left_error _ _ _ _ _ u (p_error p z B N)))
      (sum_right_error _ _ _ _ _ u (correction_error p z B N hN))) (q_error p z B N hN) (core_balance p z B N hN)

ipra_subst logExponentData

theorem balanced_exponents (z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent sumF logExponentF (sumData z B N) (logExponentData z B N) := by
  apply equivalent_of_envelope _ _ _ _ (sumBudget z B N) (sum_fast z B N hN) (log_exponent_regular z B N hN)
  refine .allI ?_
  have h : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift, Syn.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using hN.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, subst_sumData, subst_logExponentData,
    subst_sumBudget, GaussianCoefficientNameBounds.unit, GaussianEuclideanPointDistance.unit] using
    balance_at (var 0) (Syn.shift z) (Syn.shift B) (Syn.shift N) h

theorem actual_folded_exponents_balance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ crossEquivalent sumF logExponentF (sumData (var 0) (var 1) (var 2))
      (logExponentData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (balanced_exponents _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaFoldedExponentBalance
