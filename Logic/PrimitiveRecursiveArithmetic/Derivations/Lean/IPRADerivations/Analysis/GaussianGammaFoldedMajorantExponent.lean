import IPRADerivations.Analysis.GaussianGammaCanonicalExponentBound
import IPRADerivations.Analysis.GaussianGammaEulerHead
import IPRADerivations.Analysis.GaussianGammaCanonicalTailMetric
import IPRADerivations.Analysis.GaussianNameRingLaws
import IPRADerivations.Analysis.GaussianExactDiskShrinking
import IPRADerivations.Analysis.GaussianPositiveExponentialMajorant

/-!
# The sharp C9 disk for the original folded approximant exponent

The actual combined name is E_(2R)-T_N, retaining every original
addition and negation clock. The original sharp finite C6 bounds give
a raw envelope A+2^(-p), A=2R²+2R. Actual rational disk correction
then yields an equivalent name with samples in the exact A disk.
No exponent comparison or desired majorant is supplied as a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFoldedMajorantExponent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianGammaCanonicalExponent (source exponentF exponentData exponentPoint exponentValue addPrecision)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianGammaCanonicalExponentBound (numericalRadius)
open GaussianFastValueCut (rawEnvelope)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (z R B N : PTm n) : Fm PTm n := source z R B ⋏ le (two*R) N
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    (input z R B N).subst σ = input (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [input]

theorem tail_source (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N :=
  .andI h.andE₁.andE₂.andE₁ (.andI
    (le_trans (GaussianGammaCanonicalExponent.tail_source z R B h.andE₁).andE₂.andE₁ h.andE₂)
    (.andI h.andE₁.andE₂.andE₂ h.andE₂))

/-- At ANY original later precision, retain the half-radius C6 term and
only half a requested dyadic unit of observation slack. -/
theorem later_tail_half_bound (p q z R B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] bounded (GaussianGammaCanonicalTailName.point q z R B N)
      (R*unit p+one) (two*unit p) := by
  have grow : Γ ⊢[PRAAx] le (unit p) (unit q) :=
    GaussianFactorBudget.power_monotone_length two p q (le_succ_self one) hpq
  have four : Γ ⊢[PRAAx] le (num 4*unit p) (DyadicComplexLogarithm.unit q) :=
    le_congr (.eqRefl _) (GaussianLocalLogarithmName.unit_factor q).eqSymm
      (le_trans (le_mul_mono (le_refl (num 4)) grow)
        (le_of_eq_add (d := num 12*unit q) (by ipra_ring)))
  have main := le_mul_mono h.andE₂.andE₂.andE₂ (le_refl (R*unit p*DyadicComplexLogarithm.unit q))
  have rounding := le_mul_mono four (le_refl N)
  have budget : Γ ⊢[PRAAx] le
      (GaussianGammaCanonicalTailName.radius q R N*(two*unit p))
      ((R*unit p+one)*GaussianGammaCanonicalTailName.denominator q N) :=
    le_congr (by unfold GaussianGammaCanonicalTailName.radius; ipra_ring)
      (by unfold GaussianGammaCanonicalTailName.denominator; ipra_ring) (add_le_add₂ main rounding)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianGammaCanonicalTailName.denominator_positive q N h.andE₂.andE₁)
    (positive_product _ _ (le_succ_self one) (unit_positive p)) budget
    (GaussianGammaCanonicalTailName.point_bound q z R B N h)

theorem later_exponent_bound (p s z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hps : Γ ⊢[PRAAx] le p s) : Γ ⊢[PRAAx] bounded (exponentPoint s z R B)
      (((one+two*R)*R)*(two*unit p)+(R*unit p+one)) (two*unit p) := by
  have hq : Γ ⊢[PRAAx] le p (addPrecision s) := le_trans hps (le_add_right _ _)
  have tail := bound_congr (GaussianGammaCanonicalTailName.point_at (addPrecision s) z R B (two*R))
    (.eqRefl _) (.eqRefl _) (later_tail_half_bound p (addPrecision s) z R B (two*R)
      (GaussianGammaCanonicalExponent.tail_source z R B h) hq)
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ (le_refl one)
    (positive_product _ _ (le_succ_self one) (unit_positive p))
    (GaussianGammaCanonicalExponentBound.product_value_bound (addPrecision s) z R B (two*R) h) tail
  exact bound_congr (GaussianGammaCanonicalExponent.exponent_sample_at s z R B).eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ _ (positive_product _ _ (le_succ_self one) (unit_positive p))).iffMpr
      (bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) sum))

def combinedF : PR 2 := GaussianNameArithmetic.addF exponentF (negativeF GaussianGammaCanonicalTailName.pointF)
def combinedData (z R B N : PTm n) : PTm n := GaussianNameArithmetic.addData (exponentData z R B)
  (negativeData (GaussianGammaCanonicalTailName.data z R B N))
def combinedPoint (p z R B N : PTm n) : PTm n := ap2 combinedF p (combinedData z R B N)
@[simp] theorem subst_combinedData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (combinedData z R B N) = combinedData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [combinedData]
@[simp] theorem subst_combinedPoint {l : ℕ} (σ : Fin n → PTm l) (p z R B N : PTm n) :
    Syn.subst σ (combinedPoint p z R B N) = combinedPoint (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ N) := by simp [combinedPoint]

theorem combined_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] pointCN combinedF (combinedData z R B N) :=
  GaussianNameArithmetic.add_fast _ _ _ _ (GaussianGammaCanonicalExponent.exponent_regular z R B h.andE₁)
    (GaussianNameRingLaws.negative_fast _ _ (GaussianGammaCanonicalTailName.name_regular z R B N (tail_source z R B N h)))

theorem combined_point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] bounded (combinedPoint p z R B N) (numericalRadius R*unit p+one) (unit p) := by
  let s := addPrecision p
  let t := GaussianFastValueCut.exponent (one+one) s
  let D := two*unit p
  have dp : Γ ⊢[PRAAx] le one D := positive_product _ _ (le_succ_self one) (unit_positive p)
  have ps : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have pt : Γ ⊢[PRAAx] le p t := le_trans ps (le_add_right _ _)
  have en := later_exponent_bound p s z R B h.andE₁ ps
  have tn := later_tail_half_bound p t z R B N (tail_source z R B N h) pt
  have rawNegative := GaussianRationalReciprocal.bounded_difference qzero (GaussianGammaCanonicalTailName.point t z R B N)
    zero one (R*unit p+one) D (le_refl _) dp
    (GaussianMonicResidualRadius.zero_bounded zero one (le_refl _)) tn
  have negativeBound : Γ ⊢[PRAAx] bounded
      (ap2 (negativeF GaussianGammaCanonicalTailName.pointF) s (negativeData (GaussianGammaCanonicalTailName.data z R B N)))
      (R*unit p+one) D :=
    bound_congr (GaussianNameRingLaws.negative_at GaussianGammaCanonicalTailName.pointF _ s).eqSymm (.eqRefl _) (.eqRefl _)
      ((GaussianFastValueCut.recode_bound_iff _ _ _ dp).iffMpr
        (bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) rawNegative))
  have sum := GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ dp en negativeBound
  have normalized := (GaussianFastValueCut.recode_bound_iff _ _ _ dp).iffMpr sum
  have actual := bound_congr
    (GaussianNameArithmetic.add_at exponentF (negativeF GaussianGammaCanonicalTailName.pointF)
      (exponentData z R B) (negativeData (GaussianGammaCanonicalTailName.data z R B N)) p).eqSymm
    (.eqRefl _) (.eqRefl _) normalized
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ dp (unit_positive p)
    (le_of_eq_add (d := zero) (by unfold D numericalRadius; ipra_ring)) actual

theorem combined_envelope (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] rawEnvelope combinedF (combinedData z R B N) (numericalRadius R) one one := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [rawEnvelope,combinedPoint,Syn.shift,subst_combinedData,
    GaussianGammaCanonicalExponentBound.subst_numericalRadius,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    bound_congr (.eqRefl _) (show Γ.map Fm.shift ⊢[PRAAx]
      numericalRadius (Syn.shift R)*unit (var 0)+one ≐ numericalRadius (Syn.shift R)*unit (var 0)+one*one by ipra_ring)
      (show Γ.map Fm.shift ⊢[PRAAx] unit (var 0) ≐ one*unit (var 0) by ipra_ring)
      (combined_point_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs)

def correctedF : PR 2 := GaussianExactDiskShrinking.nameF combinedF
def correctedData (z R B N : PTm n) : PTm n := GaussianExactDiskShrinking.data (combinedData z R B N) (numericalRadius R) one one
@[simp] theorem subst_correctedData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (correctedData z R B N) = correctedData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [correctedData]

theorem corrected_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] pointCN correctedF (correctedData z R B N) :=
  GaussianExactDiskShrinking.name_regular _ _ _ _ _ (le_refl _) (combined_regular z R B N h) (combined_envelope z R B N h)
theorem corrected_cross (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    crossEquivalent correctedF combinedF (correctedData z R B N) (combinedData z R B N) :=
  GaussianExactDiskShrinking.cross_equivalent _ _ _ _ _ (le_refl _) (combined_regular z R B N h) (combined_envelope z R B N h)
theorem corrected_point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] bounded (ap2 correctedF p (correctedData z R B N)) (numericalRadius R) one :=
  GaussianExactDiskShrinking.sample_bound _ p _ _ _ _ (le_refl _) (combined_envelope z R B N h)
theorem corrected_exponential_input (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input correctedF (numericalRadius R) (correctedData z R B N) := by
  refine .andI (corrected_regular z R B N h) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,subst_correctedData,
    GaussianGammaCanonicalExponentBound.subst_numericalRadius] using
    corrected_point_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

theorem corrected_finite_exponential_bound (p K z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    bounded (GaussianRationalPolynomialExponential.scalarSum (ap2 correctedF p (correctedData z R B N)) K)
      (pw (num 3) (numericalRadius R)) one :=
  GaussianPositiveExponentialMajorant.disk_bound _ _ _ (corrected_point_bound p z R B N h)

def exponentialF : PR 2 := GaussianRadiusExponentialName.nameF correctedF
def exponentialData (z R B N : PTm n) : PTm n := GaussianRadiusExponentialName.data (numericalRadius R) (correctedData z R B N)
def majorantF : PR 2 := GaussianNameArithmetic.multiplyF GaussianGammaCanonicalExponent.constantF exponentialF
def majorantData (z R B N : PTm n) : PTm n := GaussianNameArithmetic.multiplyData
  GaussianGammaCanonicalExponent.constantF exponentialF (GaussianGammaEulerHead.run z B (two*R)) (exponentialData z R B N)
def majorant (R : PTm n) : PTm n := R*pw (one+R) (two*R)*pw (num 3) (numericalRadius R)
@[simp] theorem subst_exponentialData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (exponentialData z R B N) = exponentialData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exponentialData]
@[simp] theorem subst_majorantData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (majorantData z R B N) = majorantData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp only [majorantData,GaussianNameArithmetic.subst_multiplyData,subst_exponentialData,
    GaussianGammaEulerHead.run,ConciseIPRA.PTm.subst_app]
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp
@[simp] theorem subst_majorant {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (majorant R) = majorant (Syn.subst σ R) := by simp [majorant]

theorem exponential_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] pointCN exponentialF (exponentialData z R B N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (corrected_exponential_input z R B N h)
theorem exponential_point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] bounded (ap2 exponentialF p (exponentialData z R B N)) (pw (num 3) (numericalRadius R)) one :=
  bound_congr (GaussianRadiusExponentialName.sample_at correctedF (numericalRadius R) p (correctedData z R B N)).eqSymm
    (.eqRefl _) (.eqRefl _)
    (corrected_finite_exponential_bound (GaussianRadiusExponentialName.inputPrecision (numericalRadius R) p)
      (GaussianRadiusExponentialName.index (numericalRadius R) p) z R B N h)

theorem majorant_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] pointCN majorantF (majorantData z R B N) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (GaussianGammaCanonicalExponent.constant_regular _)
    (exponential_regular z R B N h)

/-- The actual head_(2R) times the corrected exponential has the exact
original C9 majorant, at every requested observation precision. -/
theorem majorant_point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] bounded (ap2 majorantF p (majorantData z R B N)) (majorant R) one := by
  let H := GaussianGammaEulerHead.run z B (two*R)
  let s := GaussianFastValueCut.exponent
    (GaussianNameArithmetic.multiplyModulus GaussianGammaCanonicalExponent.constantF exponentialF H (exponentialData z R B N)) p
  have hb := bound_congr (GaussianGammaCanonicalExponent.constant_at s H).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianGammaEulerHead.returned_head_bound z R B (two*R) h.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂)
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) hb
    (exponential_point_bound s z R B N h)
  exact bound_congr (GaussianNameArithmetic.multiply_at GaussianGammaCanonicalExponent.constantF exponentialF H (exponentialData z R B N) p).eqSymm
    (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ _ (le_refl one)).iffMpr
      (bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) product))

theorem original_later_tail_half_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaCanonicalTailName.source (var 2) (var 3) (var 4) (var 5) ⟶ le (var 0) (var 1) ⟶
      bounded (GaussianGammaCanonicalTailName.point (var 1) (var 2) (var 3) (var 4) (var 5))
        (var 3*unit (var 0)+one) (two*unit (var 0))) :=
  closeUniv 6 (.impI (.impI (later_tail_half_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_folded_majorant_exponent_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ rawEnvelope combinedF (combinedData (var 0) (var 1) (var 2) (var 3))
      (numericalRadius (var 1)) one one) := closeUniv 4 (.impI (combined_envelope _ _ _ _ Prf.hyp0))
theorem original_exact_folded_majorant_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ pointCN correctedF (correctedData (var 0) (var 1) (var 2) (var 3)) ⋏
      crossEquivalent correctedF combinedF (correctedData (var 0) (var 1) (var 2) (var 3)) (combinedData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.andI (corrected_regular _ _ _ _ Prf.hyp0) (corrected_cross _ _ _ _ Prf.hyp0)))
theorem original_exact_folded_exponential_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 1) (var 2) (var 3) (var 4) ⟶ bounded
      (ap2 exponentialF (var 0) (exponentialData (var 1) (var 2) (var 3) (var 4))) (pw (num 3) (numericalRadius (var 2))) one) :=
  closeUniv 5 (.impI (exponential_point_bound _ _ _ _ _ Prf.hyp0))
theorem original_C9_bounded_representative_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ pointCN majorantF (majorantData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (majorant_regular _ _ _ _ Prf.hyp0))
theorem original_C9_bounded_representative_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 1) (var 2) (var 3) (var 4) ⟶ bounded
      (ap2 majorantF (var 0) (majorantData (var 1) (var 2) (var 3) (var 4))) (majorant (var 2)) one) :=
  closeUniv 5 (.impI (majorant_point_bound _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaFoldedMajorantExponent
