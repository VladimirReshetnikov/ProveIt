import IPRADerivations.Algebra.QuadraticTowerDifferenceIdentities
import IPRADerivations.Algebra.QuadraticRationalSignDispatch
import IPRADerivations.Core.CertificateTactics

/-!
# Actual rational difference signs and order at every numerical tower depth

The actual scalar-array difference is the scalar array of the original
rational difference. Original scalar height bounds derive its real table
budget. Native numerator/cross-product arithmetic then reflects equality
and strict rational order. This is the rational ground-field embedding
slice of the ordered-domain provider, not full tower order correctness.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerScalarDifferenceOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open RationalSupMetric (numeratorOf denominatorOf)
open QuadraticTowerCoefficients (width)
open QuadraticTowerScalarArrays (scalarArray cell)
open QuadraticTowerScalarBudget (height amp)
open QuadraticTowerDifferenceIdentities (scalarDifference difference signDifference)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceEquality (sequence_equal)
open LeanProofs.IPRA.Foundations.BoundedReflection
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel_one sel_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem scalar_difference_recoded (q r : PTm n) : Γ ⊢[PRAAx]
    scalarDifference (RationalArithmetic.recode q) (RationalArithmetic.recode r) ≐ scalarDifference q r :=
  QuadraticTowerOperandProperness.scalar_equal_of_canonical _ _ (RationalArithmetic.add_guard _ _) (RationalArithmetic.add_guard _ _)
    (QuadraticRationalRepresentationInvariance.scalar_add_congr _ _ _ _ (RationalArithmetic.recode_equal q)
      (QuadraticRationalRepresentationInvariance.scalar_negative_congr _ _ (RationalArithmetic.recode_equal r)))

theorem cell_difference (i q r : PTm n) : Γ ⊢[PRAAx]
    scalarDifference (cell i q) (cell i r) ≐ cell i (scalarDifference q r) := by
  refine .orE (eqb_cases i zero) ?_ ?_
  · exact ((QuadraticTowerDifferenceIdentities.scalar_difference_congr (sel_zero Prf.hyp0) (sel_zero Prf.hyp0)).eqTrans
      (QuadraticTowerDifferenceIdentities.scalar_cancel _)).eqTrans (sel_zero Prf.hyp0).eqSymm
  · exact ((QuadraticTowerDifferenceIdentities.scalar_difference_congr (sel_one Prf.hyp0) (sel_one Prf.hyp0)).eqTrans
      (scalar_difference_recoded q r)).eqTrans
        ((RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.add_guard _ _)).eqSymm.eqTrans (sel_one Prf.hyp0).eqSymm)

/-- Both sides are actual fixed-syntax sequence constructors. Original raw
scalar coefficients need no canonicality or size premise for this identity. -/
theorem actual_scalar_difference (h q r : PTm n) : Γ ⊢[PRAAx]
    difference h (scalarArray h q) (scalarArray h r) ≐ scalarArray h (scalarDifference q r) := by
  apply sequence_equal QuadraticTowerCoefficientArithmetic.addBody QuadraticTowerScalarArrays.scalarBody (width h)
    (pairT (scalarArray h q) (QuadraticTowerCoefficientArithmetic.negated h (scalarArray h r))) (scalarDifference q r)
  refine .allI (.impI ?_)
  let h' := Syn.shift h
  let a := Syn.shift q
  let b := Syn.shift r
  let Δ := lt (var 0) (width h') :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width h') := Prf.hyp0
  have value := (QuadraticTowerDifferenceIdentities.difference_body_at h' (scalarArray h' a) (scalarArray h' b) (var 0) hi).eqTrans
    ((QuadraticTowerDifferenceIdentities.scalar_difference_congr (QuadraticTowerScalarArrays.scalar_lookup _ _ _ hi)
      (QuadraticTowerScalarArrays.scalar_lookup _ _ _ hi)).eqTrans (cell_difference (var 0) a b))
  simpa only [Δ,h',a,b,Syn.shift,subst_pairT,QuadraticTowerScalarArrays.subst_scalarArray,
    QuadraticTowerCoefficientArithmetic.subst_negated,QuadraticTowerCoefficients.subst_width,
    QuadraticTowerDifferenceIdentities.subst_scalarDifference,QuadraticTowerScalarArrays.scalar_body_at] using value

theorem difference_height (q r b B : PTm n) (hq : Γ ⊢[PRAAx] height q b) (hr : Γ ⊢[PRAAx] height r b)
    (hB : Γ ⊢[PRAAx] le (amp b) B) : Γ ⊢[PRAAx] height (scalarDifference q r) B :=
  QuadraticTowerScalarBudget.height_mono _ _ _
    (QuadraticTowerScalarBudget.add_height q _ b hq (QuadraticTowerScalarBudget.negative_height r b hr)) hB

theorem scalar_sign_difference (h B D q r b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] height q b) (hr : Γ ⊢[PRAAx] height r b) (hb : Γ ⊢[PRAAx] le (amp b) B) : Γ ⊢[PRAAx]
    signDifference h B D (scalarArray h q) (scalarArray h r) ≐ QuadraticRationalSignDispatch.scalarTag (scalarDifference q r) :=
  (QuadraticTowerSignRecipe.read_operand_congr h B (QuadraticTowerSignTable.table h B D) _ _ (actual_scalar_difference h q r)).eqTrans
    (QuadraticTowerSignEmbedding.scalar_query_native h B D _ hB (difference_height q r b B hq hr hb))

def rationalLess (q r : PTm n) : Fm PTm n := lt (RationalArgmin.left q r) (RationalArgmin.left r q)
@[simp] theorem subst_rationalLess {k : ℕ} (σ : Fin n → PTm k) (q r : PTm n) :
    (rationalLess q r).subst σ = rationalLess (Syn.subst σ q) (Syn.subst σ r) := by simp [rationalLess]

theorem scalar_difference_representation (q r : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (scalarDifference q r) (QuadraticRationalEmbedding.crossNumerator q r) (denominatorOf q*denominatorOf r) := by
  have total := RationalRepresentations.represents_add (Γ := Γ) q (RationalArithmetic.negative r)
    (numeratorOf q) (-numeratorOf r) (denominatorOf q) (denominatorOf r) (RationalRepresentations.represents_self q)
      (RationalRepresentations.represents_negative r (numeratorOf r) (denominatorOf r) (RationalRepresentations.represents_self r))
  apply QuadraticRationalPairArithmetic.scalar_value_congr _ _ _ _ _ total
  simp only [QuadraticRationalEmbedding.crossNumerator,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_ofNat]
  ring
theorem scalar_difference_tag (q r : PTm n) : Γ ⊢[PRAAx]
    QuadraticRationalSignDispatch.scalarTag (scalarDifference q r) ≐ QuadraticSignCertificates.tag (QuadraticRationalEmbedding.crossNumerator q r) :=
  QuadraticRationalSignDispatch.tag_of_representation _ _ _
    (RationalAlgebra.positive_product (RationalArgmin.denominator_positive q) (RationalArgmin.denominator_positive r))
      (scalar_difference_representation q r)

theorem cross_value (q r : PTm n) : ZT.toZ Γ (QuadraticRationalEmbedding.crossNumerator q r) =
    𝔞(RationalArgmin.left q r)-𝔞(RationalArgmin.left r q) := by
  simp only [QuadraticRationalEmbedding.crossNumerator]
  rw [ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_ofNat]
  simp only [RationalArgmin.left,ZT.toZ]
  ipra_simps
  ring
theorem cross_zero_of_equal (q r : PTm n) (h : Γ ⊢[PRAAx] RationalArgmin.rationalEq q r) : Γ ⊢[PRAAx]
    ZT.eq (QuadraticRationalEmbedding.crossNumerator q r) (ZT.ofNat zero) := by
  apply ZT.derive
  rw [cross_value,natEq h,ZT.toZ_ofNat]
  ipra_simps
  ring
theorem equal_of_cross_zero (q r : PTm n) (h : Γ ⊢[PRAAx] ZT.eq (QuadraticRationalEmbedding.crossNumerator q r) (ZT.ofNat zero)) :
    Γ ⊢[PRAAx] RationalArgmin.rationalEq q r := by
  have hz := ZT.toZ_eq h
  rw [cross_value,ZT.toZ_ofNat] at hz
  ipra_lc hz

theorem positive_cross_of_less (q r : PTm n) (h : Γ ⊢[PRAAx] rationalLess q r) : Γ ⊢[PRAAx]
    zle (ZT.ofNat one) (QuadraticRationalEmbedding.crossNumerator r q) :=
  zle_of_comb (sl h) (by rw [cross_value,ZT.toZ_ofNat]; simp only [sl_def]; ipra_simps; ring) (nn_sl h)
theorem less_of_positive_cross (q r : PTm n)
    (h : Γ ⊢[PRAAx] zle (ZT.ofNat one) (QuadraticRationalEmbedding.crossNumerator r q)) : Γ ⊢[PRAAx] rationalLess q r := by
  have hz := nn_zsl h
  rw [zsl_def,cross_value,ZT.toZ_ofNat] at hz
  apply le_of_nonneg
  convert hz using 1
  ipra_simps
  ring

theorem scalar_zero_reflect (q r : PTm n)
    (h : Γ ⊢[PRAAx] QuadraticRationalSignDispatch.scalarTag (scalarDifference q r) ≐ zero) : Γ ⊢[PRAAx] RationalArgmin.rationalEq q r :=
  equal_of_cross_zero q r (QuadraticIntegerEmbedding.integer_zero_reflect one _ (le_refl one)
    ((QuadraticIntegerEmbedding.integer_sign one _ (le_refl one)).eqTrans ((scalar_difference_tag q r).eqSymm.eqTrans h)))
theorem scalar_zero_of_equal (q r : PTm n) (h : Γ ⊢[PRAAx] RationalArgmin.rationalEq q r) : Γ ⊢[PRAAx]
    QuadraticRationalSignDispatch.scalarTag (scalarDifference q r) ≐ zero :=
  (scalar_difference_tag q r).eqTrans (QuadraticIntegerSignDispatch.tag_of_zero _ (cross_zero_of_equal q r h))
theorem scalar_positive_reflect (q r : PTm n)
    (h : Γ ⊢[PRAAx] QuadraticRationalSignDispatch.scalarTag (scalarDifference r q) ≐ one) : Γ ⊢[PRAAx] rationalLess q r :=
  less_of_positive_cross q r (QuadraticIntegerEmbedding.integer_positive_reflect one _ (le_refl one)
    ((QuadraticIntegerEmbedding.integer_sign one _ (le_refl one)).eqTrans ((scalar_difference_tag r q).eqSymm.eqTrans h)))
theorem scalar_positive_of_less (q r : PTm n) (h : Γ ⊢[PRAAx] rationalLess q r) : Γ ⊢[PRAAx]
    QuadraticRationalSignDispatch.scalarTag (scalarDifference r q) ≐ one :=
  (scalar_difference_tag r q).eqTrans (QuadraticIntegerSignDispatch.tag_of_positive _ (positive_cross_of_less q r h))

theorem scalar_equality_iff (h B D q r b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] height q b) (hr : Γ ⊢[PRAAx] height r b) (hb : Γ ⊢[PRAAx] le (amp b) B) : Γ ⊢[PRAAx]
    Fm.iff (QuadraticTowerDifferenceIdentities.equivalent h B D (scalarArray h q) (scalarArray h r)) (RationalArgmin.rationalEq q r) :=
  .andI (.impI (scalar_zero_reflect q r ((scalar_sign_difference h B D q r b hB.wk hq.wk hr.wk hb.wk).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((scalar_sign_difference h B D q r b hB.wk hq.wk hr.wk hb.wk).eqTrans (scalar_zero_of_equal q r Prf.hyp0)))

/-- The strict sign convention uses r-q, so the reflected native comparison
is left(q,r)<left(r,q), exactly the original strict rational order. -/
theorem scalar_order_iff (h B D q r b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] height q b) (hr : Γ ⊢[PRAAx] height r b) (hb : Γ ⊢[PRAAx] le (amp b) B) : Γ ⊢[PRAAx]
    Fm.iff (QuadraticTowerDifferenceIdentities.less h B D (scalarArray h q) (scalarArray h r)) (rationalLess q r) :=
  .andI (.impI (scalar_positive_reflect q r ((scalar_sign_difference h B D r q b hB.wk hr.wk hq.wk hb.wk).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((scalar_sign_difference h B D r q b hB.wk hr.wk hq.wk hb.wk).eqTrans (scalar_positive_of_less q r Prf.hyp0)))

theorem scalar_nonstrict_iff (h B D q r b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] height q b) (hr : Γ ⊢[PRAAx] height r b) (hb : Γ ⊢[PRAAx] le (amp b) B) : Γ ⊢[PRAAx]
    Fm.iff (QuadraticTowerDifferenceIdentities.equivalent h B D (scalarArray h q) (scalarArray h r) ⋎
      QuadraticTowerDifferenceIdentities.less h B D (scalarArray h q) (scalarArray h r)) (RationalArgmin.rationalLE q r) := by
  refine .andI (.impI ?_) (.impI ?_)
  · refine .orE Prf.hyp0 ?_ ?_
    · exact RationalArgmin.eq_le (.impE (.andE₁ (scalar_equality_iff h B D q r b hB.wk.wk hq.wk.wk hr.wk.wk hb.wk.wk)) Prf.hyp0)
    · exact le_of_lt (.impE (.andE₁ (scalar_order_iff h B D q r b hB.wk.wk hq.wk.wk hr.wk.wk hb.wk.wk)) Prf.hyp0)
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · exact .orI₂ (.impE (.andE₂ (scalar_order_iff h B D q r b hB.wk.wk hq.wk.wk hr.wk.wk hb.wk.wk)) Prf.hyp0)
    · exact .orI₁ (.impE (.andE₂ (scalar_equality_iff h B D q r b hB.wk.wk hq.wk.wk hr.wk.wk hb.wk.wk)) Prf.hyp0)

def output (h B D q r : PTm n) : PTm n := pairT (difference h (scalarArray h q) (scalarArray h r))
  (pairT (signDifference h B D (scalarArray h q) (scalarArray h r))
    (pairT (signDifference h B D (scalarArray h r) (scalarArray h q)) (pairT (scalarDifference q r) (scalarDifference r q))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (h B D q r : PTm n) : PTm n := PTm.app outputF ![h,B,D,q,r]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (h B D q r : PTm n) :
    Syn.subst σ (output h B D q r) = output (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ q) (Syn.subst σ r) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (h B D q r : PTm n) :
    Syn.subst σ (run h B D q r) = run (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ q) (Syn.subst σ r) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (h B D q r : PTm n) : Γ ⊢[PRAAx] run h B D q r ≐ output h B D q r := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![h,B,D,q,r]
theorem returned_array (h B D q r : PTm n) : Γ ⊢[PRAAx] fstT (run h B D q r) ≐ difference h (scalarArray h q) (scalarArray h r) :=
  (congrFst (program_at h B D q r)).eqTrans (fst_pair _ _)
theorem returned_tail (h B D q r : PTm n) : Γ ⊢[PRAAx] sndT (run h B D q r) ≐
    pairT (signDifference h B D (scalarArray h q) (scalarArray h r))
      (pairT (signDifference h B D (scalarArray h r) (scalarArray h q)) (pairT (scalarDifference q r) (scalarDifference r q))) :=
  (congrSnd (program_at h B D q r)).eqTrans (snd_pair _ _)
theorem returned_forward (h B D q r : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D q r)) ≐ signDifference h B D (scalarArray h q) (scalarArray h r) :=
  (congrFst (returned_tail h B D q r)).eqTrans (fst_pair _ _)
theorem returned_rest (h B D q r : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D q r)) ≐
    pairT (signDifference h B D (scalarArray h r) (scalarArray h q)) (pairT (scalarDifference q r) (scalarDifference r q)) :=
  (congrSnd (returned_tail h B D q r)).eqTrans (snd_pair _ _)
theorem returned_reverse (h B D q r : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h B D q r))) ≐ signDifference h B D (scalarArray h r) (scalarArray h q) :=
  (congrFst (returned_rest h B D q r)).eqTrans (fst_pair _ _)
theorem returned_differences (h B D q r : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h B D q r))) ≐ pairT (scalarDifference q r) (scalarDifference r q) :=
  (congrSnd (returned_rest h B D q r)).eqTrans (snd_pair _ _)

theorem returned_equality_iff (h B D q r b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] height q b) (hr : Γ ⊢[PRAAx] height r b) (hb : Γ ⊢[PRAAx] le (amp b) B) : Γ ⊢[PRAAx]
    Fm.iff (fstT (sndT (run h B D q r)) ≐ zero) (RationalArgmin.rationalEq q r) :=
  .andI (.impI (.impE (.andE₁ (scalar_equality_iff h B D q r b hB.wk hq.wk hr.wk hb.wk))
    ((returned_forward h B D q r).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((returned_forward h B D q r).eqTrans
      (.impE (.andE₂ (scalar_equality_iff h B D q r b hB.wk hq.wk hr.wk hb.wk)) Prf.hyp0)))
theorem returned_order_iff (h B D q r b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] height q b) (hr : Γ ⊢[PRAAx] height r b) (hb : Γ ⊢[PRAAx] le (amp b) B) : Γ ⊢[PRAAx]
    Fm.iff (fstT (sndT (sndT (run h B D q r))) ≐ one) (rationalLess q r) :=
  .andI (.impI (.impE (.andE₁ (scalar_order_iff h B D q r b hB.wk hq.wk hr.wk hb.wk))
    ((returned_reverse h B D q r).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((returned_reverse h B D q r).eqTrans
      (.impE (.andE₂ (scalar_order_iff h B D q r b hB.wk hq.wk hr.wk hb.wk)) Prf.hyp0)))

theorem actual_scalar_array_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (difference (var 0) (scalarArray (var 0) (var 1)) (scalarArray (var 0) (var 2)) ≐ scalarArray (var 0) (scalarDifference (var 1) (var 2))) :=
  closeUniv 3 (actual_scalar_difference _ _ _)
theorem actual_scalar_difference_original_tag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ height (var 3) (var 5) ⟶ height (var 4) (var 5) ⟶ le (amp (var 5)) (var 1) ⟶
      signDifference (var 0) (var 1) (var 2) (scalarArray (var 0) (var 3)) (scalarArray (var 0) (var 4)) ≐
        QuadraticRationalSignDispatch.scalarTag (scalarDifference (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (scalar_sign_difference _ _ _ _ _ (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))
theorem actual_scalar_tower_equality_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ height (var 3) (var 5) ⟶ height (var 4) (var 5) ⟶ le (amp (var 5)) (var 1) ⟶
      Fm.iff (QuadraticTowerDifferenceIdentities.equivalent (var 0) (var 1) (var 2) (scalarArray (var 0) (var 3)) (scalarArray (var 0) (var 4)))
        (RationalArgmin.rationalEq (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (scalar_equality_iff _ _ _ _ _ (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))
theorem actual_scalar_tower_order_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ height (var 3) (var 5) ⟶ height (var 4) (var 5) ⟶ le (amp (var 5)) (var 1) ⟶
      Fm.iff (QuadraticTowerDifferenceIdentities.less (var 0) (var 1) (var 2) (scalarArray (var 0) (var 3)) (scalarArray (var 0) (var 4)))
        (rationalLess (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (scalar_order_iff _ _ _ _ _ (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))
theorem actual_scalar_tower_nonstrict_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ height (var 3) (var 5) ⟶ height (var 4) (var 5) ⟶ le (amp (var 5)) (var 1) ⟶
      Fm.iff (QuadraticTowerDifferenceIdentities.equivalent (var 0) (var 1) (var 2) (scalarArray (var 0) (var 3)) (scalarArray (var 0) (var 4)) ⋎
        QuadraticTowerDifferenceIdentities.less (var 0) (var 1) (var 2) (scalarArray (var 0) (var 3)) (scalarArray (var 0) (var 4)))
          (RationalArgmin.rationalLE (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (scalar_nonstrict_iff _ _ _ _ _ (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))
theorem actual_scalar_difference_order_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_scalar_equality_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ height (var 3) (var 5) ⟶ height (var 4) (var 5) ⟶ le (amp (var 5)) (var 1) ⟶
      Fm.iff (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ zero) (RationalArgmin.rationalEq (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (returned_equality_iff _ _ _ _ _ (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))
theorem actual_returned_scalar_order_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ height (var 3) (var 5) ⟶ height (var 4) (var 5) ⟶ le (amp (var 5)) (var 1) ⟶
      Fm.iff (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ one) (rationalLess (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (returned_order_iff _ _ _ _ _ (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))

end LeanProofs.IPRA.Algebra.QuadraticTowerScalarDifferenceOrder
