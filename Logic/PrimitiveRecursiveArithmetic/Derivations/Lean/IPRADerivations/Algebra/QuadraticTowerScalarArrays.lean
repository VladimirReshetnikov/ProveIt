import IPRADerivations.Algebra.QuadraticTowerArrayNormalization

/-!
# Actual scalar and zero coefficient arrays at numerical tower depth

The scalar is stored canonically at coefficient0, followed by actual zero
coefficients. The programs have width2^h and use only the original checked
sequence constructor. Their bounded representation and half laws supply
the scalar-embedding sign proof; arbitrary outer codes are never equated
from their entries.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerScalarArrays

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width)
open QuadraticTowerArrayCodec (arrayHeight)
open QuadraticTowerScalarBudget (height)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (sequence_equal)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero sel_cases)
open LeanProofs.IPRA.Foundations.BoundedReflection
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zeroScalar : PTm n := QuadraticRationalEmbedding.zeroScalar
def zeroBody : PTm 2 := zeroScalar
def zeroArray (h : PTm n) : PTm n := sequence zeroBody (width h) zero
def cell (i q : PTm n) : PTm n := sel (eqb i zero) (RationalArithmetic.recode q) zeroScalar
def scalarBody : PTm 2 := cell (var 0) (var 1)
def scalarArray (h q : PTm n) : PTm n := sequence scalarBody (width h) q
@[simp] theorem subst_zeroScalar {k : ℕ} (σ : Fin n → PTm k) :
    Syn.subst σ (zeroScalar : PTm n) = (zeroScalar : PTm k) := by simp [zeroScalar]
@[simp] theorem subst_zeroArray {k : ℕ} (σ : Fin n → PTm k) (h : PTm n) :
    Syn.subst σ (zeroArray h) = zeroArray (Syn.subst σ h) := by simp [zeroArray]
@[simp] theorem subst_cell {k : ℕ} (σ : Fin n → PTm k) (i q : PTm n) :
    Syn.subst σ (cell i q) = cell (Syn.subst σ i) (Syn.subst σ q) := by simp [cell,sel]
@[simp] theorem subst_scalarArray {k : ℕ} (σ : Fin n → PTm k) (h q : PTm n) :
    Syn.subst σ (scalarArray h q) = scalarArray (Syn.subst σ h) (Syn.subst σ q) := by simp [scalarArray]

theorem width_positive (h : PTm n) : Γ ⊢[PRAAx] le one (width h) :=
  Foundations.RuntimeWordAppend.power_positive two h (le_succ_self one)
theorem zero_canonical : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (zeroScalar : PTm n) :=
  RationalNormalForm.normalize_well_formed _ one (le_refl _)
theorem zero_height (b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] height zeroScalar b := by
  have z : Γ ⊢[PRAAx] le (Foundations.GapDecision.zabs (ZT.ofNat (zero : PTm n))) b :=
    le_congr ((congrAdd (monus_self zero) (monus_self zero)).eqTrans (zero_add zero)).eqSymm (.eqRefl _) (zero_le b)
  exact QuadraticTowerScalarBudget.normalize_height (ZT.ofNat zero) one b (le_refl _) z hb
theorem zero_recode : Γ ⊢[PRAAx] RationalArithmetic.recode (zeroScalar : PTm n) ≐ zeroScalar :=
  RationalNormalForm.normalize_fixed_point _ zero_canonical

theorem zero_numerator_parts : Γ ⊢[PRAAx]
    ((RationalSupMetric.numeratorOf (zeroScalar : PTm n)).pos ≐ zero) ⋏
      ((RationalSupMetric.numeratorOf (zeroScalar : PTm n)).neg ≐ zero) := by
  have parts := RationalNormalForm.code_parts (Γ := Γ)
    (RationalIntegerNormalization.reducedNumerator (ZT.ofNat zero) one)
    (RationalIntegerNormalization.reducedDenominator (ZT.ofNat zero) one)
  exact .andI ((Prf.andE₁ parts).eqTrans ((congrAp2 quoF (monus_self zero) (.eqRefl _)).eqTrans (quo_zero _)))
    ((Prf.andE₂ parts).eqTrans ((congrAp2 quoF (monus_self zero) (.eqRefl _)).eqTrans (quo_zero _)))

theorem zero_native_tag : Γ ⊢[PRAAx] QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf (zeroScalar : PTm n)) ≐ zero :=
  QuadraticSignCertificates.tag_zero _
    ((congrMonus (Prf.andE₁ zero_numerator_parts) (Prf.andE₂ zero_numerator_parts)).eqTrans (monus_self zero))
    ((congrMonus (Prf.andE₂ zero_numerator_parts) (Prf.andE₁ zero_numerator_parts)).eqTrans (monus_self zero))

theorem zero_length (h : PTm n) : Γ ⊢[PRAAx] length (zeroArray h) ≐ width h := sequence_length _ _ _
theorem scalar_length (h q : PTm n) : Γ ⊢[PRAAx] length (scalarArray h q) ≐ width h := sequence_length _ _ _
theorem zero_body_at (i x : PTm n) : inst2 zeroBody i x = zeroScalar := by simp [zeroBody,inst2]
theorem scalar_body_at (i q : PTm n) : inst2 scalarBody i q = cell i q := by simp [scalarBody,inst2]
theorem zero_lookup (h i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx] entry (zeroArray h) i ≐ zeroScalar := by
  simpa only [zeroArray,zero_body_at] using sequence_decode (Γ := Γ) zeroBody (x := zero) hi
theorem scalar_lookup (h q i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx] entry (scalarArray h q) i ≐ cell i q := by
  simpa only [scalarArray,scalar_body_at] using sequence_decode (Γ := Γ) scalarBody (x := q) hi
theorem cell_zero (i q : PTm n) (hi : Γ ⊢[PRAAx] i ≐ zero) : Γ ⊢[PRAAx] cell i q ≐ RationalArithmetic.recode q :=
  sel_one (eqb_of_eq hi)
theorem cell_nonzero (i q : PTm n) (hi : Γ ⊢[PRAAx] neg (i ≐ zero)) : Γ ⊢[PRAAx] cell i q ≐ zeroScalar :=
  sel_zero (eqb_of_ne hi)
theorem cell_canonical (i q : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (cell i q) :=
  .orE (sel_cases (eqb_cases i zero))
    (RationalArithmetic.guard_congr Prf.hyp0 (RationalArithmetic.recode_guard q))
    (RationalArithmetic.guard_congr Prf.hyp0 zero_canonical)
theorem cell_height (i q b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hq : Γ ⊢[PRAAx] height q b) : Γ ⊢[PRAAx] height (cell i q) b :=
  .orE (sel_cases (eqb_cases i zero))
    (QuadraticTowerScalarBudget.height_congr Prf.hyp0.eqSymm (.eqRefl _) (QuadraticTowerScalarBudget.recode_height q b hq.wk))
    (QuadraticTowerScalarBudget.height_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_height b hb.wk))

theorem zero_array_height (h b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] arrayHeight h (zeroArray h) b := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using hb.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_zeroArray] using QuadraticTowerScalarBudget.height_congr
    (zero_lookup (Syn.shift h) (var 0) Prf.hyp0).eqSymm (.eqRefl _) (zero_height (Syn.shift b) hs.wk)
theorem scalar_array_height (h q b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hq : Γ ⊢[PRAAx] height q b) : Γ ⊢[PRAAx]
    arrayHeight h (scalarArray h q) b := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hb.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] height (Syn.shift q) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerScalarBudget.subst_height,Syn.shift] using hq.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_scalarArray] using QuadraticTowerScalarBudget.height_congr
    (scalar_lookup (Syn.shift h) (Syn.shift q) (var 0) Prf.hyp0).eqSymm (.eqRefl _)
      (cell_height (var 0) (Syn.shift q) (Syn.shift b) hs.wk qs.wk)

theorem zero_at_zero (h : PTm n) : Γ ⊢[PRAAx] entry (zeroArray h) zero ≐ zeroScalar :=
  zero_lookup h zero (width_positive h)
theorem scalar_at_zero (h q : PTm n) : Γ ⊢[PRAAx] entry (scalarArray h q) zero ≐ RationalArithmetic.recode q :=
  (scalar_lookup h q zero (width_positive h)).eqTrans (cell_zero zero q (.eqRefl _))

theorem normalized_zero (h : PTm n) : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.normalized h (zeroArray h) ≐ zeroArray h := by
  apply sequence_equal QuadraticTowerArrayCodec.normalizeBody zeroBody (width h) (zeroArray h) zero
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have value : Δ ⊢[PRAAx] RationalArithmetic.recode (entry (zeroArray (Syn.shift h)) (var 0)) ≐ zeroScalar :=
    (QuadraticTowerArrayNormalization.recode_congr (zero_lookup _ _ Prf.hyp0)).eqTrans zero_recode
  simpa only [Δ,Syn.shift,QuadraticTowerArrayCodec.normalize_body_at,zero_body_at,subst_zeroArray,
    QuadraticTowerCoefficients.subst_width,subst_zeroScalar] using value

theorem normalized_scalar (h q : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerArrayCodec.normalized h (scalarArray h q) ≐ scalarArray h q := by
  apply sequence_equal QuadraticTowerArrayCodec.normalizeBody scalarBody (width h) (scalarArray h q) q
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have value : Δ ⊢[PRAAx] RationalArithmetic.recode (entry (scalarArray (Syn.shift h) (Syn.shift q)) (var 0)) ≐
      cell (var 0) (Syn.shift q) :=
    (QuadraticTowerArrayNormalization.recode_congr (scalar_lookup _ _ _ Prf.hyp0)).eqTrans
      (RationalNormalForm.normalize_fixed_point _ (cell_canonical _ _))
  simpa only [Δ,Syn.shift,QuadraticTowerArrayCodec.normalize_body_at,scalar_body_at,subst_scalarArray,
    QuadraticTowerCoefficients.subst_width] using value

theorem offset_nonzero (h i : PTm n) : Γ ⊢[PRAAx] neg (width h+i ≐ zero) := by
  have positive : Γ ⊢[PRAAx] le one (width h+i) := le_trans (width_positive h) (le_add_right _ _)
  exact .impI (not_succ_le_self zero .bot (le_congr (.eqRefl _) Prf.hyp0 positive.wk))

theorem left_zero (h : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.leftHalf h (zeroArray (succ h)) ≐ zeroArray h := by
  apply sequence_equal Foundations.RealizerComposition.sliceBody zeroBody (width h) (pairT zero (zeroArray (succ h))) zero
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (succ (Syn.shift h))) :=
    lt_of_lt_of_le Prf.hyp0 (QuadraticTowerCoefficientArithmetic.width_le_next _)
  have value := (Foundations.RealizerComposition.sliceBody_at (Γ := Δ) (zeroArray (succ (Syn.shift h))) zero (var 0)).eqTrans
    ((entry_congr (.eqRefl _) (zero_add _)).eqTrans (zero_lookup _ _ hi))
  simpa only [Δ,Syn.shift,zero_body_at,subst_pairT,subst_zeroArray,QuadraticTowerCoefficients.subst_width,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,subst_zeroScalar] using value

theorem right_zero (h : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.rightHalf h (zeroArray (succ h)) ≐ zeroArray h := by
  apply sequence_equal Foundations.RealizerComposition.sliceBody zeroBody (width h) (pairT (width h) (zeroArray (succ h))) zero
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi := QuadraticTowerCoefficientArithmetic.right_half_bound (Γ := Δ) (Syn.shift h) (var 0) Prf.hyp0
  have value := (Foundations.RealizerComposition.sliceBody_at (Γ := Δ) (zeroArray (succ (Syn.shift h))) (width (Syn.shift h)) (var 0)).eqTrans
    (zero_lookup _ _ hi)
  simpa only [Δ,Syn.shift,zero_body_at,subst_pairT,subst_zeroArray,QuadraticTowerCoefficients.subst_width,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,subst_zeroScalar] using value

theorem left_scalar (h q : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.leftHalf h (scalarArray (succ h) q) ≐ scalarArray h q := by
  apply sequence_equal Foundations.RealizerComposition.sliceBody scalarBody (width h) (pairT zero (scalarArray (succ h) q)) q
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (succ (Syn.shift h))) :=
    lt_of_lt_of_le Prf.hyp0 (QuadraticTowerCoefficientArithmetic.width_le_next _)
  have value := (Foundations.RealizerComposition.sliceBody_at (Γ := Δ) (scalarArray (succ (Syn.shift h)) (Syn.shift q)) zero (var 0)).eqTrans
    ((entry_congr (.eqRefl _) (zero_add _)).eqTrans (scalar_lookup _ _ _ hi))
  simpa only [Δ,Syn.shift,scalar_body_at,subst_pairT,subst_scalarArray,QuadraticTowerCoefficients.subst_width,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using value

theorem right_scalar (h q : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.rightHalf h (scalarArray (succ h) q) ≐ zeroArray h := by
  apply sequence_equal Foundations.RealizerComposition.sliceBody zeroBody (width h) (pairT (width h) (scalarArray (succ h) q)) zero
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi := QuadraticTowerCoefficientArithmetic.right_half_bound (Γ := Δ) (Syn.shift h) (var 0) Prf.hyp0
  have value := (Foundations.RealizerComposition.sliceBody_at (Γ := Δ) (scalarArray (succ (Syn.shift h)) (Syn.shift q))
    (width (Syn.shift h)) (var 0)).eqTrans ((scalar_lookup _ _ _ hi).eqTrans (cell_nonzero _ _ (offset_nonzero _ _)))
  simpa only [Δ,Syn.shift,zero_body_at,subst_pairT,subst_scalarArray,QuadraticTowerCoefficients.subst_width,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,subst_zeroScalar] using value

def output (h q : PTm n) : PTm n := pairT (zeroArray h) (scalarArray h q)
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (h q : PTm n) : PTm n := ap2 outputF h q
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (h q : PTm n) :
    Syn.subst σ (output h q) = output (Syn.subst σ h) (Syn.subst σ q) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (h q : PTm n) :
    Syn.subst σ (run h q) = run (Syn.subst σ h) (Syn.subst σ q) := by simp [run]
theorem program_at (h q : PTm n) : Γ ⊢[PRAAx] run h q ≐ output h q := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![h,q]
theorem returned_zero (h q : PTm n) : Γ ⊢[PRAAx] fstT (run h q) ≐ zeroArray h :=
  (congrFst (program_at _ _)).eqTrans (fst_pair _ _)
theorem returned_scalar (h q : PTm n) : Γ ⊢[PRAAx] sndT (run h q) ≐ scalarArray h q :=
  (congrSnd (program_at _ _)).eqTrans (snd_pair _ _)

theorem actual_scalar_array_lengths_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (zeroArray (var 0)) ≐ width (var 0) ⋏ length (scalarArray (var 0) (var 1)) ≐ width (var 0)) :=
  closeUniv 2 (.andI (zero_length _) (scalar_length _ _))
theorem actual_scalar_array_original_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (entry (scalarArray (var 0) (var 1)) zero ≐ RationalArithmetic.recode (var 1)) := closeUniv 2 (scalar_at_zero _ _)
theorem actual_zero_array_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ arrayHeight (var 0) (zeroArray (var 0)) (var 1)) :=
  closeUniv 2 (.impI (zero_array_height _ _ Prf.hyp0))
theorem actual_scalar_array_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ height (var 1) (var 2) ⟶ arrayHeight (var 0) (scalarArray (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (.impI (scalar_array_height _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_scalar_array_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticTowerArrayCodec.normalized (var 0) (zeroArray (var 0)) ≐ zeroArray (var 0) ⋏
      QuadraticTowerArrayCodec.normalized (var 0) (scalarArray (var 0) (var 1)) ≐ scalarArray (var 0) (var 1)) :=
  closeUniv 2 (.andI (normalized_zero _) (normalized_scalar _ _))
theorem actual_zero_array_halves_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (QuadraticTowerMultiplicationTable.leftHalf (var 0) (zeroArray (succ (var 0))) ≐ zeroArray (var 0) ⋏
      QuadraticTowerMultiplicationTable.rightHalf (var 0) (zeroArray (succ (var 0))) ≐ zeroArray (var 0)) :=
  closeUniv 1 (.andI (left_zero _) (right_zero _))
theorem actual_scalar_array_halves_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticTowerMultiplicationTable.leftHalf (var 0) (scalarArray (succ (var 0)) (var 1)) ≐ scalarArray (var 0) (var 1) ⋏
      QuadraticTowerMultiplicationTable.rightHalf (var 0) (scalarArray (succ (var 0)) (var 1)) ≐ zeroArray (var 0)) :=
  closeUniv 2 (.andI (left_scalar _ _) (right_scalar _ _))
theorem actual_scalar_array_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)

end LeanProofs.IPRA.Algebra.QuadraticTowerScalarArrays
