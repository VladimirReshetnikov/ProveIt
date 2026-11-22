import IPRADerivations.Algebra.QuadraticTowerMultiplicationTable
import IPRADerivations.Foundations.SequenceEquality
import IPRADerivations.Analysis.RationalGaussianEmbedding

/-!
# Actual normalization of numerical quadratic-tower arrays

The actual mixed-radix restore program constructs exactly the original
canonical coefficient sequence, independently of its valid numerical cap.
Original bounded rational-value equality also gives literal equality of
these constructed normalized sequences. The genuine checked sequence
equality theorem is used throughout; arbitrary outer list codes are never
identified from their entries. Actual lower and upper slices commute with
normalization. This supplies common operands for later table coherence,
without assuming a multiplication correctness or cap-independence law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerArrayNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width width_succ)
open QuadraticTowerArrayCodec
  (arrayHeight normalized normalizeBody normalize_body_at normalized_lookup
    restored decoded digitBody data digit_body_at restored_entry)
open QuadraticTowerCoefficientArithmetic (equalValues values_at)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (agree sequence_equal)
open LeanProofs.IPRA.Foundations.RealizerComposition
  (slice sliceBody sliceBody_at slice_lookup)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem recode_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] RationalArithmetic.recode a ≐ RationalArithmetic.recode b := by
  simpa [RationalArithmetic.subst_recode] using
    Prf.eqCongr (RationalArithmetic.recode (var 0) : PTm 1)
      (σ := ![a]) (σ' := ![b]) (fun i => by fin_cases i; exact h)

theorem normalized_proper (h A C : PTm n)
    (hV : Γ ⊢[PRAAx] equalValues h A C) : Γ ⊢[PRAAx]
    normalized h A ≐ normalized h C := by
  have hs : Γ.map Fm.shift ⊢[PRAAx]
      equalValues (Syn.shift h) (Syn.shift A) (Syn.shift C) := by
    simpa only [Fm.shift,QuadraticTowerCoefficientArithmetic.subst_equalValues,Syn.shift] using hV.shift
  apply sequence_equal normalizeBody normalizeBody (width h) A C
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have value := values_at (Γ := Δ) (Syn.shift h) (Syn.shift A) (Syn.shift C)
    (var 0) hs.wk Prf.hyp0
  simpa only [Δ,agree,normalize_body_at,Syn.shift,QuadraticTowerCoefficients.subst_width] using
    RationalGaussianEmbedding.scalar_recode_equal _ _ value

theorem normalized_idempotent (h A : PTm n) : Γ ⊢[PRAAx]
    normalized h (normalized h A) ≐ normalized h A := by
  apply sequence_equal normalizeBody normalizeBody (width h) (normalized h A) A
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have value : Δ ⊢[PRAAx]
      RationalArithmetic.recode (entry (normalized (Syn.shift h) (Syn.shift A)) (var 0)) ≐
        RationalArithmetic.recode (entry (Syn.shift A) (var 0)) :=
    (recode_congr (normalized_lookup _ _ _ hi)).eqTrans
      (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.recode_guard _))
  simpa only [Δ,normalize_body_at,Syn.shift,QuadraticTowerCoefficients.subst_width,
    QuadraticTowerArrayCodec.subst_normalized] using value

theorem restored_normalized (h A B : PTm n)
    (hA : Γ ⊢[PRAAx] arrayHeight h A B) : Γ ⊢[PRAAx]
    restored h A B ≐ normalized h A := by
  have hs : Γ.map Fm.shift ⊢[PRAAx]
      arrayHeight (Syn.shift h) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,Syn.shift] using hA.shift
  apply sequence_equal digitBody normalizeBody (width h)
    (data (QuadraticTowerScalarBudget.codeCap B) (QuadraticTowerArrayCodec.code h A B)) A
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have value : Δ ⊢[PRAAx]
      inst2 digitBody (var 0) (data (QuadraticTowerScalarBudget.codeCap (Syn.shift B))
        (QuadraticTowerArrayCodec.code (Syn.shift h) (Syn.shift A) (Syn.shift B))) ≐
        RationalArithmetic.recode (entry (Syn.shift A) (var 0)) :=
    (digit_body_at _ _ _).eqTrans
      ((QuadraticTowerArrayCodec.decoded_lookup _ _ _ _ hi).eqSymm.eqTrans
        (restored_entry _ _ _ _ hs.wk hi))
  simpa only [Δ,normalize_body_at,Syn.shift,QuadraticTowerCoefficients.subst_width,
    QuadraticTowerArrayCodec.subst_data,QuadraticTowerScalarBudget.subst_codeCap,
    QuadraticTowerArrayCodec.subst_code] using value

theorem restored_cap_independent (h A B C : PTm n)
    (hB : Γ ⊢[PRAAx] arrayHeight h A B) (hC : Γ ⊢[PRAAx] arrayHeight h A C) :
    Γ ⊢[PRAAx] restored h A B ≐ restored h A C :=
  (restored_normalized h A B hB).eqTrans (restored_normalized h A C hC).eqSymm

theorem restored_proper (h A C B D : PTm n)
    (hA : Γ ⊢[PRAAx] arrayHeight h A B) (hC : Γ ⊢[PRAAx] arrayHeight h C D)
    (hV : Γ ⊢[PRAAx] equalValues h A C) : Γ ⊢[PRAAx]
    restored h A B ≐ restored h C D :=
  (restored_normalized h A B hA).eqTrans
    ((normalized_proper h A C hV).eqTrans (restored_normalized h C D hC).eqSymm)

theorem slice_normalized (h k A offset : PTm n)
    (hRange : Γ ⊢[PRAAx] le (offset+width k) (width h)) : Γ ⊢[PRAAx]
    slice (normalized h A) offset (width k) ≐ normalized k (slice A offset (width k)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx]
      le (Syn.shift offset+width (Syn.shift k)) (width (Syn.shift h)) := by
    simpa only [Fm.shift,subst_le,PTm.subst_add,QuadraticTowerCoefficients.subst_width,Syn.shift] using hRange.shift
  apply sequence_equal sliceBody normalizeBody (width k)
    (pairT offset (normalized h A)) (slice A offset (width k))
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift k)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift k)) := Prf.hyp0
  have bound : Δ ⊢[PRAAx] lt (Syn.shift offset+var 0) (width (Syn.shift h)) :=
    le_trans (Foundations.SequenceComposition.add_lt_left _ hi) hs.wk
  have value := (sliceBody_at (Γ := Δ) (normalized (Syn.shift h) (Syn.shift A))
    (Syn.shift offset) (var 0)).eqTrans
      ((normalized_lookup _ _ _ bound).eqTrans
        (recode_congr (slice_lookup (Syn.shift A) (Syn.shift offset) (width (Syn.shift k)) (var 0) hi).eqSymm))
  simpa only [Δ,normalize_body_at,Syn.shift,QuadraticTowerCoefficients.subst_width,subst_pairT,
    QuadraticTowerArrayCodec.subst_normalized,Foundations.RealizerComposition.subst_slice] using value

theorem left_half_normalized (h A : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.leftHalf h (normalized (succ h) A) ≐
      normalized h (QuadraticTowerMultiplicationTable.leftHalf h A) :=
  slice_normalized (succ h) h A zero
    (le_congr (zero_add _).eqSymm (.eqRefl _)
      (QuadraticTowerCoefficientArithmetic.width_le_next h))

theorem right_half_normalized (h A : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.rightHalf h (normalized (succ h) A) ≐
      normalized h (QuadraticTowerMultiplicationTable.rightHalf h A) :=
  slice_normalized (succ h) h A (width h)
    (le_congr (.eqRefl _) (width_succ h).eqSymm (le_refl _))

theorem normalized_added (h A C : PTm n) : Γ ⊢[PRAAx]
    normalized h (QuadraticTowerCoefficientArithmetic.added h A C) ≐
      QuadraticTowerCoefficientArithmetic.added h A C := by
  apply sequence_equal normalizeBody QuadraticTowerCoefficientArithmetic.addBody
    (width h) (QuadraticTowerCoefficientArithmetic.added h A C) (pairT A C)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have value : Δ ⊢[PRAAx] RationalArithmetic.recode
      (entry (QuadraticTowerCoefficientArithmetic.added (Syn.shift h) (Syn.shift A) (Syn.shift C)) (var 0)) ≐
        inst2 QuadraticTowerCoefficientArithmetic.addBody (var 0) (pairT (Syn.shift A) (Syn.shift C)) :=
    (RationalNormalForm.normalize_fixed_point _
      (QuadraticTowerCoefficientArithmetic.added_canonical_at _ _ _ _ hi)).eqTrans
      ((QuadraticTowerCoefficientArithmetic.added_lookup _ _ _ _ hi).eqTrans
        (QuadraticTowerCoefficientArithmetic.add_body_at _ _ _).eqSymm)
  simpa only [Δ,normalize_body_at,Syn.shift,QuadraticTowerCoefficients.subst_width,subst_pairT,
    QuadraticTowerCoefficientArithmetic.subst_added] using value

theorem normalized_negated (h A : PTm n) : Γ ⊢[PRAAx]
    normalized h (QuadraticTowerCoefficientArithmetic.negated h A) ≐
      QuadraticTowerCoefficientArithmetic.negated h A := by
  apply sequence_equal normalizeBody QuadraticTowerCoefficientArithmetic.negativeBody
    (width h) (QuadraticTowerCoefficientArithmetic.negated h A) A
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have value : Δ ⊢[PRAAx] RationalArithmetic.recode
      (entry (QuadraticTowerCoefficientArithmetic.negated (Syn.shift h) (Syn.shift A)) (var 0)) ≐
        RationalArithmetic.negative (entry (Syn.shift A) (var 0)) :=
    (RationalNormalForm.normalize_fixed_point _
      (QuadraticTowerCoefficientArithmetic.negated_canonical_at _ _ _ hi)).eqTrans
      (QuadraticTowerCoefficientArithmetic.negated_lookup _ _ _ hi)
  simpa only [Δ,normalize_body_at,QuadraticTowerCoefficientArithmetic.negative_body_at,Syn.shift,
    QuadraticTowerCoefficients.subst_width,QuadraticTowerCoefficientArithmetic.subst_negated] using value

theorem returned_restored_normalized (h A B : PTm n)
    (hA : Γ ⊢[PRAAx] arrayHeight h A B) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (QuadraticTowerArrayCodec.run h A B))) ≐ normalized h A :=
  (QuadraticTowerArrayCodec.returned_restored h A B).eqTrans (restored_normalized h A B hA)

theorem returned_cap_independent (h A B C : PTm n)
    (hB : Γ ⊢[PRAAx] arrayHeight h A B) (hC : Γ ⊢[PRAAx] arrayHeight h A C) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (QuadraticTowerArrayCodec.run h A B))) ≐
      sndT (sndT (sndT (QuadraticTowerArrayCodec.run h A C))) :=
  (returned_restored_normalized h A B hB).eqTrans (returned_restored_normalized h A C hC).eqSymm

theorem actual_normalized_values_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (equalValues (var 0) (var 1) (var 2) ⟶ normalized (var 0) (var 1) ≐ normalized (var 0) (var 2)) :=
  closeUniv 3 (.impI (normalized_proper _ _ _ Prf.hyp0))

theorem actual_normalized_idempotent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (normalized (var 0) (normalized (var 0) (var 1)) ≐ normalized (var 0) (var 1)) :=
  closeUniv 2 (normalized_idempotent _ _)

theorem actual_restored_normalized_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (arrayHeight (var 0) (var 1) (var 2) ⟶ restored (var 0) (var 1) (var 2) ≐ normalized (var 0) (var 1)) :=
  closeUniv 3 (.impI (restored_normalized _ _ _ Prf.hyp0))

theorem actual_restored_cap_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (arrayHeight (var 0) (var 1) (var 2) ⟶ arrayHeight (var 0) (var 1) (var 3) ⟶
      restored (var 0) (var 1) (var 2) ≐ restored (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (restored_cap_independent _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_restored_values_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (arrayHeight (var 0) (var 1) (var 3) ⟶ arrayHeight (var 0) (var 2) (var 4) ⟶
      equalValues (var 0) (var 1) (var 2) ⟶ restored (var 0) (var 1) (var 3) ≐ restored (var 0) (var 2) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (restored_proper _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_normalized_slice_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3+width (var 1)) (width (var 0)) ⟶
      slice (normalized (var 0) (var 2)) (var 3) (width (var 1)) ≐
        normalized (var 1) (slice (var 2) (var 3) (width (var 1)))) :=
  closeUniv 4 (.impI (slice_normalized _ _ _ _ Prf.hyp0))

theorem actual_normalized_left_half_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticTowerMultiplicationTable.leftHalf (var 0) (normalized (succ (var 0)) (var 1)) ≐
      normalized (var 0) (QuadraticTowerMultiplicationTable.leftHalf (var 0) (var 1))) :=
  closeUniv 2 (left_half_normalized _ _)

theorem actual_normalized_right_half_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticTowerMultiplicationTable.rightHalf (var 0) (normalized (succ (var 0)) (var 1)) ≐
      normalized (var 0) (QuadraticTowerMultiplicationTable.rightHalf (var 0) (var 1))) :=
  closeUniv 2 (right_half_normalized _ _)

theorem actual_normalized_addition_fixed_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (normalized (var 0) (QuadraticTowerCoefficientArithmetic.added (var 0) (var 1) (var 2)) ≐
      QuadraticTowerCoefficientArithmetic.added (var 0) (var 1) (var 2)) :=
  closeUniv 3 (normalized_added _ _ _)

theorem actual_normalized_negative_fixed_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (normalized (var 0) (QuadraticTowerCoefficientArithmetic.negated (var 0) (var 1)) ≐
      QuadraticTowerCoefficientArithmetic.negated (var 0) (var 1)) :=
  closeUniv 2 (normalized_negated _ _)

theorem actual_returned_restored_normalized_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (arrayHeight (var 0) (var 1) (var 2) ⟶
      sndT (sndT (sndT (QuadraticTowerArrayCodec.run (var 0) (var 1) (var 2)))) ≐ normalized (var 0) (var 1)) :=
  closeUniv 3 (.impI (returned_restored_normalized _ _ _ Prf.hyp0))

theorem actual_returned_cap_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (arrayHeight (var 0) (var 1) (var 2) ⟶ arrayHeight (var 0) (var 1) (var 3) ⟶
      sndT (sndT (sndT (QuadraticTowerArrayCodec.run (var 0) (var 1) (var 2)))) ≐
        sndT (sndT (sndT (QuadraticTowerArrayCodec.run (var 0) (var 1) (var 3))))) :=
  closeUniv 4 (.impI (.impI (returned_cap_independent _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticTowerArrayNormalization
