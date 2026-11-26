import IPRADerivations.Algebra.QuadraticTowerMultiplicationUnit

/-!
# Constructed addition, normalization and extension halves

Literal identities apply to the actual checked sequence constructors.
Arbitrary raw input array codes are compared only by bounded rational
coefficient values. The joined-sum law keeps its actual stored-width
premises. These laws supply the original multiplication distributivity
proof without an outer-list extensionality principle.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerAdditionLaws

open_ipra
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width)
open QuadraticTowerArrayCodec (normalized)
open QuadraticTowerCoefficientArithmetic (added equalValues)
open QuadraticTowerMultiplicationTable (leftHalf rightHalf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length append entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (sequence_equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem normalized_congr (h : PTm n) {A C : PTm n} (e : Γ ⊢[PRAAx] A ≐ C) : Γ ⊢[PRAAx]
    normalized h A ≐ normalized h C := QuadraticTowerMultiplicationZero.sequence_congr _ (.eqRefl _) e

theorem added_values_congr (h A A' C C' : PTm n) (ha : Γ ⊢[PRAAx] equalValues h A A')
    (hc : Γ ⊢[PRAAx] equalValues h C C') : Γ ⊢[PRAAx] added h A C ≐ added h A' C' :=
  (QuadraticTowerArrayNormalization.normalized_added h A C).eqSymm.eqTrans
    ((QuadraticTowerArrayNormalization.normalized_proper h _ _
      (QuadraticTowerCoefficientArithmetic.added_proper h A A' C C' ha hc)).eqTrans
        (QuadraticTowerArrayNormalization.normalized_added h A' C'))

theorem added_normalized (h A C : PTm n) : Γ ⊢[PRAAx] added h (normalized h A) (normalized h C) ≐ added h A C :=
  added_values_congr h _ A _ C (QuadraticTowerOperandProperness.normalized_values h A)
    (QuadraticTowerOperandProperness.normalized_values h C)

theorem add_body_lookup (h A C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    inst2 QuadraticTowerCoefficientArithmetic.addBody i (pairT A C) ≐ entry (added h A C) i :=
  (QuadraticTowerCoefficientArithmetic.add_body_at A C i).eqTrans (QuadraticTowerCoefficientArithmetic.added_lookup h A C i hi).eqSymm

theorem added_associative (h A C E : PTm n) : Γ ⊢[PRAAx] added h (added h A C) E ≐ added h A (added h C E) := by
  apply sequence_equal QuadraticTowerCoefficientArithmetic.addBody QuadraticTowerCoefficientArithmetic.addBody
    (width h) (pairT (added h A C) E) (pairT A (added h C E))
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have value := (add_body_lookup (Γ := Δ) (Syn.shift h) (added (Syn.shift h) (Syn.shift A) (Syn.shift C)) (Syn.shift E) (var 0) Prf.hyp0).eqTrans
    ((QuadraticTowerCoefficientArithmetic.added_associative_at _ _ _ _ _ Prf.hyp0).eqTrans
      (add_body_lookup _ _ _ _ Prf.hyp0).eqSymm)
  simpa only [Δ,Syn.shift,QuadraticTowerCoefficients.subst_width,QuadraticTowerCoefficientArithmetic.subst_added,subst_pairT] using value

theorem added_four (h A C E F : PTm n) : Γ ⊢[PRAAx]
    added h (added h A C) (added h E F) ≐ added h (added h A E) (added h C F) :=
  (added_associative h A C (added h E F)).eqTrans
    ((QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (.eqRefl A) (added_associative h C E F).eqSymm).eqTrans
      ((QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (.eqRefl A)
        (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h)
          (QuadraticTowerMultiplicationCommutativity.added_commutative h C E) (.eqRefl F))).eqTrans
        ((QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (.eqRefl A) (added_associative h E C F)).eqTrans
          (added_associative h A E (added h C F)).eqSymm)))

theorem left_added (h A C : PTm n) : Γ ⊢[PRAAx]
    leftHalf h (added (succ h) A C) ≐ added h (leftHalf h A) (leftHalf h C) := by
  apply sequence_equal Foundations.RealizerComposition.sliceBody QuadraticTowerCoefficientArithmetic.addBody
    (width h) (pairT zero (added (succ h) A C)) (pairT (leftHalf h A) (leftHalf h C))
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (succ (Syn.shift h))) :=
    lt_of_lt_of_le Prf.hyp0 (QuadraticTowerCoefficientArithmetic.width_le_next _)
  have actual := (Foundations.RealizerComposition.sliceBody_at (Γ := Δ)
    (added (succ (Syn.shift h)) (Syn.shift A) (Syn.shift C)) zero (var 0)).eqTrans
      ((entry_congr (.eqRefl _) (zero_add _)).eqTrans (QuadraticTowerCoefficientArithmetic.added_lookup _ _ _ _ hi))
  have left : Δ ⊢[PRAAx] entry (leftHalf (Syn.shift h) (Syn.shift A)) (var 0) ≐ entry (Syn.shift A) (var 0) :=
    (Foundations.RealizerComposition.slice_lookup _ zero _ _ Prf.hyp0).eqTrans (entry_congr (.eqRefl _) (zero_add _))
  have right : Δ ⊢[PRAAx] entry (leftHalf (Syn.shift h) (Syn.shift C)) (var 0) ≐ entry (Syn.shift C) (var 0) :=
    (Foundations.RealizerComposition.slice_lookup _ zero _ _ Prf.hyp0).eqTrans (entry_congr (.eqRefl _) (zero_add _))
  have value := actual.eqTrans ((RationalAlgebra.add_congr left.eqSymm right.eqSymm).eqTrans
    (QuadraticTowerCoefficientArithmetic.add_body_at _ _ _).eqSymm)
  simpa only [Δ,Syn.shift,subst_pairT,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
    QuadraticTowerCoefficientArithmetic.subst_added,QuadraticTowerMultiplicationTable.subst_leftHalf,QuadraticTowerCoefficients.subst_width] using value

theorem right_added (h A C : PTm n) : Γ ⊢[PRAAx]
    rightHalf h (added (succ h) A C) ≐ added h (rightHalf h A) (rightHalf h C) := by
  apply sequence_equal Foundations.RealizerComposition.sliceBody QuadraticTowerCoefficientArithmetic.addBody
    (width h) (pairT (width h) (added (succ h) A C)) (pairT (rightHalf h A) (rightHalf h C))
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi := QuadraticTowerCoefficientArithmetic.right_half_bound (Γ := Δ) (Syn.shift h) (var 0) Prf.hyp0
  have actual := (Foundations.RealizerComposition.sliceBody_at (Γ := Δ)
    (added (succ (Syn.shift h)) (Syn.shift A) (Syn.shift C)) (width (Syn.shift h)) (var 0)).eqTrans
      (QuadraticTowerCoefficientArithmetic.added_lookup _ _ _ _ hi)
  have value := actual.eqTrans ((RationalAlgebra.add_congr
    (Foundations.RealizerComposition.slice_lookup (Syn.shift A) (width (Syn.shift h)) _ _ Prf.hyp0).eqSymm
    (Foundations.RealizerComposition.slice_lookup (Syn.shift C) (width (Syn.shift h)) _ _ Prf.hyp0).eqSymm).eqTrans
      (QuadraticTowerCoefficientArithmetic.add_body_at _ _ _).eqSymm)
  simpa only [Δ,Syn.shift,subst_pairT,ConciseIPRA.PTm.subst_succ,QuadraticTowerCoefficients.subst_width,
    QuadraticTowerCoefficientArithmetic.subst_added,QuadraticTowerMultiplicationTable.subst_rightHalf,QuadraticTowerMultiplicationTable.rightHalf,Foundations.RealizerComposition.subst_slice] using value

theorem left_added_join (h A B C D : PTm n) (hA : Γ ⊢[PRAAx] length A ≐ width h)
    (hC : Γ ⊢[PRAAx] length C ≐ width h) : Γ ⊢[PRAAx]
    leftHalf h (added (succ h) (append A B) (append C D)) ≐ added h A C := by
  have as : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift A) ≐ width (Syn.shift h) := by simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using hA.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ width (Syn.shift h) := by simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using hC.shift
  apply sequence_equal Foundations.RealizerComposition.sliceBody QuadraticTowerCoefficientArithmetic.addBody
    (width h) (pairT zero (added (succ h) (append A B) (append C D))) (pairT A C)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have value := (Foundations.RealizerComposition.sliceBody_at (Γ := Δ)
    (added (succ (Syn.shift h)) (append (Syn.shift A) (Syn.shift B)) (append (Syn.shift C) (Syn.shift D))) zero (var 0)).eqTrans
      ((entry_congr (.eqRefl _) (zero_add _)).eqTrans
        ((QuadraticTowerCoefficientArithmetic.added_join_left _ _ _ _ _ _ as.wk cs.wk Prf.hyp0).eqTrans
          (add_body_lookup _ _ _ _ Prf.hyp0).eqSymm))
  simpa only [Δ,Syn.shift,subst_pairT,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
    QuadraticTowerCoefficientArithmetic.subst_added,Foundations.SequenceComposition.subst_append,QuadraticTowerCoefficients.subst_width] using value

theorem right_added_join (h A B C D : PTm n) (hA : Γ ⊢[PRAAx] length A ≐ width h)
    (hB : Γ ⊢[PRAAx] length B ≐ width h) (hC : Γ ⊢[PRAAx] length C ≐ width h)
    (hD : Γ ⊢[PRAAx] length D ≐ width h) : Γ ⊢[PRAAx]
    rightHalf h (added (succ h) (append A B) (append C D)) ≐ added h B D := by
  have as : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift A) ≐ width (Syn.shift h) := by simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using hA.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift B) ≐ width (Syn.shift h) := by simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using hB.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ width (Syn.shift h) := by simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using hC.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift D) ≐ width (Syn.shift h) := by simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using hD.shift
  apply sequence_equal Foundations.RealizerComposition.sliceBody QuadraticTowerCoefficientArithmetic.addBody
    (width h) (pairT (width h) (added (succ h) (append A B) (append C D))) (pairT B D)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have value := (Foundations.RealizerComposition.sliceBody_at (Γ := Δ)
    (added (succ (Syn.shift h)) (append (Syn.shift A) (Syn.shift B)) (append (Syn.shift C) (Syn.shift D))) (width (Syn.shift h)) (var 0)).eqTrans
      ((QuadraticTowerCoefficientArithmetic.added_join_right _ _ _ _ _ _ as.wk bs.wk cs.wk ds.wk Prf.hyp0).eqTrans
        (add_body_lookup _ _ _ _ Prf.hyp0).eqSymm)
  simpa only [Δ,Syn.shift,subst_pairT,ConciseIPRA.PTm.subst_succ,QuadraticTowerCoefficients.subst_width,
    QuadraticTowerCoefficientArithmetic.subst_added,Foundations.SequenceComposition.subst_append] using value

theorem added_join (h A B C D : PTm n) (hA : Γ ⊢[PRAAx] length A ≐ width h)
    (hB : Γ ⊢[PRAAx] length B ≐ width h) (hC : Γ ⊢[PRAAx] length C ≐ width h)
    (hD : Γ ⊢[PRAAx] length D ≐ width h) : Γ ⊢[PRAAx]
    added (succ h) (append A B) (append C D) ≐ append (added h A C) (added h B D) := by
  let X := added (succ h) (append A B) (append C D)
  have left := (normalized_congr h (left_added_join h A B C D hA hC)).eqTrans
    (QuadraticTowerArrayNormalization.normalized_added h A C)
  have right := (normalized_congr h (right_added_join h A B C D hA hB hC hD)).eqTrans
    (QuadraticTowerArrayNormalization.normalized_added h B D)
  have whole : Γ ⊢[PRAAx] append (normalized h (leftHalf h X)) (normalized h (rightHalf h X)) ≐ X :=
    (QuadraticTowerMultiplicationUnit.normalized_join h X).eqTrans (QuadraticTowerArrayNormalization.normalized_added _ _ _)
  exact whole.eqSymm.eqTrans (QuadraticTowerCoefficients.append_congr left right)

theorem added_singletons (a c : PTm n) : Γ ⊢[PRAAx]
    added zero (QuadraticTowerCoefficients.singleton a) (QuadraticTowerCoefficients.singleton c) ≐
      QuadraticTowerCoefficients.singleton (RationalArithmetic.add a c) := by
  have head : Γ ⊢[PRAAx] entry (added zero (QuadraticTowerCoefficients.singleton a) (QuadraticTowerCoefficients.singleton c)) zero ≐
      RationalArithmetic.add a c :=
    (QuadraticTowerCoefficientArithmetic.added_lookup _ _ _ _ QuadraticTowerCoefficientArithmetic.base_index).eqTrans
      (RationalAlgebra.add_congr (QuadraticTowerCoefficients.singleton_entry a) (QuadraticTowerCoefficients.singleton_entry c))
  have scalar := (QuadraticTowerArrayNormalization.recode_congr head).eqTrans
    (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.add_guard a c))
  exact (QuadraticTowerArrayNormalization.normalized_added zero _ _).eqSymm.eqTrans
    ((QuadraticTowerMultiplicationUnit.normalized_base _).eqTrans
      (QuadraticTowerMultiplicationZero.sequence_congr (var 1) (.eqRefl one) scalar))

theorem original_add_program_associative (h A C E : PTm n) : Γ ⊢[PRAAx]
    ap3 QuadraticTowerCoefficientArithmetic.addF h (ap3 QuadraticTowerCoefficientArithmetic.addF h A C) E ≐
      ap3 QuadraticTowerCoefficientArithmetic.addF h A (ap3 QuadraticTowerCoefficientArithmetic.addF h C E) :=
  (QuadraticTowerCoefficientArithmetic.add_program_at _ _ _).eqTrans
    ((QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (QuadraticTowerCoefficientArithmetic.add_program_at h A C) (.eqRefl E)).eqTrans
      ((added_associative h A C E).eqTrans
        ((QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) (.eqRefl A)
          (QuadraticTowerCoefficientArithmetic.add_program_at h C E).eqSymm).eqTrans
            (QuadraticTowerCoefficientArithmetic.add_program_at _ _ _).eqSymm)))

theorem actual_constructed_addition_associative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (added (var 0) (added (var 0) (var 1) (var 2)) (var 3) ≐ added (var 0) (var 1) (added (var 0) (var 2) (var 3))) := closeUniv 4 (added_associative _ _ _ _)
theorem actual_constructed_addition_four_terms_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (added (var 0) (added (var 0) (var 1) (var 2)) (added (var 0) (var 3) (var 4)) ≐
      added (var 0) (added (var 0) (var 1) (var 3)) (added (var 0) (var 2) (var 4))) := closeUniv 5 (added_four _ _ _ _ _)
theorem actual_addition_normalized_inputs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (added (var 0) (normalized (var 0) (var 1)) (normalized (var 0) (var 2)) ≐ added (var 0) (var 1) (var 2)) := closeUniv 3 (added_normalized _ _ _)
theorem original_rational_values_actual_addition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (equalValues (var 0) (var 1) (var 2) ⟶ equalValues (var 0) (var 3) (var 4) ⟶
      added (var 0) (var 1) (var 3) ≐ added (var 0) (var 2) (var 4)) :=
  closeUniv 5 (.impI (.impI (added_values_congr _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_addition_halves_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((leftHalf (var 0) (added (succ (var 0)) (var 1) (var 2)) ≐ added (var 0) (leftHalf (var 0) (var 1)) (leftHalf (var 0) (var 2))) ⋏
      (rightHalf (var 0) (added (succ (var 0)) (var 1) (var 2)) ≐ added (var 0) (rightHalf (var 0) (var 1)) (rightHalf (var 0) (var 2)))) :=
  closeUniv 3 (.andI (left_added _ _ _) (right_added _ _ _))
theorem original_widths_actual_joined_addition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 1) ≐ width (var 0) ⟶ length (var 2) ≐ width (var 0) ⟶ length (var 3) ≐ width (var 0) ⟶ length (var 4) ≐ width (var 0) ⟶
      added (succ (var 0)) (append (var 1) (var 2)) (append (var 3) (var 4)) ≐ append (added (var 0) (var 1) (var 3)) (added (var 0) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (added_join _ _ _ _ _ (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))
theorem original_addition_program_associative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap3 QuadraticTowerCoefficientArithmetic.addF (var 0) (ap3 QuadraticTowerCoefficientArithmetic.addF (var 0) (var 1) (var 2)) (var 3) ≐
      ap3 QuadraticTowerCoefficientArithmetic.addF (var 0) (var 1) (ap3 QuadraticTowerCoefficientArithmetic.addF (var 0) (var 2) (var 3))) := closeUniv 4 (original_add_program_associative _ _ _ _)

end LeanProofs.IPRA.Algebra.QuadraticTowerAdditionLaws
