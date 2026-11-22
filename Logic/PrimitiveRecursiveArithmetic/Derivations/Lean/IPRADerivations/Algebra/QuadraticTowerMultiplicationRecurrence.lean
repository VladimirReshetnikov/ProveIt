import IPRADerivations.Algebra.QuadraticTowerAdditionLaws

/-!
# Original operands and normalized outputs of the actual tower recipe

The actual five-call recipe ignores replacement of raw original operands
by their checked coefficient normalization. This gives the true successor
query on ORIGINAL operands under only their original height guards. Actual
query outputs are fixed by coefficient normalization; no raw input eta or
multiplication correctness law is assumed. These are suppliers for the
remaining finite ring identities.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width singleton)
open QuadraticTowerArrayCodec (arrayHeight normalized)
open QuadraticTowerCoefficientArithmetic (added equalValues)
open QuadraticTowerMultiplicationTable (lookup budget recipe leftHalf rightHalf query)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length append entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem lookup_normalized (h B T A C : PTm n) : Γ ⊢[PRAAx]
    lookup h B T (normalized h A) (normalized h C) ≐ lookup h B T A C :=
  QuadraticTowerOperandProperness.lookup_proper h B T _ A _ C
    (QuadraticTowerOperandProperness.normalized_values h A) (QuadraticTowerOperandProperness.normalized_values h C)

theorem recipe_normalized (h B T D A C : PTm n) : Γ ⊢[PRAAx]
    recipe h B T D (normalized (succ h) A) (normalized (succ h) C) ≐ recipe h B T D A C := by
  let K := budget h B D
  have ac := (QuadraticTowerMultiplicationCoherence.lookup_congr (Γ := Γ) (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (QuadraticTowerArrayNormalization.left_half_normalized h A) (QuadraticTowerArrayNormalization.left_half_normalized h C)).eqTrans
      (lookup_normalized h K T _ _)
  have be := (QuadraticTowerMultiplicationCoherence.lookup_congr (Γ := Γ) (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (QuadraticTowerArrayNormalization.right_half_normalized h A) (QuadraticTowerArrayNormalization.right_half_normalized h C)).eqTrans
      (lookup_normalized h K T _ _)
  have bed := QuadraticTowerMultiplicationCoherence.lookup_congr (Γ := Γ) (.eqRefl h) (.eqRefl K) (.eqRefl T) be (.eqRefl (entry D h))
  have ae := (QuadraticTowerMultiplicationCoherence.lookup_congr (Γ := Γ) (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (QuadraticTowerArrayNormalization.left_half_normalized h A) (QuadraticTowerArrayNormalization.right_half_normalized h C)).eqTrans
      (lookup_normalized h K T _ _)
  have bc := (QuadraticTowerMultiplicationCoherence.lookup_congr (Γ := Γ) (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (QuadraticTowerArrayNormalization.right_half_normalized h A) (QuadraticTowerArrayNormalization.left_half_normalized h C)).eqTrans
      (lookup_normalized h K T _ _)
  exact QuadraticTowerCoefficients.append_congr
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) ac bed)
    (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) ae bc)

theorem query_succ_original (h B D A C : PTm n)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C B) : Γ ⊢[PRAAx]
    query (succ h) B D A C ≐ recipe h B (QuadraticTowerMultiplicationTable.table h (budget h B D) D) D A C :=
  (QuadraticTowerOperandProperness.query_succ_normalized h B D A C ha hc).eqTrans (recipe_normalized _ _ _ _ _ _)

theorem step_lookup_original (h B T D A C : PTm n)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C B) : Γ ⊢[PRAAx]
    lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A C ≐ recipe h B T D A C :=
  (QuadraticTowerMultiplicationCoherence.step_lookup_normalized h B T D A C ha hc).eqTrans (recipe_normalized _ _ _ _ _ _)

def firstComponent (h B T D A C : PTm n) : PTm n := added h
  (lookup h (budget h B D) T (leftHalf h A) (leftHalf h C))
  (lookup h (budget h B D) T (lookup h (budget h B D) T (rightHalf h A) (rightHalf h C)) (entry D h))
def secondComponent (h B T D A C : PTm n) : PTm n := added h
  (lookup h (budget h B D) T (leftHalf h A) (rightHalf h C))
  (lookup h (budget h B D) T (rightHalf h A) (leftHalf h C))
@[simp] theorem subst_firstComponent {k : ℕ} (σ : Fin n → PTm k) (h B T D A C : PTm n) :
    Syn.subst σ (firstComponent h B T D A C) = firstComponent (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [firstComponent]
@[simp] theorem subst_secondComponent {k : ℕ} (σ : Fin n → PTm k) (h B T D A C : PTm n) :
    Syn.subst σ (secondComponent h B T D A C) = secondComponent (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [secondComponent]
theorem recipe_components (h B T D A C : PTm n) : Γ ⊢[PRAAx]
    recipe h B T D A C ≐ append (firstComponent h B T D A C) (secondComponent h B T D A C) := .eqRefl _

theorem left_join_values (h A C : PTm n) (ha : Γ ⊢[PRAAx] length A ≐ width h) : Γ ⊢[PRAAx]
    equalValues h (leftHalf h (append A C)) A := by
  have as : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift A) ≐ width (Syn.shift h) := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using ha.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have eq := (Foundations.RealizerComposition.slice_lookup (Γ := Δ) (append (Syn.shift A) (Syn.shift C)) zero _ _ Prf.hyp0).eqTrans
    ((entry_congr (.eqRefl _) (zero_add _)).eqTrans
      (Foundations.SequenceComposition.append_left (lt_congr (.eqRefl _) as.wk.eqSymm Prf.hyp0)))
  have value := RationalArgmin.rationalEq_congr (Γ := Δ) eq.eqSymm (.eqRefl _) (.eqRefl _)
  simpa only [Δ,Syn.shift,QuadraticTowerCoefficients.subst_width,Foundations.SequenceComposition.subst_append,
    QuadraticTowerMultiplicationTable.subst_leftHalf,QuadraticTowerMultiplicationTable.leftHalf,Foundations.RealizerComposition.subst_slice,ConciseIPRA.PTm.subst_zero] using value

theorem right_join_values (h A C : PTm n) (ha : Γ ⊢[PRAAx] length A ≐ width h)
    (hc : Γ ⊢[PRAAx] length C ≐ width h) : Γ ⊢[PRAAx] equalValues h (rightHalf h (append A C)) C := by
  have as : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift A) ≐ width (Syn.shift h) := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using ha.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ width (Syn.shift h) := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using hc.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have eq := (Foundations.RealizerComposition.slice_lookup (Γ := Δ) (append (Syn.shift A) (Syn.shift C)) (width (Syn.shift h)) _ _ Prf.hyp0).eqTrans
    ((entry_congr (.eqRefl _) (congrAdd as.wk.eqSymm (.eqRefl _))).eqTrans
      (Foundations.SequenceComposition.append_right (lt_congr (.eqRefl _) cs.wk.eqSymm Prf.hyp0)))
  have value := RationalArgmin.rationalEq_congr (Γ := Δ) eq.eqSymm (.eqRefl _) (.eqRefl _)
  simpa only [Δ,Syn.shift,QuadraticTowerCoefficients.subst_width,Foundations.SequenceComposition.subst_append,
    QuadraticTowerMultiplicationTable.subst_rightHalf,QuadraticTowerMultiplicationTable.rightHalf,Foundations.RealizerComposition.subst_slice] using value

theorem left_step_values (h B T D A C : PTm n)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C B) : Γ ⊢[PRAAx]
    equalValues h (leftHalf h (lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A C)) (firstComponent h B T D A C) := by
  have eq := (step_lookup_original h B T D A C ha hc).eqTrans (recipe_components _ _ _ _ _ _)
  have value := left_join_values (Γ := Γ) h (firstComponent h B T D A C) (secondComponent h B T D A C)
    (QuadraticTowerCoefficientArithmetic.added_length _ _ _)
  have proof := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (equalValues (var 0) (leftHalf (var 0) (var 1)) (var 2) : Fm PTm 3)
    ![h,append (firstComponent h B T D A C) (secondComponent h B T D A C),firstComponent h B T D A C]
    ![h,lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A C,firstComponent h B T D A C]
    (fun i => by fin_cases i; exact .eqRefl _; exact eq.eqSymm; exact .eqRefl _) (by simpa using value)
  simpa using proof

theorem right_step_values (h B T D A C : PTm n)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C B) : Γ ⊢[PRAAx]
    equalValues h (rightHalf h (lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A C)) (secondComponent h B T D A C) := by
  have eq := (step_lookup_original h B T D A C ha hc).eqTrans (recipe_components _ _ _ _ _ _)
  have value := right_join_values (Γ := Γ) h (firstComponent h B T D A C) (secondComponent h B T D A C)
    (QuadraticTowerCoefficientArithmetic.added_length _ _ _) (QuadraticTowerCoefficientArithmetic.added_length _ _ _)
  have proof := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (equalValues (var 0) (rightHalf (var 0) (var 1)) (var 2) : Fm PTm 3)
    ![h,append (firstComponent h B T D A C) (secondComponent h B T D A C),secondComponent h B T D A C]
    ![h,lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A C,secondComponent h B T D A C]
    (fun i => by fin_cases i; exact .eqRefl _; exact eq.eqSymm; exact .eqRefl _) (by simpa using value)
  simpa using proof

theorem normalized_append (h A C : PTm n) (ha : Γ ⊢[PRAAx] length A ≐ width h)
    (hc : Γ ⊢[PRAAx] length C ≐ width h) (a : Γ ⊢[PRAAx] normalized h A ≐ A)
    (c : Γ ⊢[PRAAx] normalized h C ≐ C) : Γ ⊢[PRAAx] normalized (succ h) (append A C) ≐ append A C :=
  (QuadraticTowerMultiplicationUnit.normalized_join h (append A C)).eqSymm.eqTrans
    (QuadraticTowerCoefficients.append_congr
      ((QuadraticTowerArrayNormalization.normalized_proper h _ A (left_join_values h A C ha)).eqTrans a)
      ((QuadraticTowerArrayNormalization.normalized_proper h _ C (right_join_values h A C ha hc)).eqTrans c))

theorem normalized_recipe (h B T D A C : PTm n) : Γ ⊢[PRAAx]
    normalized (succ h) (recipe h B T D A C) ≐ recipe h B T D A C :=
  normalized_append h _ _ (QuadraticTowerCoefficientArithmetic.added_length _ _ _)
    (QuadraticTowerCoefficientArithmetic.added_length _ _ _)
    (QuadraticTowerArrayNormalization.normalized_added _ _ _) (QuadraticTowerArrayNormalization.normalized_added _ _ _)

theorem normalized_singleton (q : PTm n) (hq : Γ ⊢[PRAAx] RationalNormalForm.wellFormed q) : Γ ⊢[PRAAx]
    normalized zero (singleton q) ≐ singleton q :=
  (QuadraticTowerMultiplicationUnit.normalized_base _).eqTrans
    (QuadraticTowerOperandProperness.singleton_congr
      ((QuadraticTowerArrayNormalization.recode_congr (QuadraticTowerCoefficients.singleton_entry q)).eqTrans
        (RationalNormalForm.normalize_fixed_point q hq)))

def outputFixed (h B D A C : PTm n) : Fm PTm n := normalized h (query h B D A C) ≐ query h B D A C
@[simp] theorem subst_outputFixed {k : ℕ} (σ : Fin n → PTm k) (h B D A C : PTm n) :
    (outputFixed h B D A C).subst σ = outputFixed (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [outputFixed]
theorem fixed_depth_congr {h k : PTm n} (B D A C : PTm n) (e : Γ ⊢[PRAAx] h ≐ k)
    (p : Γ ⊢[PRAAx] outputFixed h B D A C) : Γ ⊢[PRAAx] outputFixed k B D A C := by
  have proof := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (outputFixed (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5)
    ![h,B,D,A,C] ![k,B,D,A,C]
      (fun i => by fin_cases i; exact e; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _) (by simpa using p)
  simpa using proof

theorem normalized_query_zero (B D A C : PTm n)
    (ha : Γ ⊢[PRAAx] arrayHeight zero A B) (hc : Γ ⊢[PRAAx] arrayHeight zero C B) : Γ ⊢[PRAAx] outputFixed zero B D A C := by
  have original := QuadraticTowerOperandProperness.query_zero_original B D A C ha hc
  exact (QuadraticTowerAdditionLaws.normalized_congr zero original).eqTrans
    ((normalized_singleton _ (RationalArithmetic.multiply_guard _ _)).eqTrans original.eqSymm)

theorem normalized_query_succ (h B D A C : PTm n)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C B) : Γ ⊢[PRAAx] outputFixed (succ h) B D A C := by
  have original := query_succ_original h B D A C ha hc
  exact (QuadraticTowerAdditionLaws.normalized_congr (succ h) original).eqTrans
    ((normalized_recipe _ _ _ _ _ _).eqTrans original.eqSymm)

theorem normalized_query (h B D A C : PTm n)
    (ha : Γ ⊢[PRAAx] arrayHeight h A B) (hc : Γ ⊢[PRAAx] arrayHeight h C B) : Γ ⊢[PRAAx]
    normalized h (query h B D A C) ≐ query h B D A C := by
  refine .orE (zero_or_succ h) ?_ ?_
  · have a : (h ≐ zero) :: Γ ⊢[PRAAx] arrayHeight zero A B :=
      QuadraticTowerMultiplicationHeight.array_congr Prf.hyp0 (.eqRefl A) (.eqRefl B) ha.wk
    have c : (h ≐ zero) :: Γ ⊢[PRAAx] arrayHeight zero C B :=
      QuadraticTowerMultiplicationHeight.array_congr Prf.hyp0 (.eqRefl C) (.eqRefl B) hc.wk
    exact fixed_depth_congr B D A C Prf.hyp0.eqSymm (normalized_query_zero B D A C a c)
  · have a : (h ≐ succ (LeanProofs.IPRA.PTm.pred h)) :: Γ ⊢[PRAAx] arrayHeight (succ (LeanProofs.IPRA.PTm.pred h)) A B :=
      QuadraticTowerMultiplicationHeight.array_congr Prf.hyp0 (.eqRefl A) (.eqRefl B) ha.wk
    have c : (h ≐ succ (LeanProofs.IPRA.PTm.pred h)) :: Γ ⊢[PRAAx] arrayHeight (succ (LeanProofs.IPRA.PTm.pred h)) C B :=
      QuadraticTowerMultiplicationHeight.array_congr Prf.hyp0 (.eqRefl C) (.eqRefl B) hc.wk
    exact fixed_depth_congr B D A C Prf.hyp0.eqSymm (normalized_query_succ _ B D A C a c)

theorem normalized_returned_query (h B D A C : PTm n)
    (ha : Γ ⊢[PRAAx] arrayHeight h A B) (hc : Γ ⊢[PRAAx] arrayHeight h C B) : Γ ⊢[PRAAx]
    normalized h (PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,A,C]) ≐
      PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,A,C] :=
  (QuadraticTowerAdditionLaws.normalized_congr h (QuadraticTowerMultiplicationTable.query_program_at _ _ _ _ _)).eqTrans
    ((normalized_query h B D A C ha hc).eqTrans (QuadraticTowerMultiplicationTable.query_program_at _ _ _ _ _).eqSymm)

theorem actual_recipe_original_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (recipe (var 0) (var 1) (var 2) (var 3) (normalized (succ (var 0)) (var 4)) (normalized (succ (var 0)) (var 5)) ≐
      recipe (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (recipe_normalized _ _ _ _ _ _)
theorem original_height_query_successor_original_operands_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (arrayHeight (succ (var 0)) (var 3) (var 1) ⟶ arrayHeight (succ (var 0)) (var 4) (var 1) ⟶
      query (succ (var 0)) (var 1) (var 2) (var 3) (var 4) ≐ recipe (var 0) (var 1)
        (QuadraticTowerMultiplicationTable.table (var 0) (budget (var 0) (var 1) (var 2)) (var 2)) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (query_succ_original _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_heights_actual_step_components_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (arrayHeight (succ (var 0)) (var 4) (var 1) ⟶ arrayHeight (succ (var 0)) (var 5) (var 1) ⟶
      (equalValues (var 0) (leftHalf (var 0) (lookup (succ (var 0)) (var 1) (QuadraticTowerMultiplicationTable.step (var 0) (var 1) (var 2) (var 3)) (var 4) (var 5)))
        (firstComponent (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
       equalValues (var 0) (rightHalf (var 0) (lookup (succ (var 0)) (var 1) (QuadraticTowerMultiplicationTable.step (var 0) (var 1) (var 2) (var 3)) (var 4) (var 5)))
        (secondComponent (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) :=
  closeUniv 6 (.impI (.impI (.andI (left_step_values _ _ _ _ _ _ Prf.hyp1 Prf.hyp0) (right_step_values _ _ _ _ _ _ Prf.hyp1 Prf.hyp0))))
theorem actual_recipe_normalized_output_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (normalized (succ (var 0)) (recipe (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ recipe (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (normalized_recipe _ _ _ _ _ _)
theorem original_fixed_widths_normalized_append_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 1) ≐ width (var 0) ⟶ length (var 2) ≐ width (var 0) ⟶ normalized (var 0) (var 1) ≐ var 1 ⟶ normalized (var 0) (var 2) ≐ var 2 ⟶
      normalized (succ (var 0)) (append (var 1) (var 2)) ≐ append (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (normalized_append _ _ _ (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))
theorem original_heights_normalized_query_output_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (arrayHeight (var 0) (var 3) (var 1) ⟶ arrayHeight (var 0) (var 4) (var 1) ⟶
      normalized (var 0) (query (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ query (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (normalized_query _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_heights_actual_returned_query_normalized_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (arrayHeight (var 0) (var 3) (var 1) ⟶ arrayHeight (var 0) (var 4) (var 1) ⟶
      normalized (var 0) (PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 2,var 3,var 4]) ≐
        PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 2,var 3,var 4]) :=
  closeUniv 5 (.impI (.impI (normalized_returned_query _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationRecurrence
