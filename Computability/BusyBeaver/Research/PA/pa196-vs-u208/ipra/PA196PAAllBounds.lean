import PA196PAFreeGraph
import PA196PAFreeExistential
import PA196PASetShiftExistential

/-! Both exact arithmetic all-introduction derivation-core branches. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace PA196PAAllBounds
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessTransfer PRAWitnessFormulaFunctions

noncomputable def positiveBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, ∃ d < D, !allIntroGraph D s p d ∧
    (∃ ap, !qqAllDef ap p ∧ ap ∈ s) ∧
    ∃ c, !fstIdxDef c d ∧ ∃ fp, !(freeGraph ℒₒᵣ) fp p ∧
      ∃ ss, !(setShiftGraph ℒₒᵣ) ss s ∧ !insertDef c fp ss ∧ d ∈ C”
noncomputable def actualPositive : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or a _))))) => a
  | _ => ⊥
theorem actualPositive_eq : actualPositive = positiveBranch := by rfl

noncomputable def negativeBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, ∃ dp < D,
    !allIntroGraph D s p dp ∧ (∀ all, !qqAllDef all p → all ∈ s) ∧
    ∀ c, !fstIdxDef c dp → ∀ fp, !(freeGraph ℒₒᵣ) fp p → ∀ ss, !(setShiftGraph ℒₒᵣ) ss s →
      !insertDef c fp ss ∧ dp ∈ C”
noncomputable def actualNegative : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or a _))))) => a
  | _ => ⊥
theorem actualNegative_eq : actualNegative = negativeBranch := by rfl

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_positiveBranch : WB M positiveBranch := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_allIntroGraph (M := M); have := wb_qqAllDef (M := M); have := wb_bitDef (M := M)
  have := wb_fstIdxDef (M := M); have := PA196PAFreeGraph.wb_freeGraph (M := M)
  have := PA196PASetShift.wb_setShiftGraph (M := M); have := wb_insertDef (M := M)
  simp only [positiveBranch]
  wb_auto
  · refine wb_exs_poly _ (by simp) ‘#2’ (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
    have h' := h
    simp at h'
    exact le_of_lt (lt_of_mem h'.2)
  · refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
    · have h' := h
      simp at h'
      simp [h'.1]
    · wb_auto
      refine PA196PAFreeExistential.wb_exs_free (2 : Fin 6) _ (by simp) ?_ ?_
      · wb_auto
        refine PA196PASetShiftExistential.wb_exs_setShift (4 : Fin 7) _ (by simp) (by wb_auto) ?_
        intro V _ _ e y h
        have h' := h
        simp at h'
        simpa using h'.1
      · intro V _ _ e y h
        have h' := h
        simp at h'
        simpa using h'.1


theorem wb_negativeBranch : WB M (∼negativeBranch) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_neg_allIntroGraph (M := M)
  have := wb_qqAllDef (M := M)
  have := wb_fstIdxDef (M := M)
  have := PA196PAFreeGraph.wb_freeGraph (M := M)
  have := PA196PASetShift.wb_setShiftGraph (M := M)
  have := wb_neg_insertDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [negativeBranch]
  wb_auto
  · refine wb_exs_poly _ (by simp) ‘(6+#1+1)*(6+#1+1)+1’
      (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
    have h' := h
    simp at h'
    rw [h'.1]
    simpa [qqAll, Semiterm.val_func, numeral_eq_natCast] using code2_le (6 : V) (e 1)
  · refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e c h => ⟨c, ?_, h⟩) ?_
    · have h' := h
      simp at h'
      simp [h'.1]
    · wb_auto
      refine PA196PAFreeExistential.wb_exs_free (2 : Fin 6) _ (by simp) ?_ ?_
      · wb_auto
        refine PA196PASetShiftExistential.wb_exs_setShift (4 : Fin 7) _ (by simp) (by wb_auto) ?_
        intro V _ _ e y h
        have h' := h
        simp at h' ⊢
        exact h'.1
      · intro V _ _ e y h
        have h' := h
        simp at h' ⊢
        exact h'.1

theorem wb_positiveAll : WB M actualPositive := by
  rw [actualPositive_eq]
  exact wb_positiveBranch

theorem wb_negativeAll : WB M (∼actualNegative) := by
  rw [actualNegative_eq]
  exact wb_negativeBranch

#print axioms actualPositive_eq
#print axioms actualNegative_eq
#print axioms wb_positiveAll
#print axioms wb_negativeAll
end PA196PAAllBounds
