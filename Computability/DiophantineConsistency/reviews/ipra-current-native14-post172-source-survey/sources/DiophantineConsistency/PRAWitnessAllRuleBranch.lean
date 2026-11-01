import DiophantineConsistency.PRAWitnessSubsts
import DiophantineConsistency.PRAWitnessFreeExistential
import DiophantineConsistency.PRAWitnessSetShiftExistential
/-! Witness bound for the literal negative pi universal-introduction
disjunct of Foundation’s derivation core. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessAllRuleBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessFormulaFunctions PRAWitnessTransfer PRAWitnessSubsts PRAWitnessFreeExistential PRAWitnessSetShiftExistential
noncomputable def branch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, ∃ dp < D,
    !allIntroGraph D s p dp ∧ (∀ all, !qqAllDef all p → all ∈ s) ∧
    ∀ c, !fstIdxDef c dp → ∀ fp, !(freeGraph ℒₛₑₜ) fp p → ∀ ss, !(setShiftGraph ℒₛₑₜ) ss s →
      !insertDef c fp ss ∧ dp ∈ C”
noncomputable def actualAllBranch (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.pi.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or a _))))) => a
  | _ => ⊥
theorem actualAllBranch_eq (T : SetTheory) [T.Δ₁] : actualAllBranch T = branch := by rfl
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_neg_branch : WB M (∼branch) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_neg_allIntroGraph (M := M)
  have := wb_qqAllDef (M := M)
  have := wb_fstIdxDef (M := M)
  have := wb_freeGraph (M := M)
  have := PRAWitnessSetShiftCandidate.wb_setShiftGraph (M := M)
  have := wb_neg_insertDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [branch]
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
      refine wb_exs_free (2 : Fin 6) _ (by simp) ?_ ?_
      · wb_auto
        refine wb_exs_setShift (4 : Fin 7) _ (by simp) (by wb_auto) ?_
        intro V _ _ e y h
        have h' := h
        simp at h' ⊢
        exact h'.1
      · intro V _ _ e y h
        have h' := h
        simp at h' ⊢
        exact h'.1
theorem wb_neg_actualAllBranch (T : SetTheory) [T.Δ₁] : WB M (∼actualAllBranch T) := by
  rw [actualAllBranch_eq]
  exact wb_neg_branch
end DiophantineConsistency.PRAWitnessAllRuleBranch
