import DiophantineConsistency.PRAWitnessNegExistential
import DiophantineConsistency.PRAWitnessFormulaFunctions
import DiophantineConsistency.PRAWitnessTransfer
/-! Positive cut derivation leaf. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessPositiveCutRule
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessTransfer PRAWitnessNegExistential PRAWitnessFormulaFunctions
noncomputable def branch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, ∃ d₁ < D, ∃ d₂ < D, !cutRuleGraph D s p d₁ d₂ ∧
    (∃ c, !fstIdxDef c d₁ ∧ !insertDef c p s ∧ d₁ ∈ C) ∧
    ∃ c, !fstIdxDef c d₂ ∧ ∃ np, !(negGraph ℒₛₑₜ) np p ∧ !insertDef c np s ∧ d₂ ∈ C”
noncomputable def actual (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.sigma.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or a _))))))))) => a
  | _ => ⊥
theorem actual_eq (T : SetTheory) [T.Δ₁] : actual T = branch := by rfl
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_branch : WB M branch := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_cutRuleGraph (M := M); have := wb_fstIdxDef (M := M)
  have := wb_insertDef (M := M); have := wb_bitDef (M := M); have := wb_negGraph (M := M)
  simp only [branch]
  wb_auto
  · refine wb_exs_poly _ (by simp) ‘#1’ (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
    have h' := h
    simp at h'
    simp [h'.1]
  · refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
    · have h' := h
      simp at h'
      simp [h'.1]
    · wb_auto
      refine wb_exs_neg (3 : Fin 7) _ (by simp) (by wb_auto) ?_
      intro V _ _ e y h
      have h' := h
      simp at h'
      simpa using h'.1

theorem wb_actual (T : SetTheory) [T.Δ₁] : WB M (actual T) := by
  rw [actual_eq]
  exact wb_branch
end DiophantineConsistency.PRAWitnessPositiveCutRule
