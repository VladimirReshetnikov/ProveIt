import DiophantineConsistency.PRAWitnessTransfer
import DiophantineConsistency.PRAWitnessArithmetic
import ZFCinPA.Instances
/-! Witness bound for the literal negative pi weakening disjunct of
Foundation’s `Derivation.blueprint`, with its syntactic identity checked. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessWeakeningRuleBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessTransfer
noncomputable def branch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ d < D, !wkRuleGraph D s d ∧
    ∀ c, !fstIdxDef c d → !bitSubsetDef c s ∧ d ∈ C”
noncomputable def actualWeakeningBranch (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.pi.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or wk _))))))) => wk
  | _ => ⊥
theorem actualWeakeningBranch_eq (T : SetTheory) [T.Δ₁] : actualWeakeningBranch T = branch := by
  rfl
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
  have := wb_neg_wkRuleGraph (M := M)
  have := wb_fstIdxDef (M := M)
  have := wb_neg_bitSubsetDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [branch]
  wb_auto
  refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e c h => ⟨c, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  simp [h'.1]
theorem wb_neg_actualWeakeningBranch (T : SetTheory) [T.Δ₁] : WB M (∼actualWeakeningBranch T) := by
  rw [actualWeakeningBranch_eq]
  exact wb_neg_branch
end DiophantineConsistency.PRAWitnessWeakeningRuleBranch
