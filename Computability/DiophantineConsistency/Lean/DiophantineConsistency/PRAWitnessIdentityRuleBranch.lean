import DiophantineConsistency.PRAWitnessNegExistential
/-! Witness bound for the literal negative pi identity disjunct of
Foundation’s `Derivation.blueprint`, with its syntactic identity checked. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessIdentityRuleBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessNegExistential PRAWitnessFormulaFunctions
noncomputable def branch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, !axLGraph D s p ∧ p ∈ s ∧
    ∀ np, !(negGraph ℒₛₑₜ) np p → np ∈ s”
noncomputable def actualIdentityBranch (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.pi.val with
  | .and _ (.or ax _) => ax
  | _ => ⊥
theorem actualIdentityBranch_eq (T : SetTheory) [T.Δ₁] : actualIdentityBranch T = branch := by
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
  have := wb_neg_axLGraph (M := M)
  have := wb_neg_bitDef (M := M)
  have := wb_negGraph (M := M)
  simp only [branch]
  wb_auto
  refine wb_exs_neg (0 : Fin 4) _ (by simp) (by wb_auto) ?_
  intro V _ _ e y h
  have h' := h
  simp at h' ⊢
  exact h'.1
theorem wb_neg_actualIdentityBranch (T : SetTheory) [T.Δ₁] : WB M (∼actualIdentityBranch T) := by
  rw [actualIdentityBranch_eq]
  exact wb_neg_branch
end DiophantineConsistency.PRAWitnessIdentityRuleBranch
