import DiophantineConsistency.PRAWitnessFormulaFunctions
import DiophantineConsistency.PRAWitnessTransfer
/-! Positive axiom derivation leaf. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessPositiveAxiomRule
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessTransfer
noncomputable def branch (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, !axmGraph D s p ∧ p ∈ s ∧ !((T.Δ₁ch).sigma) p”
noncomputable def actual (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.sigma.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ ax))))))))) => ax
  | _ => ⊥
theorem actual_eq (T : SetTheory) [T.Δ₁] : actual T = branch T := by rfl
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_branch (T : SetTheory) [T.Δ₁] (hT : WB M (T.Δ₁ch).sigma.val) : WB M (branch T) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_axmGraph (M := M); have := wb_bitDef (M := M); have := hT
  simp only [branch]
  wb_auto

theorem wb_actual (T : SetTheory) [T.Δ₁] (hT : WB M (T.Δ₁ch).sigma.val) : WB M (actual T) := by
  rw [actual_eq]
  exact wb_branch T hT
end DiophantineConsistency.PRAWitnessPositiveAxiomRule
