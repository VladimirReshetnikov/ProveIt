import DiophantineConsistency.PRAWitnessPositiveAxiomRule
import DiophantineConsistency.PRAWitnessAxiomRuleBranch
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-! Arithmetic-language axiom-rule witness bounds. These establish only one
rule branch and explicitly assume bounds for the PA axiom recognizer. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PAAxiomBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.PRAWitnessCalculus DiophantineConsistency.PRAWitnessArithmetic
open DiophantineConsistency.PRAWitnessTransfer

noncomputable def positiveBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, !axmGraph D s p ∧ p ∈ s ∧ !(((𝗣𝗔 : ArithmeticTheory).Δ₁ch).sigma) p”
noncomputable def negativeBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, !axmGraph D s p ∧ p ∈ s ∧ !(((𝗣𝗔 : ArithmeticTheory).Δ₁ch).pi) p”

noncomputable def actualPositive : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ ax))))))))) => ax
  | _ => ⊥
noncomputable def actualNegative : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ ax))))))))) => ax
  | _ => ⊥
theorem actualPositive_eq : actualPositive = positiveBranch := by rfl
theorem actualNegative_eq : actualNegative = negativeBranch := by rfl

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_positiveBranch (h : WB M ((𝗣𝗔 : ArithmeticTheory).Δ₁ch).sigma.val) :
    WB M actualPositive := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := DiophantineConsistency.PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rw [actualPositive_eq]
  have := wb_axmGraph (M := M); have := wb_bitDef (M := M); have := h
  simp only [positiveBranch]
  wb_auto

theorem wb_negativeBranch (h : WB M (∼((𝗣𝗔 : ArithmeticTheory).Δ₁ch).pi.val)) :
    WB M (∼actualNegative) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := DiophantineConsistency.PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rw [actualNegative_eq]
  have := wb_neg_axmGraph (M := M); have := wb_neg_bitDef (M := M); have := h
  simp only [negativeBranch]
  wb_auto

#print axioms wb_positiveBranch
#print axioms wb_negativeBranch
end PA196PAAxiomBound
