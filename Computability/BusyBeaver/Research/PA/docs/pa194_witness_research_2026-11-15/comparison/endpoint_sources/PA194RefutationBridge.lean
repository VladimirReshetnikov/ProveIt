import DiophantineConsistency.IPRAPA196Consistency
import DiophantineConsistency.PRAWitnessTransfer

/-! In every model whose arithmetic reduct satisfies IΣ₁, the mapped
Foundation PA refutation formula has exactly the proof-code witness used by
Foundation’s internal syntax. The witness can be nonstandard. This is a
semantic binding only: it does not relate the proof code to the PA194 checker,
and its IΣ₁ assumption is stronger than the candidate PRA model assumptions. -/
set_option autoImplicit false
noncomputable section
namespace PA194RefutationBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRAPA196Consistency

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem mapped_refutation_iff :
    Semiformula.Eval (s := (inferInstance : Structure language M)) ![] Empty.elim mappedPARefutation ↔
      ∃ d : M, Proof (𝗣𝗔 : ArithmeticTheory) d (⌜(⊥ : ArithmeticSentence)⌝ : M) := by
  rw [mappedPARefutation, DiophantineConsistency.PRAWitnessTransfer.eval_lMap_std]
  simp [paRefutation, provabilityPred, Provable]

#print axioms mapped_refutation_iff
end PA194RefutationBridge
