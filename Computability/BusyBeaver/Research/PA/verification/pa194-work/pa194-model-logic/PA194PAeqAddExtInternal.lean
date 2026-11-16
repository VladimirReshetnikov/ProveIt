import PA194PAeqAddExtNormalized
import PA194PAeqOrdinaryTheoryClass
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AddExtNormalized
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind PA194PAeqTermBlueprint
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
attribute [local irreducible] theoryProof

theorem internal_addExt_proof {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    Provable ordinaryPAeq (formulaCode 0 (⌜Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.add⌝ : V)) := by
  exact ⟨_, PA194PAeqQuoteProof.translated_quote_proof (V := V)
    (σ := Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.add) (τ := targetSentence)
    ordinaryPAeq source_formula theoryProof⟩
#print axioms internal_addExt_proof
end PA194PAeq.AddExtNormalized
