import PA194PAeqMulAssocProof
import PA194PAeqQuoteProof
import PA194PAeqOrdinaryTheoryClass
import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulAssoc
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

theorem internal_mulAssoc_proof {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    Provable ordinaryPAeq (formulaCode 0 (⌜PeanoMinus.Axiom.mulAssoc⌝ : V)) := by
  exact ⟨_, PA194PAeqQuoteProof.translated_quote_proof (V := V)
    (σ := PeanoMinus.Axiom.mulAssoc) (τ := resultSentence) ordinaryPAeq source_formula theoryProof⟩
#print axioms internal_mulAssoc_proof
end PA194PAeq.MulAssoc
