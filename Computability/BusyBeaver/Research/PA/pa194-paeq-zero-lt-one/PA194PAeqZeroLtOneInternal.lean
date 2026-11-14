import PA194PAeqZeroLtOne
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 2000
set_option linter.unnecessarySeqFocus false
namespace PA194PAeq.ZeroLtOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeqTermBlueprint
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
attribute [local irreducible] zeroLtOneProof

theorem internal_zeroLtOne_proof {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    Provable targetFixedTheory
      (formulaCode 0 (⌜PeanoMinus.Axiom.zeroLtOne⌝ : V)) := by
  exact ⟨_, PA194PAeqQuoteProof.translated_quote_proof (V := V)
    (σ := PeanoMinus.Axiom.zeroLtOne)
    (τ := zeroLtOneSentence) targetFixedTheory zeroLtOne_formula zeroLtOneProof⟩


#print axioms internal_zeroLtOne_proof
end PA194PAeq.ZeroLtOne
