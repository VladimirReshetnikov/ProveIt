import PA194PAeqFormulaQuote
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
namespace PA194PAeqQuoteProof
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable (U : Theory PA194PAeq.language) [U.Δ₁]

theorem translated_quote_proof {σ : ArithmeticSentence} {τ : Sentence PA194PAeq.language}
    (h : PA194PAeq.formula (Rewriting.emb σ : ArithmeticSemiformula ℕ 0) =
      (Rewriting.emb τ : Semiproposition PA194PAeq.language 0)) (d : U ⊢! τ) :
    Proof U (⌜d⌝ : V) (formulaCode 0 (⌜σ⌝ : V)) := by
  have hc : formulaCode (0:V) (⌜σ⌝ : V) = (⌜τ⌝ : V) := by
    calc
      _ = formulaCode 0 (⌜(Rewriting.emb σ : ArithmeticSemiformula ℕ 0)⌝ : V) :=
        congrArg (formulaCode (0:V)) (Sentence.quote_def σ)
      _ = (⌜PA194PAeq.formula (Rewriting.emb σ : ArithmeticSemiformula ℕ 0)⌝ : V) :=
        formulaCode_quote 0 _
      _ = (⌜(Rewriting.emb τ : Semiproposition PA194PAeq.language 0)⌝ : V) := by rw [h]
      _ = (⌜τ⌝ : V) := (Sentence.quote_def τ).symm
  rw [hc]
  exact proof_of_quote_proof d

#print axioms translated_quote_proof
end PA194PAeqQuoteProof
