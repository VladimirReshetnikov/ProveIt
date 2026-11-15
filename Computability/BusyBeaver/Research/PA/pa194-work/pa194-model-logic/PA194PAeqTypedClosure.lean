import PA194PAeqBindFormulaTyped
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def typedCloseOne (p : Proposition PA194PAeq.language) : Proposition PA194PAeq.language := ∀⁰ (Rew.fix ▹ p)
def typedCloseIter : Nat → Proposition PA194PAeq.language → Proposition PA194PAeq.language
  | 0,p => p
  | n+1,p => typedCloseOne (typedCloseIter n p)
theorem close_quote (n : Nat) (p : Proposition PA194PAeq.language) :
    close (n : V) (⌜p⌝ : V) = (⌜typedCloseIter n p⌝ : V) := by
  induction n with
  | zero => simp [typedCloseIter]
  | succ n ih =>
    rw [Nat.cast_succ,close_succ,ih]
    change ^∀ (bindFormula (0 : V) (⌜typedCloseIter n p⌝ : V)) = _
    have hfix := bindFormula_quote_fix (V := V) (n := 0) (typedCloseIter n p)
    simp only [Nat.cast_zero] at hfix
    rw [hfix]
    rfl
theorem typedCloseIter_eq_fixitr (n : Nat) (p : Proposition PA194PAeq.language) :
    typedCloseIter n p = (∀⁰* (Rew.fixitr 0 n ▹ p)) := by
  induction n with
  | zero => simp [typedCloseIter]
  | succ n ih =>
    rw [LawfulSyntacticRewriting.allClosure_fixitr]
    simpa [typedCloseIter,typedCloseOne,ih]
theorem close_quote_univCl (p : Proposition PA194PAeq.language) :
    close (p.fvSup : V) (⌜p⌝ : V) = (⌜p.univCl⌝ : V) := by
  rw [close_quote,typedCloseIter_eq_fixitr]
  exact (quote_univCl (V := V) p).symm
#print axioms close_quote
#print axioms close_quote_univCl
end generic
end PA194PAeqBind
