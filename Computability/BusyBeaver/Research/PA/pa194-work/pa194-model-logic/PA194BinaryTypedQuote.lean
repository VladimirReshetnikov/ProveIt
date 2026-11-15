import PA194FormulaScope
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqOrdinalValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates
open M6.PA.RelationalSource
open Ordinal (Term Formula)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem binaryValue_quote {m : Nat} (p : Formula 3) (z : Term m)
    (left right : Formula (m+2)) :
    binaryValue p (⌜z⌝ : V) ⌜left⌝ ⌜right⌝ = ⌜Ordinal.domain z ⋏
      (∃⁰ ∃⁰ (left ⋏ (right ⋏ (p ⇜ ![.bvar 1,.bvar 0,Rew.bShift (Rew.bShift z)]))))⌝ := by
  have h0 : (^#(0:V)) = (⌜(.bvar 0 : Term (m+2))⌝ : V) := by simp
  have h1 : (^#(1:V)) = (⌜(.bvar 1 : Term (m+2))⌝ : V) := by simp
  have hs : termBShift SourceL (termBShift SourceL (⌜z⌝ : V)) = ⌜Rew.bShift (Rew.bShift z)⌝ := by
    simp [Semiterm.quote_def]
  rw [binaryValue,domainCode_quote,h0,h1,hs,templateThree_quote]
  rfl

theorem additionValue_quote {m : Nat} (z : Term m) (left right : Formula (m+2)) :
    binaryValue additionTemplate (⌜z⌝ : V) ⌜left⌝ ⌜right⌝ = ⌜Ordinal.domain z ⋏
      (∃⁰ ∃⁰ (left ⋏ (right ⋏ PairGraph.addResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z)))))⌝ := by
  rw [binaryValue_quote]
  congr 1
  change _ ⋏ (∃⁰ ∃⁰ (_ ⋏ (_ ⋏ _))) = _ ⋏ (∃⁰ ∃⁰ (_ ⋏ (_ ⋏ _)))
  rw [show (additionTemplate ⇜ ![.bvar 1,.bvar 0,Rew.bShift (Rew.bShift z)]) =
      PairGraph.addResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z)) from
    PairGraph.addResult_rew _ _ _ _]

theorem multiplicationValue_quote {m : Nat} (z : Term m) (left right : Formula (m+2)) :
    binaryValue multiplicationTemplate (⌜z⌝ : V) ⌜left⌝ ⌜right⌝ = ⌜Ordinal.domain z ⋏
      (∃⁰ ∃⁰ (left ⋏ (right ⋏ PairGraph.mulResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z)))))⌝ := by
  rw [binaryValue_quote]
  congr 1
  change _ ⋏ (∃⁰ ∃⁰ (_ ⋏ (_ ⋏ _))) = _ ⋏ (∃⁰ ∃⁰ (_ ⋏ (_ ⋏ _)))
  rw [show (multiplicationTemplate ⇜ ![.bvar 1,.bvar 0,Rew.bShift (Rew.bShift z)]) =
      PairGraph.mulResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z)) from
    PairGraph.mulResult_rew _ _ _ _]
#print axioms binaryValue_quote
#print axioms additionValue_quote
#print axioms multiplicationValue_quote
end generic
end PA194PAeqOrdinalValues
