import PA194ForwardAtomicCorrect
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ForwardTyped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open M6.PA.RelationalSource
open Ordinal (Term Formula)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem quote_neg {n : Nat} (p : Formula n) : (⌜∼p⌝ : V) = neg SourceL (⌜p⌝ : V) := by
  change ((Semiformula.typedQuote V (∼p)).val : V) = neg SourceL (Semiformula.typedQuote V p).val
  rw [Semiformula.typedQuote_neg]
  rfl

theorem quote_eq_rel {n : Nat} (ts : Fin 2 → SourceTerm n) :
    (⌜(.rel PA194PAeq.Rel.eq ts : SourceFormula n)⌝ : V) = ^rel (2 : V) 0 (?[⌜ts 0⌝,⌜ts 1⌝] : V) := by
  simp [Semiformula.quote_rel,SemitermVec.val]
  constructor
  · change ((0 : Nat) : V) = 0; simp
  · constructor <;> rfl

theorem quote_eq_nrel {n : Nat} (ts : Fin 2 → SourceTerm n) :
    (⌜(.nrel PA194PAeq.Rel.eq ts : SourceFormula n)⌝ : V) = ^nrel (2 : V) 0 (?[⌜ts 0⌝,⌜ts 1⌝] : V) := by
  simp [Semiformula.quote_nrel,SemitermVec.val]
  constructor
  · change ((0 : Nat) : V) = 0; simp
  · constructor <;> rfl

theorem allOutput_quote {m : Nat} (p : Formula (m+1)) :
    allOutput (⌜p⌝ : V) = ⌜∀⁰ sourceImply (Ordinal.domain (.bvar 0)) p⌝ := by
  have h0 : (^#(0 : V)) = (⌜(.bvar 0 : Term (m+1))⌝ : V) := by simp
  rw [allOutput,h0,domainCode_quote]
  change ^∀ (imp SourceL (⌜Ordinal.domain (.bvar 0 : Term (m+1))⌝ : V) ⌜p⌝) = _
  change ^∀ (neg SourceL (⌜Ordinal.domain (.bvar 0 : Term (m+1))⌝ : V) ^⋎ ⌜p⌝) = _
  change ^∀ (neg SourceL (⌜Ordinal.domain (.bvar 0 : Term (m+1))⌝ : V) ^⋎ ⌜p⌝) =
    ^∀ (⌜(∼Ordinal.domain (.bvar 0 : Term (m+1))) ⋎ p⌝ : V)
  rw [Semiformula.quote_or,quote_neg]

theorem exsOutput_quote {m : Nat} (p : Formula (m+1)) :
    exsOutput (⌜p⌝ : V) = ⌜∃⁰ (Ordinal.domain (.bvar 0) ⋏ p)⌝ := by
  have h0 : (^#(0 : V)) = (⌜(.bvar 0 : Term (m+1))⌝ : V) := by simp
  rw [exsOutput,h0,domainCode_quote]
  rfl
#print axioms quote_eq_rel
#print axioms quote_eq_nrel
#print axioms allOutput_quote
#print axioms exsOutput_quote
end generic
end PA194ForwardTyped
