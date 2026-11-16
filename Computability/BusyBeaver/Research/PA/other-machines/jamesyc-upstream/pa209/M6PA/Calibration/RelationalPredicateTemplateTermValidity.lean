module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateTermGraph
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def EnvironmentsValid (s n b f : V) : Prop :=
  IsSemitermVec RelationalSource.language s n b ∧
  IsSemitermVec RelationalSource.language (len f) n f

theorem termValue_isSemiterm {s : Nat} {n b f : V} (t : Term s)
    (h : EnvironmentsValid (s:V) n b f)
    (hf : ∀i,t.FVar? i→(i:V)<len f) :
    IsSemiterm RelationalSource.language n (termValue t b f) := by
  cases t with
  | bvar i =>
    exact h.1.nth (by exact_mod_cast i.isLt)
  | fvar i => exact h.2.nth (hf i (by simp))
  | func fn _ => nomatch fn


#print axioms termValue_isSemiterm
end M6.PA.RelationalPredicateTemplate

