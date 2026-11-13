module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLiftLanguage
public import M6PA.Calibration.RelationalPredicateTemplateFormulaValidity
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

def IdentityBound (s : Nat) (b : V) : Prop :=
  ∀i : Fin s,nth b (i:Nat)=qqBvar ((i:Nat):V)

theorem identityBound_bind {s : Nat} {b : V} (hb : IsSemitermVec L (s:V) (s:V) b)
    (hi : IdentityBound s b) : IdentityBound (s+1) (bindBound b) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [bindBound]
  · have hj : (j:V)<(s:V) := by exact_mod_cast j.isLt
    simp only [bindBound,Fin.val_succ,Nat.cast_add,Nat.cast_one,nth_adjoin_succ]
    rw [NumericPAeqTerm.shiftTerms_nth hb hj,hi j]
    simp

theorem closed_termValue_lift {s : Nat} (t : Semiterm L Nat s) {b f : V}
    (hb : IdentityBound s b) (hc : ∀i,¬t.FVar? i) :
    termValue (liftTerm t) b f=(⌜t⌝ : V) := by
  cases t with
  | bvar i => simpa [liftTerm,Semiterm.lMap,termValue] using hb i
  | fvar i => exact (hc i (by simp)).elim
  | func fn _ => nomatch fn

#print axioms identityBound_bind
#print axioms closed_termValue_lift
end M6.PA.RelationalPredicateTemplate
