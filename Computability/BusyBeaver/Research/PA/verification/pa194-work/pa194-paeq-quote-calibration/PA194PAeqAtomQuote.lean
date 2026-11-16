import PA194PAeqTermQuote
import PA194PAeqFormulaValidity
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem equality_quote {n : Nat} (s t : SyntacticSemiterm PA194PAeq.language n) :
    equalityCode (⌜s⌝ : V) ⌜t⌝=⌜PA194PAeq.eq s t⌝ := by
  simp [equalityCode,PA194PAeq.eq,SemitermVec.val]
  exact ⟨by rfl,rfl,rfl⟩
theorem less_quote {n : Nat} (s t : SyntacticSemiterm PA194PAeq.language n) :
    lessCode (⌜s⌝ : V) ⌜t⌝=⌜PA194PAeq.less s t⌝ := by
  change qqExs _ = qqExs (⌜PA194PAeq.eq (PA194PAeq.add (Rew.bShift s)
    (PA194PAeq.succ (.bvar 0))) (Rew.bShift t)⌝ : V)
  rw [←equality_quote,quote_paeq_add,PA194PAeq.quote_successor]
  simp [LO.FirstOrder.Semiterm.quote_def]

theorem atom_quote {n k : Nat} (param : V) (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Nat n) :
    atomCode param (k:V) ⌜r⌝ (SemitermVec.val (fun i => (⌜ts i⌝ : Bootstrapping.Semiterm V ℒₒᵣ n)))=
      ⌜PA194PAeq.atom r ts⌝ := by
  cases r with
  | eq =>
    have hr : (⌜Language.ORing.Rel.eq⌝ : V)=0 := rfl
    simp only [hr,atomCode,PA194PAeq.atom]
    rw [←equality_quote]
    simp [SemitermVec.val]
    change equalityCode (termCode (⌜ts 0⌝:V)) (termCode ⌜ts 1⌝)=_
    rw [termCode_quote,termCode_quote]
  | lt =>
    have hr : (⌜Language.ORing.Rel.lt⌝ : V)=1 := by change ((1:Nat):V)=1; simp
    simp only [hr,atomCode,Arithmetic.one_ne_zero,if_false,PA194PAeq.atom]
    rw [←less_quote]
    simp [SemitermVec.val]
    change lessCode (termCode (⌜ts 0⌝:V)) (termCode ⌜ts 1⌝)=_
    rw [termCode_quote,termCode_quote]


#print axioms equality_quote
#print axioms less_quote
#print axioms atom_quote
end PA194PAeqTermBlueprint
