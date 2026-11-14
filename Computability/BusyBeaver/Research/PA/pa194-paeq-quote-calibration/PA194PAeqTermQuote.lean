import PA194PAeqTermValidity
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-! Standard syntax calibration of the independently total numeric adapter.
This theorem does not replace the arbitrary-model recursion/arity results. -/
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem quote_paeq_add {n : Nat} (s t : SyntacticSemiterm PA194PAeq.language n) :
    (⌜PA194PAeq.add s t⌝ : V)=qqFunc 2 2 (⌜s⌝∷(⌜t⌝∷0)) := by
  simp [PA194PAeq.add,SemitermVec.val]
  exact ⟨by rfl,rfl,rfl⟩
theorem quote_paeq_mul {n : Nat} (s t : SyntacticSemiterm PA194PAeq.language n) :
    (⌜PA194PAeq.mul s t⌝ : V)=qqFunc 2 3 (⌜s⌝∷(⌜t⌝∷0)) := by
  simp [PA194PAeq.mul,SemitermVec.val]
  exact ⟨by rfl,rfl,rfl⟩

theorem termCode_quote {n : Nat} (t : ArithmeticSemiterm Nat n) :
    termCode (⌜t⌝ : V)=⌜PA194PAeq.term t⌝ := by
  induction t with
  | bvar i => simp [PA194PAeq.term]
  | fvar i => simp [PA194PAeq.term]
  | func f ts ih =>
    cases f with
    | zero =>
      have he : (⌜Semiterm.func Language.ORing.Func.zero ts⌝ : V)=qqFunc 0 0 0 := by
        simp [SemitermVec.val]; rfl
      rw [he,termCode_zero]
      exact PA194PAeq.quote_zero.symm
    | one =>
      have he : (⌜Semiterm.func Language.ORing.Func.one ts⌝ : V)=qqFunc 0 1 0 := by
        simp [SemitermVec.val]
        change ((1:Nat):V)=1
        simp
      rw [he,termCode_one]
      simp only [PA194PAeq.term,PA194PAeq.quote_successor,PA194PAeq.quote_zero,oneCode,zeroCode]
    | add =>
      have he : (⌜Semiterm.func Language.ORing.Func.add ts⌝ : V)=qqFunc 2 0 (⌜ts 0⌝∷(⌜ts 1⌝∷0)) := by
        simp [SemitermVec.val]
        exact ⟨by rfl,rfl,rfl⟩
      rw [he,termCode_add (by simp [LO.FirstOrder.Semiterm.quote_def]) (by simp [LO.FirstOrder.Semiterm.quote_def])]
      simp only [PA194PAeq.term,quote_paeq_add,ih]
    | mul =>
      have he : (⌜Semiterm.func Language.ORing.Func.mul ts⌝ : V)=qqFunc 2 1 (⌜ts 0⌝∷(⌜ts 1⌝∷0)) := by
        simp [SemitermVec.val]
        refine ⟨?_,rfl,rfl⟩
        change ((1:Nat):V)=1
        simp
      rw [he,termCode_mul (by simp [LO.FirstOrder.Semiterm.quote_def]) (by simp [LO.FirstOrder.Semiterm.quote_def])]
      simp only [PA194PAeq.term,quote_paeq_mul,ih]

#print axioms quote_paeq_add
#print axioms quote_paeq_mul
#print axioms termCode_quote
end PA194PAeqTermBlueprint

