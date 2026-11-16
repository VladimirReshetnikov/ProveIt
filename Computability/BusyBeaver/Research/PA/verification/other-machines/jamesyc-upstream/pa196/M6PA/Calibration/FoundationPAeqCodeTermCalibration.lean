module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeTermValidity
@[expose] public section

/-! Standard syntax calibration of the independently total numeric adapter.
This theorem does not replace the arbitrary-model recursion/arity results. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem quote_paeq_add {n : Nat} (s t : SyntacticSemiterm Presentation.language n) :
    (⌜Presentation.add s t⌝ : V)=qqFunc 2 2 (⌜s⌝∷(⌜t⌝∷0)) := by
  simp [Presentation.add,SemitermVec.val,quote_func_def]
  exact ⟨by rfl,rfl,rfl⟩
theorem quote_paeq_mul {n : Nat} (s t : SyntacticSemiterm Presentation.language n) :
    (⌜Presentation.mul s t⌝ : V)=qqFunc 2 3 (⌜s⌝∷(⌜t⌝∷0)) := by
  simp [Presentation.mul,SemitermVec.val,quote_func_def]
  exact ⟨by rfl,rfl,rfl⟩

theorem termCode_quote {n : Nat} (t : ArithmeticSemiterm Nat n) :
    termCode (⌜t⌝ : V)=⌜Presentation.term t⌝ := by
  induction t with
  | bvar i => simp [Presentation.term]
  | fvar i => simp [Presentation.term]
  | func f ts ih =>
    cases f with
    | zero =>
      have he : (⌜Semiterm.func Language.ORing.Func.zero ts⌝ : V)=qqFunc 0 0 0 := by
        simp [SemitermVec.val]; rfl
      rw [he,termCode_zero]
      exact Presentation.quote_zero.symm
    | one =>
      have he : (⌜Semiterm.func Language.ORing.Func.one ts⌝ : V)=qqFunc 0 1 0 := by
        simp [SemitermVec.val]
        change ((1:Nat):V)=1
        simp
      rw [he,termCode_one]
      simp only [Presentation.term,Presentation.quote_successor,Presentation.quote_zero,oneCode,zeroCode]
    | add =>
      have he : (⌜Semiterm.func Language.ORing.Func.add ts⌝ : V)=qqFunc 2 0 (⌜ts 0⌝∷(⌜ts 1⌝∷0)) := by
        simp [SemitermVec.val]
        exact ⟨by rfl,rfl,rfl⟩
      rw [he,termCode_add (by simp [FFL.FirstOrder.Semiterm.quote_def]) (by simp [FFL.FirstOrder.Semiterm.quote_def])]
      simp only [Presentation.term,quote_paeq_add,ih]
    | mul =>
      have he : (⌜Semiterm.func Language.ORing.Func.mul ts⌝ : V)=qqFunc 2 1 (⌜ts 0⌝∷(⌜ts 1⌝∷0)) := by
        simp [SemitermVec.val]
        refine ⟨?_,rfl,rfl⟩
        change ((1:Nat):V)=1
        simp
      rw [he,termCode_mul (by simp [FFL.FirstOrder.Semiterm.quote_def]) (by simp [FFL.FirstOrder.Semiterm.quote_def])]
      simp only [Presentation.term,quote_paeq_mul,ih]

#print axioms quote_paeq_add
#print axioms quote_paeq_mul
#print axioms termCode_quote
end M6.PA.FoundationPAeqCode

