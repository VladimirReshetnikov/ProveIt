module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalReturnCode
@[expose] public section

namespace PA196.Arithmetic.Machine.PA.InternalTrace.CarryReturn
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits

def relationFormula : ArithmeticSemisentence 1 :=
  “xs. ∀ l, ∃ a b, !CarryCode.leftGraph a xs l ∧
    !ReturnCode.leftGraph b xs ((1+1)*l+1) ∧ b=(1+1)*a+1”
def boundedFormula : ArithmeticSemisentence 1 := “n. ∀ xs<n, !relationFormula xs”
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma relation_correct (xs : V) : (V ⊧/![xs] relationFormula) ↔
    ∀ l : V, ReturnCode.leftFile xs ((1+1)*l+1)=(1+1)*CarryCode.leftFile xs l+1 := by
  simp [relationFormula,CarryCode.left_defined.df,ReturnCode.left_defined.df]
lemma bounded_correct (n : V) : (V ⊧/![n] boundedFormula) ↔
    ∀ xs : V, xs<n → ∀ l : V,
      ReturnCode.leftFile xs ((1+1)*l+1)=(1+1)*CarryCode.leftFile xs l+1 := by
  simp [boundedFormula,relation_correct]

theorem relation (xs l : V) :
    ReturnCode.leftFile xs ((1+1)*l+1)=(1+1)*CarryCode.leftFile xs l+1 := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ n : V, ∀ xs : V, xs<n → ∀ l : V,
      ReturnCode.leftFile xs ((1+1)*l+1)=(1+1)*CarryCode.leftFile xs l+1 := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun n : V => ∀ xs : V, xs<n → ∀ l : V,
        ReturnCode.leftFile xs ((1+1)*l+1)=(1+1)*CarryCode.leftFile xs l+1) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb boundedFormula,by trivial,?_⟩
      intro n
      simpa using (bounded_correct n).symm
    · simp
    · intro n ih xs hxs l
      by_cases hsmall : xs<n
      · exact ih xs hsmall l
      have he : xs=n := le_antisymm (lt_succ_iff_le.mp hxs) (le_of_not_gt hsmall)
      subst n
      rcases nil_or_adjoin xs with hz | ⟨p,tail,rfl⟩
      · subst xs
        simp
      · have hc : repeatBits p 1 (4*((1+1)*l+1)+1)=
            (1+1)*repeatBits p 1 (4*l+2)+1 := by
          rw [show 4*((1+1)*l+1)+1=(1+1)*(4*l+2)+1 by ring1,repeat_commute]
        rw [CarryCode.left_adjoin,ReturnCode.left_adjoin,hc]
        exact ih tail (lt_adjoin' p tail) (repeatBits p 1 (4*l+2))
  exact all (xs+1) xs (by simp) l
end Models

def sentence : ArithmeticSentence := “∀ xs, !relationFormula xs”
theorem pa_proves_relation : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [relation_correct]
  exact relation
#print axioms relation
#print axioms pa_proves_relation
end PA196.Arithmetic.Machine.PA.InternalTrace.CarryReturn

