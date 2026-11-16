module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalReturnCell
public import PA196.Arithmetic.Machine.PAInternalReturnCode
public import PA196.Arithmetic.Machine.PAInternalCarryCode
public import PA196.Arithmetic.Machine.PAInternalSegmentCompose
@[expose] public section

namespace PA196.Arithmetic.Machine.PA.InternalTrace.ReturnFile
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open CarryCode ScanBits
attribute [local irreducible] Step StepFormula.formula

def returnFormula : ArithmeticSemisentence 1 :=
  “xs. ∀ l t, ∃ r l' c, !ReturnCode.leftGraph l' xs l ∧ !rightGraph r xs t ∧ !costGraph c xs ∧
    ∃ qs ls rs, !phaseFormula c qs ls rs 40 l' t 40 l r”
def boundedFormula : ArithmeticSemisentence 1 := “n. ∀ xs < n, !returnFormula xs”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

lemma return_correct (xs : V) : (V ⊧/![xs] returnFormula) ↔
    ∀ l t : V, ∃ qs ls rs,
      Phase (cost xs) qs ls rs 40 (ReturnCode.leftFile xs l) t 40 l (rightFile xs t) := by
  simp [returnFormula,right_defined.df,ReturnCode.left_defined.df,cost_defined.df,phase_correct,numeral_eq_natCast]

lemma bounded_correct (n : V) : (V ⊧/![n] boundedFormula) ↔
    ∀ xs : V, xs<n → ∀ l t : V, ∃ qs ls rs,
      Phase (cost xs) qs ls rs 40 (ReturnCode.leftFile xs l) t 40 l (rightFile xs t) := by
  simp [boundedFormula,return_correct]

/-- Full PA induction on a bound for the HFS vector code. The tail code is
strictly smaller, permitting arbitrary model-valued vector length and entries. -/
theorem segment (xs l t : V) : ∃ qs ls rs,
    Phase (cost xs) qs ls rs 40 (ReturnCode.leftFile xs l) t 40 l (rightFile xs t) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ n : V, ∀ xs : V, xs<n → ∀ l t : V, ∃ qs ls rs,
      Phase (cost xs) qs ls rs 40 (ReturnCode.leftFile xs l) t 40 l (rightFile xs t) := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun n : V => ∀ xs : V, xs<n → ∀ l t : V, ∃ qs ls rs,
        Phase (cost xs) qs ls rs 40 (ReturnCode.leftFile xs l) t 40 l (rightFile xs t)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb boundedFormula,by trivial,?_⟩
      intro n
      simpa using (bounded_correct n).symm
    · simp
    · intro n ih xs hxs l t
      by_cases hsmall : xs<n
      · exact ih xs hsmall l t
      have he : xs=n := le_antisymm (lt_succ_iff_le.mp hxs) (le_of_not_gt hsmall)
      subst n
      rcases nil_or_adjoin xs with hz | ⟨p,tail,rfl⟩
      · subst xs
        simpa using phase_zero (40 : V) l t
      · obtain ⟨tq,tl,tr,ht⟩ := ih tail (lt_adjoin' p tail) (repeatBits p 1 (4*l+1)) t
        obtain ⟨cq,cl,cr,hc⟩ := ReturnCell.segment p l (rightFile tail t)
        have joined := phase_compose ht hc
        simpa only [cost_adjoin,right_adjoin,ReturnCode.left_adjoin,add_comm] using joined
  exact all (xs+1) xs (by simp) l t
end Models

def sentence : ArithmeticSentence := “∀ xs, !returnFormula xs”

theorem pa_proves_return_file : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [return_correct]
  exact segment

#print axioms segment
#print axioms pa_proves_return_file
end PA196.Arithmetic.Machine.PA.InternalTrace.ReturnFile

