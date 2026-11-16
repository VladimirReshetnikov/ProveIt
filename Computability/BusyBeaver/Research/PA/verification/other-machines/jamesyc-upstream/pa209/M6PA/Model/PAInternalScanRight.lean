module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalScanBits
@[expose] public section

namespace M6.Arithmetic.PA.InternalTrace.ScanRight
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits
attribute [local irreducible] Step StepFormula.formula

/-- An actual first-order formula, including the binary-word recursion graph. -/
def scanFormula (q : WorkingState) (read write : Bool) : ArithmeticSemisentence 1 :=
  “n. ∀ l t, ∃ r l', !repeatGraph r n ↑read.toNat t ∧
    !repeatGraph l' n ↑write.toNat l ∧
    ∃ qs ls rs, !segmentFormula n qs ls rs ↑q.val l r ↑q.val l' t”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

lemma scan_correct (q : WorkingState) (read write : Bool) (n : V) :
    (V ⊧/![n] (scanFormula q read write)) ↔
    ∀ l t : V, ∃ qs ls rs,
      Segment n qs ls rs q.val l (repeatBits n read.toNat t)
        q.val (repeatBits n write.toNat l) t := by
  simp [scanFormula,repeat_defined.df,segment_correct,numeral_eq_natCast]

/-- The induction variable ranges over the entire PA model. -/
theorem segment (q : WorkingState) (read write : Bool)
    (hr : row q read = ⟨write,true,some q⟩) (n l t : V) :
    ∃ qs ls rs, Segment n qs ls rs q.val l (repeatBits n read.toNat t)
      q.val (repeatBits n write.toNat l) t := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ n : V, ∀ l t : V, ∃ qs ls rs,
      Segment n qs ls rs q.val l (repeatBits n read.toNat t)
        q.val (repeatBits n write.toNat l) t := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun n : V => ∀ l t : V, ∃ qs ls rs,
        Segment n qs ls rs q.val l (repeatBits n read.toNat t)
          q.val (repeatBits n write.toNat l) t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb (scanFormula q read write),by trivial,?_⟩
      intro n
      simpa using (scan_correct q read write n).symm
    · intro l t
      exact ⟨_,_,_,by simpa using segment_zero (q.val : V) l t⟩
    · intro n ih l t
      obtain ⟨qs,ls,rs,h⟩ := ih ((1+1)*l+write.toNat) t
      have first := right_row q read (by rw [hr]) l (repeatBits n read.toNat t)
      rw [hr] at first
      simp only [StepFormula.controlCode] at first
      have joined := segment_prepend first h
      refine ⟨(q.val : V) ∷ qs, l ∷ ls, ((1+1)*repeatBits n read.toNat t+read.toNat) ∷ rs,?_⟩
      simpa only [repeat_succ,repeat_commute] using joined
  exact all n l t
end Models

def sentence (q : WorkingState) (read write : Bool) : ArithmeticSentence :=
  “∀ n, !(scanFormula q read write) n”

theorem pa_proves_scan (q : WorkingState) (read write : Bool)
    (hr : row q read = ⟨write,true,some q⟩) : theory ⊢ sentence q read write := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [scan_correct]
  exact segment q read write hr

end M6.Arithmetic.PA.InternalTrace.ScanRight

namespace M6.Arithmetic.PA.InternalTrace.ScanRight
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

/-- The exact dense1/read1 row used by the native carry engine. -/
theorem dense1_row : row (⟨1,by decide⟩ : WorkingState) true =
    ⟨true,true,some ⟨1,by decide⟩⟩ := by rfl

theorem pa_proves_dense1_scan :
    theory ⊢ sentence (⟨1,by decide⟩ : WorkingState) true true :=
  pa_proves_scan _ _ _ dense1_row

#print axioms segment
#print axioms pa_proves_scan
#print axioms pa_proves_dense1_scan
end M6.Arithmetic.PA.InternalTrace.ScanRight

