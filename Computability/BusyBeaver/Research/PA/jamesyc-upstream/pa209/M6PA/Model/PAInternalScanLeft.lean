module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalScanBits
@[expose] public section

namespace M6.Arithmetic.PA.InternalTrace.ScanLeft
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits
attribute [local irreducible] Step StepFormula.formula

/-- The explicit current head bit is retained. This is a NatTape configuration,
not an implicit conversion of the native zipper's left-headed `zl` convention. -/
def scanFormula (q : WorkingState) (read write : Bool) : ArithmeticSemisentence 1 :=
  “n. ∀ l t, ∃ l' t', !repeatGraph l' n ↑read.toNat l ∧
    !repeatGraph t' n ↑write.toNat t ∧
    ∃ qs ls rs, !segmentFormula n qs ls rs ↑q.val l' ((1+1)*t+↑read.toNat)
      ↑q.val l ((1+1)*t'+↑read.toNat)”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma scan_correct (q : WorkingState) (read write : Bool) (n : V) :
    (V ⊧/![n] (scanFormula q read write)) ↔
    ∀ l t : V, ∃ qs ls rs,
      Segment n qs ls rs q.val (repeatBits n read.toNat l) ((1+1)*t+read.toNat)
        q.val l ((1+1)*repeatBits n write.toNat t+read.toNat) := by
  simp [scanFormula,repeat_defined.df,segment_correct,numeral_eq_natCast]

theorem segment (q : WorkingState) (read write : Bool)
    (hr : row q read = ⟨write,false,some q⟩) (n l t : V) :
    ∃ qs ls rs,
      Segment n qs ls rs q.val (repeatBits n read.toNat l) ((1+1)*t+read.toNat)
        q.val l ((1+1)*repeatBits n write.toNat t+read.toNat) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ n : V, ∀ l t : V, ∃ qs ls rs,
      Segment n qs ls rs q.val (repeatBits n read.toNat l) ((1+1)*t+read.toNat)
        q.val l ((1+1)*repeatBits n write.toNat t+read.toNat) := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun n : V => ∀ l t : V, ∃ qs ls rs,
        Segment n qs ls rs q.val (repeatBits n read.toNat l) ((1+1)*t+read.toNat)
          q.val l ((1+1)*repeatBits n write.toNat t+read.toNat)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb (scanFormula q read write),by trivial,?_⟩
      intro n
      simpa using (scan_correct q read write n).symm
    · intro l t
      exact ⟨_,_,_,by simpa using segment_zero (q.val : V) l ((1+1)*t+read.toNat)⟩
    · intro n ih l t
      obtain ⟨qs,ls,rs,h⟩ := ih l ((1+1)*t+write.toNat)
      have first := left_row q read read (by rw [hr]) (repeatBits n read.toNat l) t
      rw [hr] at first
      simp only [StepFormula.controlCode] at first
      have joined := segment_prepend first h
      refine ⟨(q.val : V) ∷ qs, ((1+1)*repeatBits n read.toNat l+read.toNat) ∷ ls,
        ((1+1)*t+read.toNat) ∷ rs,?_⟩
      simpa only [repeat_succ,repeat_commute] using joined
  exact all n l t
end Models

def sentence (q : WorkingState) (read write : Bool) : ArithmeticSentence :=
  “∀ n, !(scanFormula q read write) n”
theorem pa_proves_scan (q : WorkingState) (read write : Bool)
    (hr : row q read = ⟨write,false,some q⟩) : theory ⊢ sentence q read write := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [scan_correct]
  exact segment q read write hr

theorem dense94_row : row (⟨94,by decide⟩ : WorkingState) true =
    ⟨true,false,some ⟨94,by decide⟩⟩ := by rfl
theorem dense54_row : row (⟨54,by decide⟩ : WorkingState) true =
    ⟨true,false,some ⟨54,by decide⟩⟩ := by rfl

theorem pa_proves_dense94_scan : theory ⊢ sentence (⟨94,by decide⟩ : WorkingState) true true :=
  pa_proves_scan _ _ _ dense94_row
theorem pa_proves_dense54_scan : theory ⊢ sentence (⟨54,by decide⟩ : WorkingState) true true :=
  pa_proves_scan _ _ _ dense54_row

#print axioms segment
#print axioms pa_proves_scan
#print axioms pa_proves_dense94_scan
#print axioms pa_proves_dense54_scan
end M6.Arithmetic.PA.InternalTrace.ScanLeft

