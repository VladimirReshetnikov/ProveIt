module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Model.InternalCodedSourceTrace
public import M6PA.Model.PAInternalTraceCompose
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
attribute [local irreducible] stepValue stepGraph traceGraph
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Join model-length traces, removing only the shared endpoint. -/
theorem trace_compose {n m cs ds a b c : V} (h : Trace n cs a b) (g : Trace m ds b c) :
    ∃ es, Trace (n+m) es a c := by
  rcases h with ⟨hl,h0,hn,hs⟩
  rcases g with ⟨gl,g0,gm,gs⟩
  obtain ⟨first,tail,rfl⟩ := exists_adjoin_of_len_succ gl
  simp only [nth_adjoin_zero] at g0
  subst first
  have tl : len tail=m := add_right_cancel (by simpa only [len_adjoin] using gl)
  have old {i : V} (hi : i<n+1) : (HFSAppend.append cs tail).[i]=cs.[i] :=
    HFSAppend.nth_append_left cs tail (by simpa only [hl] using hi)
  have new := append_overlap cs tail n b hl hn
  refine ⟨HFSAppend.append cs tail,?_,(old (by simp)).trans h0,(new m).trans gm,?_⟩
  · simp [hl,tl,add_assoc,add_comm,add_left_comm]
  · intro i hi
    by_cases hin : i<n
    · have hi0 : i<n+1 := lt_trans hin (by simp)
      have hi1 : i+1<n+1 := by simpa using hin
      simpa only [old hi0,old hi1] using hs i hin
    · obtain ⟨j,rfl⟩ := exists_add_of_le (le_of_not_gt hin)
      have hj : j<m := by simpa using hi
      simpa only [add_assoc,new] using gs j hj

lemma trace_one (a : V) : Trace 1 ?[a,stepValue a] a (stepValue a) := by
  simpa [Trace,lt_one_iff_eq_zero]

theorem trace_prepend {n cs b c : V} (a : V) (he : stepValue a=b) (h : Trace n cs b c) :
    ∃ ds, Trace (n+1) ds a c := by
  have ha := trace_one a
  rw [he] at ha
  simpa only [add_comm] using trace_compose ha h
end Models

def traceCompositionSentence : ArithmeticSentence :=
  “∀ n m cs ds a b c, !traceGraph n cs a b ∧ !traceGraph m ds b c →
    ∃ es, !traceGraph (n+m) es a c”

theorem pa_proves_trace_composition : theory ⊢ traceCompositionSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [traceCompositionSentence,models_iff]
  simp [trace_correct]
  intro n m cs ds a b c h g
  exact trace_compose h g
#print axioms trace_compose
#print axioms trace_prepend
#print axioms pa_proves_trace_composition
end M6.Arithmetic.PA.InternalTrace.CodedSource

