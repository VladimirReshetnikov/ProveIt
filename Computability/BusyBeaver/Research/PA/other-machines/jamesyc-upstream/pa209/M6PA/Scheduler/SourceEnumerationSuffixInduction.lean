module
public import M6PA.Scheduler.SourceEnumerationCandidateBound
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open M6.PA.SourceCommandEncodingInternal
open M6.PA.ActualCandidateBlueprint M6.PA.ActualWordEncodingBlueprint
open M6.PA.SourceCantorInternal M6.PA.ActualCommandStepGraph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def sourceFromFormula : ArithmeticSemisentence 1 :=
  “i. ∀ base c initial, !commandRelationGraph c base 0 initial →
    ∃ k cs d result, !fromGraph result i base initial ∧ !traceGraph k cs c d ∧
      !commandRelationGraph d (base+i) 0 result”
theorem sourceFrom_correct (i : V) : (V ⊧/![i] sourceFromFormula) ↔
    ∀ base c initial : V, CommandRelation c base 0 initial →
      ∃ k cs d, Trace k cs c d ∧ CommandRelation d (base+i) 0 (fromValue base i initial) := by
  simp [sourceFromFormula,commandRelation_correct,from_graph,trace_correct]

/-- Genuine full PA induction over model-length suffix enumeration. -/
theorem source_from (i base c initial : V) (h : CommandRelation c base 0 initial) :
    ∃ k cs d, Trace k cs c d ∧ CommandRelation d (base+i) 0 (fromValue base i initial) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ i : V, ∀ base c initial : V, CommandRelation c base 0 initial →
      ∃ k cs d, Trace k cs c d ∧ CommandRelation d (base+i) 0 (fromValue base i initial) := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun i : V => ∀ base c initial : V, CommandRelation c base 0 initial →
        ∃ k cs d, Trace k cs c d ∧ CommandRelation d (base+i) 0 (fromValue base i initial)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb sourceFromFormula,by trivial,?_⟩
      intro i; simpa using (sourceFrom_correct i).symm
    · intro base c initial h
      exact ⟨0,?[c],c,trace_zero c,by simpa only [from_zero,add_zero] using h⟩
    · intro i ih base c initial h
      obtain ⟨k,cs,d,ht,hd⟩ := ih base c initial h
      obtain ⟨m,ds,e,hu,he⟩ := source_candidate d (base+i) (fromValue base i initial) hd
      obtain ⟨es,hv⟩ := trace_compose ht hu
      exact ⟨k+m,es,e,hv,by simpa only [from_succ,add_assoc] using he⟩
  exact all i base c initial h

end M6.Arithmetic.PA.InternalTrace.CodedSource
