module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCommandRelation
public import M6PA.Scheduler.SourceCommandIteration
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open SourceCommandEncodingInternal

def traversalRelationGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “c n p. ∃ l s, !nthDef l p 0 ∧ !nthDef s p 1 ∧ !commandRelationGraph c n l s”
noncomputable def commandIterationFormula : ArithmeticSemisentence 1 :=
  “i. ∀ c n p, !traversalRelationGraph c n p →
    ∃ k cs d q, !consumeGraph q i p ∧ !traceGraph k cs c d ∧ !traversalRelationGraph d n q”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
def TraversalRelation (c n p : V) : Prop := CommandRelation c n p.[0] p.[1]

theorem traversalRelation_correct (v : Fin 3 → V) :
    (V ⊧/v traversalRelationGraph.val) ↔ TraversalRelation (v 0) (v 1) (v 2) := by
  simp [traversalRelationGraph,TraversalRelation,nth_defined.df,commandRelation_correct]

theorem commandIteration_correct (i : V) :
    (V ⊧/![i] commandIterationFormula) ↔
      ∀ c n p : V, TraversalRelation c n p → ∃k cs d,Trace k cs c d ∧ TraversalRelation d n (consume i p) := by
  simp [commandIterationFormula,traversalRelation_correct,consume_defined.df,trace_correct]

/-- Generic model-count composition. The one-command literal refinement is an
explicit supplier; this theorem alone does not assert it or an endpoint. -/
theorem command_trace_iteration
    (single : ∀ c n p : V, TraversalRelation c n p →
      ∃k cs d,Trace k cs c d ∧ TraversalRelation d n (consumeStep p))
    (i c n p : V) (h : TraversalRelation c n p) :
    ∃k cs d,Trace k cs c d ∧ TraversalRelation d n (consume i p) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀i : V,∀c n p : V, TraversalRelation c n p →
      ∃k cs d,Trace k cs c d ∧ TraversalRelation d n (consume i p) := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun i : V=>∀c n p : V, TraversalRelation c n p →
        ∃k cs d,Trace k cs c d ∧ TraversalRelation d n (consume i p)) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb commandIterationFormula,by trivial,?_⟩
      intro i; simpa using (commandIteration_correct i).symm
    · intro c n p h
      exact ⟨0,?[c],c,trace_zero c,by simpa only [consume_zero] using h⟩
    · intro i ih c n p h
      obtain ⟨k,cs,d,ht,hd⟩ := ih c n p h
      obtain ⟨m,ds,e,hu,he⟩ := single d n (consume i p) hd
      obtain ⟨es,hv⟩ := trace_compose ht hu
      exact ⟨k+m,es,e,hv,by simpa only [consume_succ] using he⟩
  exact all i c n p h
#print axioms commandIteration_correct
#print axioms command_trace_iteration
end M6.Arithmetic.PA.InternalTrace.CodedSource

