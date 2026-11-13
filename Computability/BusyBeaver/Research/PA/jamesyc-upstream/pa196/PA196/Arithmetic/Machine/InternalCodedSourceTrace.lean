module
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Machine.InternalCodedSourceStep
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 PA196.Arithmetic.Machine.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
attribute [local irreducible] stepValue stepGraph

/-- Model-length source trace, using exactly the coded literal step graph. -/
def traceGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “n cs a b. !lenDef (n+1) cs ∧ !nthDef a cs 0 ∧ !nthDef b cs n ∧
    ∀ i<n, ∃ x y, !nthDef x cs i ∧ !nthDef y cs (i+1) ∧ !stepGraph y x”
def allTraceFormula : ArithmeticSemisentence 1 :=
  “n. ∀ a, ∃ cs b, !traceGraph n cs a b”
def traceTotalSentence : ArithmeticSentence := “∀ n, !allTraceFormula n”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
def Trace (n cs a b : V) : Prop :=
  len cs=n+1 ∧ cs.[0]=a ∧ cs.[n]=b ∧
    ∀ i<n, cs.[i+1]=stepValue cs.[i]

lemma trace_correct (v : Fin 4 → V) : (V ⊧/v traceGraph.val) ↔
    Trace (v 0) (v 1) (v 2) (v 3) := by
  simp [traceGraph,Trace,len_defined.df,nth_defined.df,step_defined.df,eq_comm]

lemma trace_zero (a : V) : Trace 0 ?[a] a a := by simp [Trace]

lemma trace_extend {n cs a b : V} (h : Trace n cs a b) :
    Trace (n+1) (concat cs (stepValue b)) a (stepValue b) := by
  rcases h with ⟨hl,h0,hn,hs⟩
  have old {i : V} (hi : i<n+1) : (concat cs (stepValue b)).[i]=cs.[i] :=
    concat_nth_lt cs (stepValue b) (by simpa only [hl] using hi)
  have new := concat_nth_len' cs (stepValue b) hl
  refine ⟨by simp [hl],(old (by simp)).trans h0,new,?_⟩
  intro i hi
  rcases eq_or_lt_of_le (lt_succ_iff_le.mp hi) with rfl | hi'
  · simp only [old hi,new,hn]
  · have his : i+1<n+1 := by simpa using hi'
    simpa only [old hi,old his] using hs i hi'

lemma allTrace_correct (n : V) : (V ⊧/![n] allTraceFormula) ↔
    ∀ a : V, ∃ cs b, Trace n cs a b := by
  simp [allTraceFormula,trace_correct]

/-- PA induction ranges over the whole model, not an external Lean natural.
The induction predicate is the displayed arithmetic allTraceFormula. -/
theorem trace_exists (n a : V) : ∃ cs b, Trace n cs a b := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ n : V, ∀ a : V, ∃ cs b, Trace n cs a b := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun n : V => ∀ a : V, ∃ cs b, Trace n cs a b) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb allTraceFormula,by trivial,?_⟩
      intro n
      simpa using (allTrace_correct n).symm
    · intro a; exact ⟨?[a],a,trace_zero a⟩
    · intro n ih a
      obtain ⟨cs,b,h⟩ := ih a
      exact ⟨concat cs (stepValue b),stepValue b,trace_extend h⟩
  exact all n a
end Models

theorem pa_proves_trace_total : theory ⊢ traceTotalSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [traceTotalSentence,models_iff]
  simp [allTrace_correct]
  exact trace_exists
#print axioms trace_correct
#print axioms trace_extend
#print axioms trace_exists
#print axioms pa_proves_trace_total
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

