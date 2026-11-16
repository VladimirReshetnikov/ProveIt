module
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Machine.InternalCodedSourceTrace
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 PA196.Arithmetic.Machine.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
attribute [local irreducible] stepValue stepGraph traceGraph

def validGraph : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “c. ∃ pc rs, !fstIdxDef pc c ∧ !sndIdxDef rs c ∧ !lenDef 9 rs ∧ pc<3813”
def traceInvariantFormula : ArithmeticSemisentence 1 :=
  “i. ∀ n cs a b, !traceGraph n cs a b ∧ !validGraph a → i≤n →
    ∃ c, !nthDef c cs i ∧ !validGraph c”
def traceInvariantSentence : ArithmeticSentence := “∀ i, !traceInvariantFormula i”
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma valid_correct (v : Fin 1 → V) : (V ⊧/v validGraph.val) ↔ ValidState (v 0) := by
  simp [validGraph,ValidState,ValidStore,control,store,fstIdx_defined.df,sndIdx_defined.df,
    len_defined.df,numeral_eq_natCast,Nat.cast_ofNat,eq_comm]
lemma traceInvariant_correct (i : V) : (V ⊧/![i] traceInvariantFormula) ↔
    ∀ n cs a b : V, Trace n cs a b → ValidState a → i≤n → ValidState cs.[i] := by
  simp [traceInvariantFormula,trace_correct,valid_correct,nth_defined.df]

/-- The validity invariant is proved by actual PA induction at arbitrary model
trace indices, using the displayed first-order predicate. -/
theorem trace_valid_at {n cs a b : V} (h : Trace n cs a b) (ha : ValidState a)
    (i : V) (hi : i≤n) : ValidState cs.[i] := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ i : V, ∀ n cs a b : V, Trace n cs a b → ValidState a →
      i≤n → ValidState cs.[i] := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun i : V => ∀ n cs a b : V, Trace n cs a b → ValidState a →
        i≤n → ValidState cs.[i]) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb traceInvariantFormula,by trivial,?_⟩
      intro i; simpa using (traceInvariant_correct i).symm
    · intro n cs a b ht ha hi
      rw [ht.2.1]
      exact ha
    · intro i ih n cs a b ht ha hi
      have hin : i<n := lt_of_lt_of_le (by simp) hi
      have hv := ih n cs a b ht ha (le_of_lt hin)
      rw [ht.2.2.2 i hin]
      exact step_valid _ hv
  exact all i n cs a b h ha hi

theorem trace_valid_end {n cs a b : V} (h : Trace n cs a b) (ha : ValidState a) :
    ValidState b := by
  have hv := trace_valid_at h ha n (le_refl n)
  simpa only [h.2.2.1] using hv
end Models

theorem pa_proves_trace_invariant : theory ⊢ traceInvariantSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [traceInvariantSentence,models_iff]
  simp [traceInvariant_correct]
  intro i n cs a b h ha hi
  exact trace_valid_at h ha i hi
#print axioms trace_valid_at
#print axioms trace_valid_end
#print axioms pa_proves_trace_invariant
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

