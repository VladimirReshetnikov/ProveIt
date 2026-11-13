module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCantorInjectiveInternal
public import M6PA.Scheduler.ActualProofCode
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualFieldGraphs
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal

/-- Fixed-arity V1 fields retain the final tail explicitly. Successful parsing
requires that tail to be zero; malformed nonzero tails are not silently ignored. -/
noncomputable def fields2 : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “a b t n. ∃ r, !decodeGraph a r n ∧ !decodeGraph b t r”
noncomputable def fields3 : 𝚺ᴬ₁.Semisentence 5 :=
  .mkSigma “a b c t n. ∃ r, !decodeGraph a r n ∧ !fields2 b c t r”
noncomputable def fields4 : 𝚺ᴬ₁.Semisentence 6 :=
  .mkSigma “a b c u t n. ∃ r, !decodeGraph a r n ∧ !fields3 b c u t r”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem decode_graph_iff_pair (a b n : V) :
    decodeGraph.val.Evalb ![a,b,n] ↔ n=pairValue a b := by
  rw [decode_graph]
  constructor
  · rintro ⟨rfl,rfl⟩
    exact (pairValue_decode n).symm
  · intro h
    subst n
    exact ⟨(decode_pairValue a b).1.symm,(decode_pairValue a b).2.symm⟩

theorem fields2_correct (a b t n : V) :
    fields2.val.Evalb ![a,b,t,n] ↔ n=pairValue a (pairValue b t) := by
  simp [fields2,decode_graph_iff_pair]
theorem fields3_correct (a b c t n : V) :
    fields3.val.Evalb ![a,b,c,t,n] ↔ n=pairValue a (pairValue b (pairValue c t)) := by
  simp [fields3,fields2_correct,decode_graph_iff_pair]
theorem fields4_correct (a b c u t n : V) :
    fields4.val.Evalb ![a,b,c,u,t,n] ↔ n=pairValue a (pairValue b (pairValue c (pairValue u t))) := by
  simp [fields4,fields3_correct,decode_graph_iff_pair,Matrix.comp_vecCons'']

theorem fields2_total (n : V) : ∃ a b t, fields2.val.Evalb ![a,b,t,n] := by
  refine ⟨decodeLeft n,decodeLeft (decodeRight n),decodeRight (decodeRight n),?_⟩
  simp [fields2,decode_graph]
theorem fields3_total (n : V) : ∃ a b c t, fields3.val.Evalb ![a,b,c,t,n] := by
  obtain ⟨b,c,t,h⟩ := fields2_total (decodeRight n)
  refine ⟨decodeLeft n,b,c,t,?_⟩
  simpa [fields3,decode_graph] using h
theorem fields4_total (n : V) : ∃ a b c u t, fields4.val.Evalb ![a,b,c,u,t,n] := by
  obtain ⟨b,c,u,t,h⟩ := fields3_total (decodeRight n)
  refine ⟨decodeLeft n,b,c,u,t,?_⟩
  simpa [fields4,decode_graph,Matrix.comp_vecCons''] using h

open NativeCalculus.ActualBasis.Code in
theorem fields2_standard (a b n : Nat) :
    fields2.val.Evalb ![a,b,0,n] ↔ n=pack2 a b := by
  simp [fields2_correct,pair_standard,pack2]
open NativeCalculus.ActualBasis.Code in
theorem fields3_standard (a b c n : Nat) :
    fields3.val.Evalb ![a,b,c,0,n] ↔ n=pack3 a b c := by
  simp [fields3_correct,pair_standard,pack3,pack2]
open NativeCalculus.ActualBasis.Code in
theorem fields4_standard (a b c u n : Nat) :
    fields4.val.Evalb ![a,b,c,u,0,n] ↔ n=pack4 a b c u := by
  simp [fields4_correct,pair_standard,pack4,pack3,pack2]

#print axioms fields4_correct
#print axioms fields4_total
#print axioms fields4_standard
end M6.PA.ActualFieldGraphs

