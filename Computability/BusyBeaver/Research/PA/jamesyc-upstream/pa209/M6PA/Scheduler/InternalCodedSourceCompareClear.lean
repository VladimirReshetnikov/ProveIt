module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCompareSteps
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
def guardStoreGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “z xs h x. ∃ ys, !(replaceGraph 5) ys xs h ∧ !(replaceGraph 6) z ys x”
def compareClearFormula (base diff : Nat) : ArithmeticSemisentence 1 :=
  “n. ∀ xs, !lenDef 9 xs → ∃ ys zs a b cs,
    !guardStoreGraph ys xs 0 n ∧ !guardStoreGraph zs xs 0 0 ∧
    !adjoinDef a ↑(base+7+1) ys ∧ !adjoinDef b ↑(diff+1) zs ∧ !traceGraph (3*n+2) cs a b”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma guardStore_graph (z xs h x : V) : guardStoreGraph.val.Evalb ![z,xs,h,x] ↔ z=guardStore xs h x := by
  simp [guardStoreGraph,(replace_defined 5).df,(replace_defined 6).df,guardStore]
lemma compare_clear_formula (base diff : Nat) (n : V) :
    (compareClearFormula base diff).Evalb ![n] ↔ ∀xs:V,ValidStore xs →∃cs,
      Trace (3*n+2) cs (stateCode ((base+7+1:Nat):V) (guardStore xs 0 n))
        (stateCode ((diff+1:Nat):V) (guardStore xs 0 0)) := by
  simp [compareClearFormula,guardStore_graph,adjoin_defined.df,trace_correct,ValidStore,stateCode,
    len_defined.df,numeral_eq_natCast,Nat.cast_ofNat,eq_comm]
theorem compare_clear_X (base same diff : Nat) (hbound : base+9<3947) (hb : CompareBound base same diff)
    (n xs : V) (hv : ValidStore xs) :
    ∃cs,Trace (3*n+2) cs (stateCode ((base+7+1:Nat):V) (guardStore xs 0 n))
      (stateCode ((diff+1:Nat):V) (guardStore xs 0 0)) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀n:V,∀xs:V,ValidStore xs →∃cs,
      Trace (3*n+2) cs (stateCode ((base+7+1:Nat):V) (guardStore xs 0 n))
        (stateCode ((diff+1:Nat):V) (guardStore xs 0 0)) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n:V=>∀xs:V,ValidStore xs →∃cs,
      Trace (3*n+2) cs (stateCode ((base+7+1:Nat):V) (guardStore xs 0 n))
        (stateCode ((diff+1:Nat):V) (guardStore xs 0 0))) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb (compareClearFormula base diff),by trivial,?_⟩
      intro n
      simpa using (compare_clear_formula (V:=V) base diff n).symm
    · intro xs hv
      have h9 := trace_one (stateCode ((base+9+1:Nat):V) (guardStore xs 0 0))
      rw [compare_step9 base same diff hbound hb xs 0 0 hv] at h9
      have h7 : stepValue (stateCode ((base+7+1:Nat):V) (guardStore xs 0 0))=
          stateCode ((base+9+1:Nat):V) (guardStore xs 0 0) := by
        simpa using compare_step7 base same diff hbound hb xs 0 0 hv
      obtain ⟨cs,hc⟩ := trace_prepend _ h7 h9
      exact ⟨cs,by simpa only [mul_zero,zero_add,one_add_one_eq_two] using hc⟩
    · intro n ih xs hv
      obtain ⟨cs,hc⟩ := ih xs hv
      have h5 : stepValue (stateCode ((base+5+1:Nat):V) (guardStore xs 0 n))=
          stateCode ((base+7+1:Nat):V) (guardStore xs 0 n) := by
        simpa using compare_step5 base same diff hbound hb xs 0 n hv
      obtain ⟨ds,hd⟩ := trace_prepend _ h5 hc
      obtain ⟨es,he⟩ := trace_prepend _ (compare_step8 base same diff hbound hb xs 0 n hv) hd
      have h7 : stepValue (stateCode ((base+7+1:Nat):V) (guardStore xs 0 (n+1)))=
          stateCode ((base+8+1:Nat):V) (guardStore xs 0 n) := by
        simpa using compare_step7 base same diff hbound hb xs 0 (n+1) hv
      obtain ⟨fs,hf⟩ := trace_prepend _ h7 he
      have h3 : (3:V)=1+1+1 := by rw [one_add_one_eq_two,two_add_one_eq_three]
      exact ⟨fs,by simpa only [mul_add,mul_one,h3,add_assoc,add_comm,add_left_comm] using hf⟩
  exact all n xs hv
#print axioms compare_clear_X
end M6.Arithmetic.PA.InternalTrace.CodedSource

