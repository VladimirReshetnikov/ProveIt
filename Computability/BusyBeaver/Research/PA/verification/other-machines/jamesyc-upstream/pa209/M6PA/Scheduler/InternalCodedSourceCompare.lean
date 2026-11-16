module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCompareSpec
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
theorem compare_loop (base same diff : Nat) (hbound : base+9<3947) (hb : CompareBound base same diff)
    (h x xs : V) (hv : ValidStore xs) :
    ∃t cs,0<t ∧ Trace t cs (stateCode ((base+1:Nat):V) (guardStore xs h x))
      (stateCode (if h=x then ((same+1:Nat):V) else ((diff+1:Nat):V)) (guardStore xs 0 0)) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀h:V,∀xs x:V,ValidStore xs →∃t cs,0<t ∧
      Trace t cs (stateCode ((base+1:Nat):V) (guardStore xs h x))
        (stateCode (if h=x then ((same+1:Nat):V) else ((diff+1:Nat):V)) (guardStore xs 0 0)) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun h:V=>∀xs x:V,ValidStore xs →∃t cs,0<t ∧
      Trace t cs (stateCode ((base+1:Nat):V) (guardStore xs h x))
        (stateCode (if h=x then ((same+1:Nat):V) else ((diff+1:Nat):V)) (guardStore xs 0 0))) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb (compareFormula base same diff),by trivial,?_⟩
      intro h
      simpa using (compare_formula (V:=V) base same diff h).symm
    · intro xs x hv
      have s0 : stepValue (stateCode ((base+1:Nat):V) (guardStore xs 0 x))=
          stateCode ((base+4+1:Nat):V) (guardStore xs 0 x) := by
        simpa using compare_step0 base same diff hbound hb xs 0 x hv
      rcases zero_or_succ x with rfl|⟨x,rfl⟩
      · have s4 : stepValue (stateCode ((base+4+1:Nat):V) (guardStore xs 0 0))=
            stateCode ((same+1:Nat):V) (guardStore xs 0 0) := by
          simpa using compare_step4 base same diff hbound hb xs 0 0 hv
        have ht := trace_one (stateCode ((base+4+1:Nat):V) (guardStore xs 0 0))
        rw [s4] at ht
        obtain ⟨cs,hc⟩ := trace_prepend _ s0 ht
        exact ⟨1+1,cs,by simp,by simpa only [ite_true] using hc⟩
      · obtain ⟨cs,hc⟩ := compare_cleanup base same diff hbound hb xs 0 x hv
        have s4 : stepValue (stateCode ((base+4+1:Nat):V) (guardStore xs 0 (x+1)))=
            stateCode ((base+5+1:Nat):V) (guardStore xs 0 x) := by
          simpa using compare_step4 base same diff hbound hb xs 0 (x+1) hv
        obtain ⟨ds,hd⟩ := trace_prepend _ s4 hc
        obtain ⟨es,he⟩ := trace_prepend _ s0 hd
        refine ⟨((2*0+1)+(3*x+2))+1+1,es,by simp,?_⟩
        simpa using he
    · intro h ih xs x hv
      have s0 : stepValue (stateCode ((base+1:Nat):V) (guardStore xs (h+1) x))=
          stateCode ((base+1+1:Nat):V) (guardStore xs h x) := by
        simpa using compare_step0 base same diff hbound hb xs (h+1) x hv
      rcases zero_or_succ x with rfl|⟨x,rfl⟩
      · obtain ⟨cs,hc⟩ := compare_cleanup base same diff hbound hb xs h 0 hv
        obtain ⟨ds,hd⟩ := trace_prepend _ (compare_step3 base same diff hbound hb xs h 0 hv) hc
        have s1 : stepValue (stateCode ((base+1+1:Nat):V) (guardStore xs h 0))=
            stateCode ((base+3+1:Nat):V) (guardStore xs h 0) := by
          simpa using compare_step1 base same diff hbound hb xs h 0 hv
        obtain ⟨es,he⟩ := trace_prepend _ s1 hd
        obtain ⟨fs,hf⟩ := trace_prepend _ s0 he
        refine ⟨((2*h+1)+(3*0+2))+1+1+1,fs,by simp,?_⟩
        simpa using hf
      · obtain ⟨t,cs,ht,hc⟩ := ih xs x hv
        have s2 : stepValue (stateCode ((base+2+1:Nat):V) (guardStore xs h x))=
            stateCode ((base+1:Nat):V) (guardStore xs h x) := by
          simpa only [Nat.add_zero] using compare_step2 base same diff hbound hb xs h x hv
        obtain ⟨ds,hd⟩ := trace_prepend _ s2 hc
        have s1 : stepValue (stateCode ((base+1+1:Nat):V) (guardStore xs h (x+1)))=
            stateCode ((base+2+1:Nat):V) (guardStore xs h x) := by
          simpa using compare_step1 base same diff hbound hb xs h (x+1) hv
        obtain ⟨es,he⟩ := trace_prepend _ s1 hd
        obtain ⟨fs,hf⟩ := trace_prepend _ s0 he
        refine ⟨t+1+1+1,fs,by simp,?_⟩
        simpa using hf
  exact all h xs x hv
#print axioms compare_loop
end M6.Arithmetic.PA.InternalTrace.CodedSource

