module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourcePairStores
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem pair_loop (offset : Nat) (hb : offset+41<3947)
    (bound : Source.AXPair.Bound Source.exactSites offset)
    (n xs : V) (hv : ValidStore xs) (ht : registers xs 1=0) (hx : registers xs 6=n) :
    ∃ k cs, 0<k ∧ Trace k cs (stateCode ((offset+36:Nat):V) xs)
      (stateCode ((offset+42:Nat):V) (pairLoopEnd n xs)) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have b4 := bound ⟨4,by decide⟩
  have b5 := bound ⟨5,by decide⟩
  have b9 := bound ⟨9,by decide⟩
  simp only [Source.AXPair.expected,Source.AXPush.expected,Source.AXPair.relocate,
    Option.map_some,Nat.reduceAdd] at b4 b5 b9
  have all : ∀ n : V, ∀ xs : V, ValidStore xs → registers xs 1=0 → registers xs 6=n → ∃ k cs,
      0<k ∧ Trace k cs (stateCode ((offset+36:Nat):V) xs)
        (stateCode ((offset+42:Nat):V) (pairLoopEnd n xs)) := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun n : V => ∀ xs : V, ValidStore xs → registers xs 1=0 → registers xs 6=n → ∃ k cs,
        0<k ∧ Trace k cs (stateCode ((offset+36:Nat):V) xs)
          (stateCode ((offset+42:Nat):V) (pairLoopEnd n xs))) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb (pairLoopFormula offset),by trivial,?_⟩
      intro n
      simpa using (pairLoop_formula (V:=V) offset n).symm
    · intro xs hv ht hx
      have hend : pairLoopEnd 0 xs=xs := by
        unfold pairLoopEnd
        have hz := replace_current 6 xs hv
        change replace 6 xs (registers xs 6)=xs at hz
        rw [hx] at hz
        rw [hz,SourceCantorInternal.triangle_zero,add_zero]
        exact replace_current 7 xs hv
      have hs : stepValue (stateCode ((offset+36:Nat):V) xs)=stateCode ((offset+42:Nat):V) xs := by
        rw [literal_step (offset+35) (by omega) _ b4]
        simp [instructionValue,hx,destinationCode,add_assoc]
      refine ⟨1,?[stateCode ((offset+36:Nat):V) xs,stateCode ((offset+42:Nat):V) xs],by simp,?_⟩
      simpa only [hs,hend] using trace_one (stateCode ((offset+36:Nat):V) xs)
    · intro n ih xs hv ht hx
      have hcy := pairAfterCycle_registers n xs hv ht
      have hct : registers (pairAfterCycle n xs) 1=0 := by rw [hcy];simp [PhysicalRegisters.write]
      have hcx : registers (pairAfterCycle n xs) 6=n := by rw [hcy];simp [PhysicalRegisters.write]
      obtain ⟨k,cs,hk,hs⟩ := ih (pairAfterCycle n xs) (pairAfterCycle_valid n xs hv) hct hcx
      rw [pairLoopEnd_cycle n xs hv ht] at hs
      have hdt : registers (pairAfterDrain n xs) 1=n := by
        rw [pairAfterDrain_registers n xs hv ht];simp [PhysicalRegisters.write]
      obtain ⟨ds,hd⟩ := pair_drain_t offset hb bound n _ (pairAfterDrain_valid n xs hv) hdt
      obtain ⟨es,he⟩ := trace_compose hd hs
      have hj : stepValue (stateCode ((offset+41:Nat):V) (pairAfterDrain n xs))=
          stateCode ((offset+32:Nat):V) (pairAfterDrain n xs) := by
        rw [literal_step (offset+40) (by omega) _ b9]
        rfl
      obtain ⟨fs,hf⟩ := trace_prepend _ hj he
      have hax : registers (pairAfterTwo n xs) 6=n := by
        rw [pairAfterTwo_registers n xs hv];simp [PhysicalRegisters.write]
      obtain ⟨gs,hg⟩ := pair_drain_x offset hb bound n _ (pairAfterTwo_valid n xs hv) hax
      obtain ⟨is,hi⟩ := trace_compose hg hf
      let ys := replace 6 xs n
      have hyv : ValidStore ys := replace_valid xs n hv 6
      have hyy : registers ys 7=registers xs 7 := registers_replace_other xs n hv 6 7 (by decide)
      have hinc : stepValue (stateCode ((offset+37:Nat):V) ys)=
          stateCode ((offset+38:Nat):V) (pairAfterTwo n xs) := by
        rw [literal_step (offset+36) (by omega) _ b5]
        simp [instructionValue,hyy,destinationCode,pairAfterTwo,ys,add_assoc]
      obtain ⟨js,hj⟩ := trace_prepend _ hinc hi
      have hdec : stepValue (stateCode ((offset+36:Nat):V) xs)=
          stateCode ((offset+37:Nat):V) ys := by
        rw [literal_step (offset+35) (by omega) _ b4]
        simp [instructionValue,hx,destinationCode,ys,add_assoc]
      obtain ⟨ks,hks⟩ := trace_prepend _ hdec hj
      exact ⟨_,ks,by simp,hks⟩
  exact all n xs hv ht hx
#print axioms pair_loop
end M6.Arithmetic.PA.InternalTrace.CodedSource

