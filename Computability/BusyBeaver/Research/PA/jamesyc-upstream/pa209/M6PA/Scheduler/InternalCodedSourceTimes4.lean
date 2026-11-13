module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceTimes4Spec
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem times4_loop (base : Nat) (hb : base+6<3947)
    (hbound : Source.AXTimes4.Bound Source.exactSites base)
    (n xs : V) (hv : ValidStore xs) (hr : registers xs 7=n) :
    ∃ cs, Trace (6*n+1) cs (stateCode ((base+1:Nat):V) xs)
      (stateCode ((base+7:Nat):V) (times4End n xs)) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ n : V, ∀ xs : V, ValidStore xs → registers xs 7=n → ∃ cs,
      Trace (6*n+1) cs (stateCode ((base+1:Nat):V) xs)
        (stateCode ((base+7:Nat):V) (times4End n xs)) := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun n : V => ∀ xs : V, ValidStore xs → registers xs 7=n → ∃ cs,
        Trace (6*n+1) cs (stateCode ((base+1:Nat):V) xs)
          (stateCode ((base+7:Nat):V) (times4End n xs))) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb (times4Formula base),by trivial,?_⟩
      intro n
      simpa using (times4_formula (V:=V) base n).symm
    · intro xs hv hr
      have hz : times4End 0 xs=xs := by
        unfold times4End
        have hz : replace 7 xs 0=xs := by
          have h := replace_current 7 xs hv
          change replace 7 xs (registers xs 7)=xs at h
          rwa [hr] at h
        rw [hz,mul_zero,add_zero]
        exact replace_current 1 xs hv
      have hstep : stepValue (stateCode ((base+1:Nat):V) xs)=stateCode ((base+7:Nat):V) xs := by
        rw [literal_step base (by omega) _ (hbound ⟨0,by decide⟩)]
        simp [Source.AXTimes4.expected,instructionValue,hr,destinationCode,add_assoc]
      refine ⟨?[stateCode ((base+1:Nat):V) xs,stateCode ((base+7:Nat):V) xs],?_⟩
      simpa only [mul_zero,zero_add,hz,hstep] using trace_one (stateCode ((base+1:Nat):V) xs)
    · intro n ih xs hv hr
      let y0 := replace 7 xs n
      have hv0 : ValidStore y0 := replace_valid xs n hv 7
      have hr0 : registers y0 7=n := registers_replace_same xs n hv 7
      have ht0 : registers y0 1=registers xs 1 := registers_replace_other xs n hv 7 1 (by decide)
      let y1 := replace 1 y0 (registers xs 1+1)
      have hv1 : ValidStore y1 := replace_valid y0 _ hv0 1
      have hr1 : registers y1 7=n := (registers_replace_other y0 _ hv0 1 7 (by decide)).trans hr0
      have ht1 : registers y1 1=registers xs 1+1 := registers_replace_same y0 _ hv0 1
      let y2 := replace 1 y1 (registers xs 1+2)
      have hv2 : ValidStore y2 := replace_valid y1 _ hv1 1
      have hr2 : registers y2 7=n := (registers_replace_other y1 _ hv1 1 7 (by decide)).trans hr1
      have ht2 : registers y2 1=registers xs 1+2 := registers_replace_same y1 _ hv1 1
      let y3 := replace 1 y2 (registers xs 1+3)
      have hv3 : ValidStore y3 := replace_valid y2 _ hv2 1
      have hr3 : registers y3 7=n := (registers_replace_other y2 _ hv2 1 7 (by decide)).trans hr2
      have ht3 : registers y3 1=registers xs 1+3 := registers_replace_same y2 _ hv2 1
      let y4 := replace 1 y3 (registers xs 1+4)
      have hv4 : ValidStore y4 := replace_valid y3 _ hv3 1
      have hr4 : registers y4 7=n := (registers_replace_other y3 _ hv3 1 7 (by decide)).trans hr3
      have ht4 : registers y4 1=registers xs 1+4 := registers_replace_same y3 _ hv3 1
      obtain ⟨cs,htrace⟩ := ih y4 hv4 hr4
      have hend : times4End n y4=times4End (n+1) xs := by
        simp only [times4End,ht4]
        dsimp [y4,y3,y2,y1,y0]
        simp only [replace_same]
        rw [replace_commute 7 1 _ _ _ (by decide),replace_same,replace_same]
        congr 1
        simp only [mul_add,mul_one,add_assoc,add_comm,add_left_comm]
      rw [hend] at htrace
      have hd : stepValue (stateCode ((base+1:Nat):V) xs)=stateCode ((base+2:Nat):V) y0 := by
        rw [literal_step base (by omega) _ (hbound ⟨0,by decide⟩)]
        simp [Source.AXTimes4.expected,instructionValue,hr,destinationCode,y0,add_assoc]
      have hi1 : stepValue (stateCode ((base+2:Nat):V) y0)=stateCode ((base+3:Nat):V) y1 := by
        rw [literal_step (base+1) (by omega) _ (hbound ⟨1,by decide⟩)]
        simp [Source.AXTimes4.expected,instructionValue,ht0,destinationCode,y1,add_assoc]
      have hi2 : stepValue (stateCode ((base+3:Nat):V) y1)=stateCode ((base+4:Nat):V) y2 := by
        rw [literal_step (base+2) (by omega) _ (hbound ⟨2,by decide⟩)]
        simp [Source.AXTimes4.expected,instructionValue,ht1,destinationCode,y2,add_assoc]
        norm_num
      have hi3 : stepValue (stateCode ((base+4:Nat):V) y2)=stateCode ((base+5:Nat):V) y3 := by
        rw [literal_step (base+3) (by omega) _ (hbound ⟨3,by decide⟩)]
        simp [Source.AXTimes4.expected,instructionValue,ht2,destinationCode,y3,add_assoc]
        norm_num
      have hi4 : stepValue (stateCode ((base+5:Nat):V) y3)=stateCode ((base+6:Nat):V) y4 := by
        rw [literal_step (base+4) (by omega) _ (hbound ⟨4,by decide⟩)]
        simp [Source.AXTimes4.expected,instructionValue,ht3,destinationCode,y4,add_assoc]
        norm_num
      have hj : stepValue (stateCode ((base+6:Nat):V) y4)=stateCode ((base+1:Nat):V) y4 := by
        rw [literal_step (base+5) (by omega) _ (hbound ⟨5,by decide⟩)]
        rfl
      obtain ⟨d0,h0⟩ := trace_prepend _ hj htrace
      obtain ⟨d1,h1⟩ := trace_prepend _ hi4 h0
      obtain ⟨d2,h2⟩ := trace_prepend _ hi3 h1
      obtain ⟨d3,h3⟩ := trace_prepend _ hi2 h2
      obtain ⟨d4,h4⟩ := trace_prepend _ hi1 h3
      obtain ⟨d5,h5⟩ := trace_prepend _ hd h4
      refine ⟨d5,?_⟩
      have hcost : (6:V)=1+1+1+1+1+1 := by norm_num
      simpa only [mul_add,mul_one,hcost,add_assoc] using h5
  exact all n xs hv hr
#print axioms times4_loop
end M6.Arithmetic.PA.InternalTrace.CodedSource

