module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceDrainSpec
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem drain_loop (entry incPC jumpPC exit : Nat) (r s : Fin 9) (hrs : r≠s)
    (he : entry<3947) (hi : incPC<3947) (hj : jumpPC<3947)
    (be : Source.resolveAt Source.exactSites entry=some (.dec r (some exit) (some incPC)))
    (bi : Source.resolveAt Source.exactSites incPC=some (.inc s (some jumpPC)))
    (bj : Source.resolveAt Source.exactSites jumpPC=some (.jump (some entry)))
    (n xs : V) (hv : ValidStore xs) (hr : registers xs r=n) :
    ∃ cs, Trace (3*n+1) cs (stateCode ((entry+1:Nat):V) xs)
      (stateCode ((exit+1:Nat):V) (drainEnd r s n xs)) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hs : s≠r := Ne.symm hrs
  have hvne : r.val≠s.val := fun h => hrs (Fin.ext h)
  have all : ∀ n : V, ∀ xs : V, ValidStore xs → registers xs r=n → ∃ cs,
      Trace (3*n+1) cs (stateCode ((entry+1:Nat):V) xs)
        (stateCode ((exit+1:Nat):V) (drainEnd r s n xs)) := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun n : V => ∀ xs : V, ValidStore xs → registers xs r=n → ∃ cs,
        Trace (3*n+1) cs (stateCode ((entry+1:Nat):V) xs)
          (stateCode ((exit+1:Nat):V) (drainEnd r s n xs))) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb (drainFormula entry exit r s),by trivial,?_⟩
      intro n
      simpa using (drain_formula (V:=V) entry exit r s n).symm
    · intro xs hv hr
      have hz : drainEnd r s 0 xs=xs := by
        unfold drainEnd
        have hzero : replace r.val xs 0=xs := by simpa only [hr] using replace_current r xs hv
        rw [hzero,add_zero]
        exact replace_current s xs hv
      have hstep : stepValue (stateCode ((entry+1:Nat):V) xs)=stateCode ((exit+1:Nat):V) xs := by
        rw [literal_step entry he _ be]
        simp [instructionValue,hr,destinationCode]
      refine ⟨?[stateCode ((entry+1:Nat):V) xs,stateCode ((exit+1:Nat):V) xs],?_⟩
      simpa only [mul_zero,zero_add,hz,hstep] using trace_one (stateCode ((entry+1:Nat):V) xs)
    · intro n ih xs hv hr
      let ys := replace r.val xs n
      let zs := replace s.val ys (registers xs s+1)
      have hy : ValidStore ys := replace_valid xs n hv r
      have hz : ValidStore zs := replace_valid ys _ hy s
      have hyr : registers ys r=n := registers_replace_same xs n hv r
      have hys : registers ys s=registers xs s := registers_replace_other xs n hv r s hs
      have hzr : registers zs r=n := (registers_replace_other ys _ hy s r hrs).trans hyr
      have hzs : registers zs s=registers xs s+1 := registers_replace_same ys _ hy s
      obtain ⟨cs,htrace⟩ := ih zs hz hzr
      have hend : drainEnd r s n zs=drainEnd r s (n+1) xs := by
        simp only [drainEnd,hzs]
        dsimp [zs,ys]
        rw [replace_commute r.val s.val _ _ _ hvne,replace_same,replace_same]
        apply congrArg (replace s.val (replace r.val xs 0))
        simp only [add_assoc,add_comm,add_left_comm]
      rw [hend] at htrace
      have hdec : stepValue (stateCode ((entry+1:Nat):V) xs)=stateCode ((incPC+1:Nat):V) ys := by
        rw [literal_step entry he _ be]
        simp [instructionValue,hr,destinationCode,ys]
      have hinc : stepValue (stateCode ((incPC+1:Nat):V) ys)=stateCode ((jumpPC+1:Nat):V) zs := by
        rw [literal_step incPC hi _ bi]
        simp [instructionValue,hys,destinationCode,zs]
      have hjump : stepValue (stateCode ((jumpPC+1:Nat):V) zs)=stateCode ((entry+1:Nat):V) zs := by
        rw [literal_step jumpPC hj _ bj]
        rfl
      obtain ⟨ds,hd⟩ := trace_prepend _ hjump htrace
      obtain ⟨es,hh⟩ := trace_prepend _ hinc hd
      obtain ⟨fs,hf⟩ := trace_prepend _ hdec hh
      refine ⟨fs,?_⟩
      have hthree : (3:V)=1+1+1 := by rw [one_add_one_eq_two,two_add_one_eq_three]
      simpa only [mul_add,mul_one,hthree,add_assoc] using hf
  exact all n xs hv hr
#print axioms drain_loop
end M6.Arithmetic.PA.InternalTrace.CodedSource

