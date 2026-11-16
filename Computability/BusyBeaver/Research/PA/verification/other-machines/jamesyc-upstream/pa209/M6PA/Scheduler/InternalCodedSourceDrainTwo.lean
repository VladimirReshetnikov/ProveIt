module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceDrainTwoSpec
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem drain_two_loop (entry inc1 inc2 jumpPC exit : Nat) (r s u : Fin 9)
    (hrs : r≠s) (hru : r≠u) (hsu : s≠u)
    (he : entry<3947) (h1 : inc1<3947) (h2 : inc2<3947) (hj : jumpPC<3947)
    (be : Source.resolveAt Source.exactSites entry=some (.dec r (some exit) (some inc1)))
    (b1 : Source.resolveAt Source.exactSites inc1=some (.inc s (some inc2)))
    (b2 : Source.resolveAt Source.exactSites inc2=some (.inc u (some jumpPC)))
    (bj : Source.resolveAt Source.exactSites jumpPC=some (.jump (some entry)))
    (n xs : V) (hv : ValidStore xs) (hr : registers xs r=n) :
    ∃ cs, Trace (4*n+1) cs (stateCode ((entry+1:Nat):V) xs)
      (stateCode ((exit+1:Nat):V) (drainTwoEnd r s u n xs)) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hvs : r.val≠s.val := fun h => hrs (Fin.ext h)
  have hvu : r.val≠u.val := fun h => hru (Fin.ext h)
  have hsu' : s.val≠u.val := fun h => hsu (Fin.ext h)
  have all : ∀ n : V, ∀ xs : V, ValidStore xs → registers xs r=n → ∃ cs,
      Trace (4*n+1) cs (stateCode ((entry+1:Nat):V) xs)
        (stateCode ((exit+1:Nat):V) (drainTwoEnd r s u n xs)) := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun n : V => ∀ xs : V, ValidStore xs → registers xs r=n → ∃ cs,
        Trace (4*n+1) cs (stateCode ((entry+1:Nat):V) xs)
          (stateCode ((exit+1:Nat):V) (drainTwoEnd r s u n xs))) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb (drainTwoFormula entry exit r s u),by trivial,?_⟩
      intro n
      simpa using (drainTwo_formula (V:=V) entry exit r s u n).symm
    · intro xs hv hr
      have hz : drainTwoEnd r s u 0 xs=xs := by
        unfold drainTwoEnd drainEnd
        have hzero : replace r.val xs 0=xs := by simpa only [hr] using replace_current r xs hv
        rw [hzero,add_zero,replace_current s xs hv,add_zero,replace_current u xs hv]
      have hstep : stepValue (stateCode ((entry+1:Nat):V) xs)=stateCode ((exit+1:Nat):V) xs := by
        rw [literal_step entry he _ be]
        simp [instructionValue,hr,destinationCode]
      refine ⟨?[stateCode ((entry+1:Nat):V) xs,stateCode ((exit+1:Nat):V) xs],?_⟩
      simpa only [mul_zero,zero_add,hz,hstep] using trace_one (stateCode ((entry+1:Nat):V) xs)
    · intro n ih xs hv hr
      let ys := replace r.val xs n
      let zs := replace s.val ys (registers xs s+1)
      let ws := replace u.val zs (registers xs u+1)
      have hy : ValidStore ys := replace_valid xs n hv r
      have hz : ValidStore zs := replace_valid ys _ hy s
      have hw : ValidStore ws := replace_valid zs _ hz u
      have hyr : registers ys r=n := registers_replace_same xs n hv r
      have hys : registers ys s=registers xs s := registers_replace_other xs n hv r s hrs.symm
      have hyu : registers ys u=registers xs u := registers_replace_other xs n hv r u hru.symm
      have hzr : registers zs r=n := (registers_replace_other ys _ hy s r hrs).trans hyr
      have hzs : registers zs s=registers xs s+1 := registers_replace_same ys _ hy s
      have hzu : registers zs u=registers xs u := (registers_replace_other ys _ hy s u hsu.symm).trans hyu
      have hwr : registers ws r=n := (registers_replace_other zs _ hz u r hru).trans hzr
      have hws : registers ws s=registers xs s+1 := (registers_replace_other zs _ hz u s hsu).trans hzs
      have hwu : registers ws u=registers xs u+1 := registers_replace_same zs _ hz u
      obtain ⟨cs,htrace⟩ := ih ws hw hwr
      have hend : drainTwoEnd r s u n ws=drainTwoEnd r s u (n+1) xs := by
        simp only [drainTwoEnd,drainEnd,hws,hwu]
        dsimp [ws,zs,ys]
        rw [replace_commute r.val u.val _ _ _ hvu,
          replace_commute r.val s.val _ _ _ hvs,replace_same,
          replace_commute s.val u.val _ _ _ hsu',replace_same,replace_same]
        have hsadd : registers xs s+1+n=registers xs s+(n+1) := by simp only [add_assoc,add_comm,add_left_comm]
        have huadd : registers xs u+1+n=registers xs u+(n+1) := by simp only [add_assoc,add_comm,add_left_comm]
        rw [hsadd,huadd]
      rw [hend] at htrace
      have hdec : stepValue (stateCode ((entry+1:Nat):V) xs)=stateCode ((inc1+1:Nat):V) ys := by
        rw [literal_step entry he _ be]
        simp [instructionValue,hr,destinationCode,ys]
      have hinc1 : stepValue (stateCode ((inc1+1:Nat):V) ys)=stateCode ((inc2+1:Nat):V) zs := by
        rw [literal_step inc1 h1 _ b1]
        simp [instructionValue,hys,destinationCode,zs]
      have hinc2 : stepValue (stateCode ((inc2+1:Nat):V) zs)=stateCode ((jumpPC+1:Nat):V) ws := by
        rw [literal_step inc2 h2 _ b2]
        simp [instructionValue,hzu,destinationCode,ws]
      have hjump : stepValue (stateCode ((jumpPC+1:Nat):V) ws)=stateCode ((entry+1:Nat):V) ws := by
        rw [literal_step jumpPC hj _ bj]
        rfl
      obtain ⟨ds,hd⟩ := trace_prepend _ hjump htrace
      obtain ⟨es,hh⟩ := trace_prepend _ hinc2 hd
      obtain ⟨fs,hf⟩ := trace_prepend _ hinc1 hh
      obtain ⟨gs,hg⟩ := trace_prepend _ hdec hf
      refine ⟨gs,?_⟩
      have hfour : (4:V)=1+1+1+1 := by rw [one_add_one_eq_two,two_add_one_eq_three,three_add_one_eq_four]
      simpa only [mul_add,mul_one,hfour,add_assoc] using hg
  exact all n xs hv hr
#print axioms drain_two_loop
end M6.Arithmetic.PA.InternalTrace.CodedSource

