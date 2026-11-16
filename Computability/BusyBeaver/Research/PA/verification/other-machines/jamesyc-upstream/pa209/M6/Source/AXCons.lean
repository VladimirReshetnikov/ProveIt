module
public import M6.Source.AXPushParamSteps
public import M6.Source.AXPop
public import M6.Source.AXPairFirst
public import M6.Source.AXCode
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXCons

/-- The two arithmetic helpers describe the same complete physical register store. -/
theorem registers_bridge (t w x y : Nat) (f : Registers) :
    Unpair.registers ⟨w,f 5,x,y,write f 1 t⟩ = AXPush.registers ⟨t,w,x,y,f⟩ := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;> by_cases h5 : r = 5 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [Unpair.registers,AXPush.registers,write]

/-- Formula constructor, with explicit row bindings and arbitrary unrelated frame. -/
theorem cons {sites : Array Site} {offset : Nat}
    (hpop : UnpairPartial.Bound sites (offset+20))
    (hpair : AXPair.Bound sites offset)
    (hfour : AXTimes4.Bound sites (offset+41))
    (t w : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps sites n (AXPushParam.configAt offset 20 ⟨t,w,0,0,f⟩)
      (AXPushParam.configAt offset 47
        ⟨AXCode.wim (Cantor.decode w).1 t,(Cantor.decode w).2,0,0,f⟩) := by
  have a := UnpairPartial.decode_prefix hpop w (f 5) (write f 1 t)
  have aa : Steps sites (Unpair.loopCost w (0,0)+(3*(Cantor.decode w).2+1))
      (AXPair.configAt offset 20 ⟨t,w,0,0,f⟩)
      (AXPair.configAt offset 31 ⟨t,(Cantor.decode w).2,(Cantor.decode w).1,0,f⟩) := by
    simpa only [UnpairPartial.configAt,UnpairPartial.registers,AXPair.configAt,
      AXPair.registers,registers_bridge,Nat.add_assoc] using a
  obtain ⟨n,hn,hb⟩ := AXPair.pair hpair t (Cantor.decode w).2 (Cantor.decode w).1 f
  have c := AXTimes4.times4 hfour 0 (Cantor.decode w).2 0
    (Cantor.pair (Cantor.decode w).1 t) f
  have cc : Steps sites (6*Cantor.pair (Cantor.decode w).1 t+1)
      (AXPair.configAt offset 41 ⟨0,(Cantor.decode w).2,0,Cantor.pair (Cantor.decode w).1 t,f⟩)
      (AXPair.configAt offset 47 ⟨AXCode.wim (Cantor.decode w).1 t,(Cantor.decode w).2,0,0,f⟩) := by
    simpa [AXTimes4.configAt,AXTimes4.registers,AXPair.configAt,AXPair.registers,
      AXCode.wim,Cantor.implication,Nat.add_assoc] using c
  refine ⟨(Unpair.loopCost w (0,0)+(3*(Cantor.decode w).2+1))+n+
    (6*Cantor.pair (Cantor.decode w).1 t+1),by omega,?_⟩
  exact (aa.append hb).append cc

theorem first_cons (t w : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (AXPush.configAt 77 ⟨t,w,0,0,f⟩)
      (AXPush.configAt 104 ⟨AXCode.wim (Cantor.decode w).1 t,(Cantor.decode w).2,0,0,f⟩) :=
  cons AXPop.bound_first AXPairFirst.pair_bound AXPairFirst.times_bound t w f

private theorem row104 : resolveAt exactSites 104 = some (.inc 1 (some 105)) := by rfl
private theorem row105 : resolveAt exactSites 105 = some (.inc 1 (some 106)) := by rfl
private theorem write_t (s : AXPush.Store) (v : Nat) :
    write (AXPush.registers s) 1 v = AXPush.registers {s with t := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,AXPush.registers]

theorem universal_tag (t w : Nat) (f : Registers) :
    Steps exactSites 2 (AXPush.configAt 104 ⟨t,w,0,0,f⟩)
      (AXPush.configAt 106 ⟨t+2,w,0,0,f⟩) := by
  apply Steps.cons
  change Steps exactSites 1 (step exactSites ⟨.at 104, AXPush.registers ⟨t,w,0,0,f⟩⟩) _
  rw [step_of_resolved row104]
  simp only [execute,destination,AXPush.registers,ite_true,write_t]
  apply Steps.cons
  change Steps exactSites 0 (step exactSites ⟨.at 105, AXPush.registers ⟨t+1,w,0,0,f⟩⟩) _
  rw [step_of_resolved row105]
  simp only [execute,destination,AXPush.registers,ite_true,write_t]
  exact Steps.refl _

theorem first_universal (t w : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (AXPush.configAt 77 ⟨t,w,0,0,f⟩)
      (AXPush.configAt 106 ⟨AXCode.wal (Cantor.decode w).1 t,(Cantor.decode w).2,0,0,f⟩) := by
  obtain ⟨n,hn,h⟩ := first_cons t w f
  refine ⟨n+2,by omega,?_⟩
  exact h.append (universal_tag (AXCode.wim (Cantor.decode w).1 t) (Cantor.decode w).2 f)
#print axioms cons
#print axioms first_cons
#print axioms first_universal
end M6.Source.AXCons

