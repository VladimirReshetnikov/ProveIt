module
public import M6.Source.MPCommand
public import M6.Source.NonexitCycle
@[expose] public section
namespace M6.Source.MP

/-- The complete MP macro transports unchanged to the restarting driver:
its finite invocation ends at an actual source ordinal, not a normal exit. -/
theorem command_cyclic (t w d h l : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ CycleSteps exactSites n (config 3804 t w d h l f)
      (config 0
        (if AXCode.wim t (d+(Cantor.decode l).1) = h then d+(Cantor.decode l).1 else 0)
        (if AXCode.wim t (d+(Cantor.decode l).1) = h then Cantor.pair 0 w else w)
        (d+(Cantor.decode l).1) 0 (Cantor.decode l).2 f) := by
  obtain ⟨n,hn,hs⟩ := command t w d h l f
  exact ⟨n,hn,nonexit_to_cycle hs (by simp [config])⟩
#print axioms command_cyclic
end M6.Source.MP

