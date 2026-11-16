module
public import M6.Source.CyclicDriver
public import M6.Source.S36Command
@[expose] public section

/-! Literal S36 invocation outcomes transported to the explicitly restarting
source driver. This does not identify the driver with physical root frames. -/
namespace M6.Source.S36Command

theorem cyclic_halt_of_sum_one (t w h : Nat) (f : Registers) (hs : t+h = 1) :
    CycleSteps exactSites (6*t+7*h+10) (start t w h f) (halted h w 0 f) :=
  halt_to_cycle (halt_of_sum_one t w h f hs) rfl

/-- A successful S36 command returns to the next enumeration iteration, not
an absorbing exit and not the machine's halting state. -/
theorem cyclic_normal_of_sum_ne_one (t w h : Nat) (f : Registers) (hs : t+h ≠ 1) :
    ∃ m, 0 < m ∧ m ≤ (8*t+9*h+9) + popCost w ∧
      CycleSteps exactSites m (start t w h f)
        ⟨.at 0, registers h (Cantor.decode w).2 (Cantor.decode w).1 f⟩ :=
  normal_to_cycle (normal_of_sum_ne_one t w h f hs) (by simp [start]) rfl

#print axioms cyclic_halt_of_sum_one
#print axioms cyclic_normal_of_sum_ne_one
end M6.Source.S36Command

