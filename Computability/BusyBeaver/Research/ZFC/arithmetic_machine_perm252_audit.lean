import BusyBeaver.ZFC.ArithmeticMachinePerm252
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper ArithmeticMachinePerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.bitsCode_head
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.bitsCode_tail
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.bitsCode_head_bit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.stateCode_zero_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.actionAt_encodeZip
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.encodeZip_step
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.zipStep_head
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.step_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.represents_state
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.numericStep_halted
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.numericStep_invalid
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.initial_represents
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.numericRun_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.numericRun_state_bounded
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.numericRun_state_zero_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.perm252_halts_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.perm252_initial
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.perm252_first_step
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachinePerm252.perm252_halt_edge
example (bs : List Bool) : bitsCode bs % 2 = (bs.getD 0 false).toNat := bitsCode_head bs
example (bs : List Bool) : bitsCode bs / 2 = bitsCode bs.tail := bitsCode_tail bs
example (bs : List Bool) : decide (bitsCode bs % 2 = 1) = bs.getD 0 false := bitsCode_head_bit bs
example (q : Option (Fin n)) : stateCode q = 0 ↔ q = none := stateCode_zero_iff q
example (M : Machine n) (z : ZipConfig n) : actionAt M (encodeZip z) = z.state.map (fun q => M.transition q (z.right.getD 0 false)) := actionAt_encodeZip M z
example (M : Machine n) (z : ZipConfig n) : encodeZip (zipStep M z) = numericStep M (encodeZip z) := encodeZip_step M z
example (M : Machine n) (z : ZipConfig n) : (zipStep M z).head = nextHead M (encodeZip z) z.head := zipStep_head M z
example (M : Machine n) (c : Config n) (u : NumericConfig) (h : Int) (hc : Represents c u h) : Represents (M.step c) (numericStep M u) (nextHead M u h) := step_sound M c u h hc
example (c : Config n) (u : NumericConfig) (h : Int) (hc : Represents c u h) : u.state = 0 ↔ c.state = none := represents_state c u h hc
example (M : Machine n) (l r : Nat) : numericStep M ⟨0,l,r⟩ = ⟨0,l,r⟩ := numericStep_halted M _ rfl
example (M : Machine n) (l r : Nat) : numericStep M ⟨n+1,l,r⟩ = ⟨n+1,l,r⟩ := numericStep_invalid M _ (by simp)
example (M : Machine 0) (l r : Nat) : numericStep M ⟨1,l,r⟩ = ⟨1,l,r⟩ := numericStep_invalid M _ (by simp)
example (n : Nat) : Represents (initial n) (numericInitial n) 0 := initial_represents n
example (M : Machine n) (t : Nat) : Represents (M.run t) (numericRun M t) (numericRunHead M t) := numericRun_sound M t
example (M : Machine n) (t : Nat) : (numericRun M t).state ≤ n := numericRun_state_bounded M t
example (M : Machine n) (t : Nat) : (numericRun M t).state = 0 ↔ (M.run t).state = none := numericRun_state_zero_iff M t
example (t : Nat) : (numericRun machinePerm252 t).state = 0 ↔ (machinePerm252.run t).state = none := numericRun_state_zero_iff machinePerm252 t
example : (∃t, (numericRun machinePerm252 t).state = 0) ↔ ∃t,(machinePerm252.run t).state = none := perm252_halts_iff
example : numericInitial 252 = ⟨1,0,0⟩ := perm252_initial
example : numericStep machinePerm252 ⟨1,0,0⟩ = ⟨28,0,0⟩ := perm252_first_step
example (l r : Nat) : numericStep machinePerm252 ⟨76,l,2*r+1⟩ = ⟨0,2*l+1,r⟩ := perm252_halt_edge l r
-- Halting move is still visible in the absolute-head computation.
example (l r : Nat) (h : Int) : nextHead machinePerm252 ⟨76,l,2*r+1⟩ h = h+1 := by
  have ht : machinePerm252.transition (75 : Fin 252) true = {write:=true,move:=.right,next:=none} := by decide
  simp [nextHead,actionAt,ht,Move.apply]
example : bitsCode [] = 0 := rfl
example : bitsCode [false] = 0 := rfl
example : bitsCode [true,false] = 1 := rfl
example : bitsCode [false,true] = 2 := rfl
-- Invalid states absorb while retaining a nonzero active state, not halt0.
example (M : Machine 3) : (numericStep M ⟨4,7,11⟩).state = 4 := by rw [numericStep_invalid M _ (by decide)]
