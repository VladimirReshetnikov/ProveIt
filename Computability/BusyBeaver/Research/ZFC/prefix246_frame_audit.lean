import BusyBeaver.ZFC.Prefix246Simulation

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath FiniteZipper Permutation252Frame SymbolicPrefix246 Prefix246Simulation

#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.registerBits_eq
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.flat_map_bit
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.start_concrete
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.source_represents
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.target_concrete
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.target_frame
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.incr_eq_write
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.decr_eq_write
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.unchanged_rebase
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.nth_vregs_append_getD
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.increment_rebase
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.decrement_rebase
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.valid_none
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Simulation.valid_branch

example (vs : List Nat) : RegisterBoxesPerm252.registerBits vs = registerBits vs :=
  registerBits_eq vs

example (n : Nat) (vs : List Nat) (P : List Bool) : flat n vs (P.map Segment.bit) = P :=
  flat_map_bit n vs P

example (n : Nat) (vs : List Nat) (Q : List Bool) (h : Int) :
    concrete n vs (SitePrefix246.start Q) h =
      zAtS (some SitePrefix246.dispatch) h [true]
        (Q ++ List.replicate (n + (40 - Q.length)) false ++ [true] ++ registerBits vs) :=
  start_concrete n vs Q h

example (logical : Configuration) (binary : Config 246) (gap : Nat)
    (spares : List Nat) (Q : List Bool)
    (hf : DispatchFrame SitePrefix246.dispatch binary logical gap spares)
    (hq : Q = consume logical.path Q.length)
    (hz : ∀ b ∈ logical.path.drop Q.length, b = false) (hd : Q.length ≤ 40) :
    Represents (logical.path.length + gap - 40) (vregs logical.registers ++ spares)
      (SitePrefix246.start Q) binary := source_represents logical binary gap spares Q hf hq hz hd

example (n : Nat) (vs : List Nat) (P : List Bool) (overflow : Bool)
    (extra : Nat) (x : Box) (h : Int) :
    concrete n vs (SitePrefix246.target P overflow extra x) h =
      zAtS (some SitePrefix246.dispatch) h [true]
        (P ++ List.replicate (n + (40 + (if overflow then 1 else 0) + extra - P.length)) false ++
          [true] ++ boxBits x vs) := target_concrete n vs P overflow extra x h

example (n : Nat) (vs : List Nat) (P : List Bool) (overflow : Bool)
    (extra : Nat) (x : Box) (R : Registers) (spares : List Nat) (c : Config 246)
    (hlen : P.length ≤ 40 + (if overflow then 1 else 0) + extra)
    (htail : LogicalTailZero R) (hbox : boxBits x vs = registerBits (vregs R ++ spares))
    (hr : Represents n vs (SitePrefix246.target P overflow extra x) c) :
    DispatchFrame SitePrefix246.dispatch c ⟨P, R⟩
      (n + (40 + (if overflow then 1 else 0) + extra - P.length)) spares :=
  target_frame n vs P overflow extra x R spares c hlen htail hbox hr

example (vs : List Nat) (r : Nat) (hr : r < vs.length) :
    incr r vs = writeRegisters vs r (vs.getD r 0 + 1) := incr_eq_write vs r hr

example (vs : List Nat) (r : Nat) (hr : r < vs.length) :
    decr r vs = writeRegisters vs r ((vs.getD r 0).pred) := decr_eq_write vs r hr

example (R : Registers) (spares : List Nat) :
    boxBits (.plain .unchanged) (vregs R ++ spares) = registerBits (vregs R ++ spares) :=
  unchanged_rebase R spares

example (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    (vregs R ++ spares).getD (physOf r) 0 = R r := nth_vregs_append_getD R spares r hr

example (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    boxBits (.plain (.increment (SitePrefix246.physical r hr))) (vregs R ++ spares) =
      registerBits (vregs (update R r (R r + 1)) ++ (spares ++ [1])) :=
  increment_rebase R spares r hr

example (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    boxBits (.plain (.decrement (SitePrefix246.physical r hr))) (vregs R ++ spares) =
      registerBits (vregs (update R r (R r - 1)) ++ spares) := decrement_rebase R spares r hr

example (R : Registers) (spares : List Nat) (hne : spares ≠ []) :
    Valid none (vregs R ++ spares) := valid_none R spares hne

example (R : Registers) (spares : List Nat) (hne : spares ≠ [])
    (r : Nat) (hr : r < 9) (zero : Bool)
    (hz : if zero then R r = 0 else R r ≠ 0) :
    Valid (some (SitePrefix246.physical r hr, zero)) (vregs R ++ spares) :=
  valid_branch R spares hne r hr zero hz
