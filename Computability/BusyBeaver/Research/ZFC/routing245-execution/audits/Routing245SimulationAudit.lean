import BusyBeaver.ZFC.Routing245Simulation

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath FiniteZipper Permutation252Frame SymbolicRouting245 Routing245Simulation

#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.registerBits_eq
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.flat_map_bit
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.start_concrete
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.source_represents
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.target_concrete
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.target_frame
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.incr_eq_write
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.decr_eq_write
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.unchanged_rebase
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.nth_vregs_append_getD
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.increment_rebase
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.decrement_rebase
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.valid_none
#print axioms SetTheory.BusyBeaver.ZFC.Routing245Simulation.valid_branch

example (vs : List Nat) : RegisterBoxesPerm252.registerBits vs = registerBits vs :=
  registerBits_eq vs

example (n : Nat) (vs : List Nat) (P : List Bool) : flat n vs (P.map Segment.bit) = P :=
  flat_map_bit n vs P

example (n : Nat) (vs : List Nat) (Q : List Bool) (h : Int) :
    concrete n vs (SiteRouting245.start Q) h =
      zAtS (some SiteRouting245.dispatch) h [true]
        (Q ++ List.replicate (n + (64 - Q.length)) false ++ [true] ++ registerBits vs) :=
  start_concrete n vs Q h

example (logical : Configuration) (binary : Config 245) (gap : Nat)
    (spares : List Nat) (Q : List Bool)
    (hf : DispatchFrame64 SiteRouting245.dispatch binary logical gap spares)
    (hq : Q = consume logical.path Q.length)
    (hz : ∀ b ∈ logical.path.drop Q.length, b = false) (hd : Q.length ≤ 64) :
    Represents (logical.path.length + gap - 64) (vregs logical.registers ++ spares)
      (SiteRouting245.start Q) binary := source_represents logical binary gap spares Q hf hq hz hd

example (n : Nat) (vs : List Nat) (P : List Bool) (overflow : Bool)
    (extra : Nat) (x : Box) (h : Int) :
    concrete n vs (SiteRouting245.target P overflow extra x) h =
      zAtS (some SiteRouting245.dispatch) h [true]
        (P ++ List.replicate (n + (64 + (if overflow then 1 else 0) + extra - P.length)) false ++
          [true] ++ boxBits x vs) := target_concrete n vs P overflow extra x h

example (n : Nat) (vs : List Nat) (P : List Bool) (overflow : Bool)
    (extra : Nat) (x : Box) (R : Registers) (spares : List Nat) (c : Config 245)
    (hlen : P.length ≤ 64 + (if overflow then 1 else 0) + extra)
    (htail : LogicalTailZero R) (hbox : boxBits x vs = registerBits (vregs R ++ spares))
    (hr : Represents n vs (SiteRouting245.target P overflow extra x) c) :
    DispatchFrame64 SiteRouting245.dispatch c ⟨P, R⟩
      (n + (64 + (if overflow then 1 else 0) + extra - P.length)) spares :=
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
    boxBits (.plain (.increment (SiteRouting245.physical r hr))) (vregs R ++ spares) =
      registerBits (vregs (update R r (R r + 1)) ++ (spares ++ [1])) :=
  increment_rebase R spares r hr

example (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    boxBits (.plain (.decrement (SiteRouting245.physical r hr))) (vregs R ++ spares) =
      registerBits (vregs (update R r (R r - 1)) ++ spares) := decrement_rebase R spares r hr

example (R : Registers) (spares : List Nat) (hne : spares ≠ []) :
    Valid none (vregs R ++ spares) := valid_none R spares hne

example (R : Registers) (spares : List Nat) (hne : spares ≠ [])
    (r : Nat) (hr : r < 9) (zero : Bool)
    (hz : if zero then R r = 0 else R r ≠ 0) :
    Valid (some (SiteRouting245.physical r hr, zero)) (vregs R ++ spares) :=
  valid_branch R spares hne r hr zero hz

example {states : Nat} (dispatch : Fin states) (binary : Config states)
    (logical : Configuration) (gap : Nat) (spares : List Nat) :
    DispatchFrame64 dispatch binary logical gap spares ↔
      64 ≤ logical.path.length + gap ∧ LogicalTailZero logical.registers ∧
        ∃ leftPadding rightPadding : Nat,
          ZipRep binary
            (dispatchZip dispatch binary.head leftPadding rightPadding logical gap spares) :=
  Iff.rfl
