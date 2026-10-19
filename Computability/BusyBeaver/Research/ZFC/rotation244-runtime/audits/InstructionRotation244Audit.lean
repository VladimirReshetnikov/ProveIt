import BusyBeaver.ZFC.InstructionRotation244

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open Rotation244Simulation
open RegisterPath Permutation252Frame SymbolicRotation244 SiteRotation244
open InstructionRotation244

#print axioms SetTheory.BusyBeaver.ZFC.InstructionRotation244.incRev_length
#print axioms SetTheory.BusyBeaver.ZFC.InstructionRotation244.incPath_length
#print axioms SetTheory.BusyBeaver.ZFC.InstructionRotation244.stripPath_length
#print axioms SetTheory.BusyBeaver.ZFC.InstructionRotation244.breakPath_length
#print axioms SetTheory.BusyBeaver.ZFC.InstructionRotation244.continuePath_length
#print axioms SetTheory.BusyBeaver.ZFC.InstructionRotation244.execute_frame
#print axioms SetTheory.BusyBeaver.ZFC.InstructionRotation244.halt_frame

example (P : List Bool) : (incRev P).length = P.length := incRev_length P

example (P : List Bool) : (incPath P).length = P.length := incPath_length P

example (b : Bool) (k : Nat) (P : List Bool) :
    (stripPath b k P).length ≤ P.length := stripPath_length b k P

example (k : Nat) (P : List Bool) :
    (breakPath k P).length ≤ P.length := breakPath_length k P

example (k : Nat) (P : List Bool) :
    (continuePath k P).length ≤ P.length := continuePath_length k P

example (Q : List Bool) (e : Edge) (R : Registers)
    (spares : List Nat) (n : Nat) (binary : Config 244) (next : Configuration)
    (hcheck : checkSite Q e = true) (htail : LogicalTailZero R)
    (hspares : spares ≠ [])
    (hc : Represents n (vregs R ++ spares) (start Q) binary)
    (he : execute e Q R = some next) :
    ∃ k : Nat, 0 < k ∧ ∃ gap spares', spares' ≠ [] ∧
      DispatchFrame64 dispatch (machineRotation244.runFrom binary k) next gap spares' :=
  execute_frame Q e R spares n binary next hcheck htail hspares hc he

example (Q : List Bool) (R : Registers) (spares : List Nat)
    (n : Nat) (binary : Config 244) (hcheck : checkSite Q .halt = true)
    (hspares : spares ≠ [])
    (hc : Represents n (vregs R ++ spares) (start Q) binary) :
    ∃ k : Nat, 0 < k ∧ (machineRotation244.runFrom binary k).state = none :=
  halt_frame Q R spares n binary hcheck hspares hc
