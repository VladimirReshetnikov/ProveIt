import BusyBeaver.ZFC.PositiveBlockBisimulation

open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.RuntimePerm252
open SetTheory.BusyBeaver.ZFC.PositiveBlockBisimulation

#print axioms Simulation.symm
#print axioms forward
#print axioms halts_iff
#print axioms blank_halts_iff

example {m n : Nat} {M : Machine m} {N : Machine n}
    {R : Config m → Config n → Prop} (s : Simulation M N R) :
    Simulation N M (fun d c => R c d) := s.symm

example {m n : Nat} {M : Machine m} {N : Machine n}
    {R : Config m → Config n → Prop} (s : Simulation M N R)
    (c : Config m) (d : Config n) (h : R c d) :
    BinaryHalts M c → BinaryHalts N d := forward s c d h

example {m n : Nat} {M : Machine m} {N : Machine n}
    {R : Config m → Config n → Prop} (s : Simulation M N R)
    (c : Config m) (d : Config n) (h : R c d) :
    BinaryHalts M c ↔ BinaryHalts N d := halts_iff s c d h

example {m n : Nat} {M : Machine m} {N : Machine n}
    {R : Config m → Config n → Prop} (s : Simulation M N R)
    (h : R (initial m) (initial n)) :
    (∃ t, (M.run t).state = none) ↔ ∃ t, (N.run t).state = none :=
  blank_halts_iff s h
