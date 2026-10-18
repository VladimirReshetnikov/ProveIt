import BusyBeaver.ZFC.Combined243Simulation

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.Combined243Simulation
open SetTheory.BusyBeaver.ZFC.Combined243Blocks
open SetTheory.BusyBeaver.ZFC.RuntimePerm252

#print axioms SetTheory.BusyBeaver.ZFC.Combined243Simulation.simulation
#print axioms SetTheory.BusyBeaver.ZFC.Combined243Simulation.start_halts_iff
#print axioms SetTheory.BusyBeaver.ZFC.Combined243Simulation.blank_halts_iff
#print axioms SetTheory.BusyBeaver.ZFC.Combined243Simulation.blank_nonhalts_iff

example : PositiveBlockBisimulation.Simulation machineRotation244 machineCombined243 Related := simulation
example (h : Int) (t : Tape) :
    BinaryHalts machineRotation244 (cfgOld 95 h t) ↔ BinaryHalts machineCombined243 (cfgNew 95 h t) :=
  start_halts_iff h t
example : (∃ t, (machineRotation244.run t).state = none) ↔ ∃ t, (machineCombined243.run t).state = none :=
  blank_halts_iff
example : (¬ ∃ t, (machineRotation244.run t).state = none) ↔ ¬ ∃ t, (machineCombined243.run t).state = none :=
  blank_nonhalts_iff
