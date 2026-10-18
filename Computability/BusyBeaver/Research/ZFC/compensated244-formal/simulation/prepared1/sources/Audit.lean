import BusyBeaver.ZFC.Compensated244Simulation

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.Compensated244Simulation
open SetTheory.BusyBeaver.ZFC.Compensated244Blocks
open SetTheory.BusyBeaver.ZFC.RuntimePerm252

#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Simulation.simulation
#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Simulation.start_halts_iff
#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Simulation.blank_halts_iff
#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Simulation.blank_nonhalts_iff

example : PositiveBlockBisimulation.Simulation machineRouting245 machineCompensated244 Related := simulation
example (h : Int) (t : Tape) :
    BinaryHalts machineRouting245 (cfgOld 95 h t) ↔ BinaryHalts machineCompensated244 (cfgNew 95 h t) :=
  start_halts_iff h t
example : (∃ t, (machineRouting245.run t).state = none) ↔ ∃ t, (machineCompensated244.run t).state = none :=
  blank_halts_iff
example : (¬ ∃ t, (machineRouting245.run t).state = none) ↔ ¬ ∃ t, (machineCompensated244.run t).state = none :=
  blank_nonhalts_iff
