import BusyBeaver.ZFC.ProgramRotation244

open SetTheory.BusyBeaver.ZFC RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ProgramRotation244.program_root
#print axioms SetTheory.BusyBeaver.ZFC.ProgramRotation244.program_nnodes
#print axioms SetTheory.BusyBeaver.ZFC.ProgramRotation244.node5
#print axioms SetTheory.BusyBeaver.ZFC.ProgramRotation244.node6
#print axioms SetTheory.BusyBeaver.ZFC.ProgramRotation244.nodes_unmodified
#print axioms SetTheory.BusyBeaver.ZFC.ProgramRotation244.original_loop_rows
#print axioms SetTheory.BusyBeaver.ZFC.ProgramRotation244.parent_row

example : ProgramRotation244.program.root = 202 := ProgramRotation244.program_root
example : ProgramRotation244.program.nnodes = 203 := ProgramRotation244.program_nnodes
example : ProgramRotation244.program.nodes 5 = (.decnz 6, .cont 2) := ProgramRotation244.node5
example : ProgramRotation244.program.nodes 6 = (.inc 0, .node 5) := ProgramRotation244.node6
example (n : Nat) (h5 : n ≠ 5) (h6 : n ≠ 6) :
    ProgramRotation244.program.nodes n = ProgramRouting245.program.nodes n :=
  ProgramRotation244.nodes_unmodified n h5 h6
example : ProgramRouting245.program.nodes 6 = (.node 5, .inc 0) :=
  ProgramRotation244.original_loop_rows.2.2
example : ProgramRotation244.program.nodes 7 = (.node 3, .node 6) :=
  ProgramRotation244.parent_row
