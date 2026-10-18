import BusyBeaver.ZFC.ProgramRouting245

/-!
The rotated logical program reuses the routed245 DAG and changes two rows.
Keeping the old numbering leaves row4 unreachable from the root. The storage
bound remains203; it is unrelated to the binary machine's244 states.
These definitions and local equalities do not establish whole-program
equivalence, a runtime simulation, or a consistency calibration.
-/
set_option autoImplicit false

namespace SetTheory.BusyBeaver.ZFC.ProgramRotation244
open RegisterPath

def nodes (n : Nat) : Edge × Edge :=
  if n = 5 then (.decnz 6, .cont 2)
  else if n = 6 then (.inc 0, .node 5)
  else ProgramRouting245.program.nodes n

def program : Program where
  nodes := nodes
  root := ProgramRouting245.program.root
  nnodes := ProgramRouting245.program.nnodes

theorem program_root : program.root = 202 := rfl
theorem program_nnodes : program.nnodes = 203 := rfl
theorem node5 : program.nodes 5 = (.decnz 6, .cont 2) := rfl
theorem node6 : program.nodes 6 = (.inc 0, .node 5) := rfl

theorem nodes_unmodified (n : Nat) (h5 : n ≠ 5) (h6 : n ≠ 6) :
    program.nodes n = ProgramRouting245.program.nodes n := by
  simp only [program, nodes, if_neg h5, if_neg h6]

theorem original_loop_rows :
    ProgramRouting245.program.nodes 4 = (.inc 0, .cont 2) ∧
    ProgramRouting245.program.nodes 5 = (.decnz 6, .node 4) ∧
    ProgramRouting245.program.nodes 6 = (.node 5, .inc 0) :=
  ⟨rfl, rfl, rfl⟩

theorem parent_row : program.nodes 7 = (.node 3, .node 6) := rfl

end SetTheory.BusyBeaver.ZFC.ProgramRotation244
