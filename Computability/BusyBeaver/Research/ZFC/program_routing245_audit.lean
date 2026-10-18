import BusyBeaver.ZFC.ProgramRouting245

/-! Focused source/tree identity audit, not source bisimulation or binary simulation. -/
open SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim

#print axioms ProgramRouting245.program_root
#print axioms ProgramRouting245.program_nnodes
#print axioms ProgramRouting245.nodes_default
#print axioms TreeRouting245.tree_eq_fuel
#print axioms TreeRouting245.tree_eq
#print axioms TreeRouting245.walk_eq_tree
#print axioms TreeRouting245.step_eq_tree
#print axioms TreeRouting245.leaf_count
#print axioms TreeRouting245.node_count
#print axioms TreeRouting245.depth_eq
#print axioms TreeRouting245.halt_count

example : ProgramRouting245.program.root = 202 := ProgramRouting245.program_root
example : ProgramRouting245.program.nnodes = 203 := ProgramRouting245.program_nnodes
example (n : Nat) (hn : 203 ≤ n) : ProgramRouting245.program.nodes n = (.halt, .halt) :=
  ProgramRouting245.nodes_default n hn
example (f : Nat) (hf : 51 ≤ f) :
    toTree ProgramRouting245.program f ProgramRouting245.program.root = TreeRouting245.tree :=
  TreeRouting245.tree_eq_fuel f hf
example : ptree ProgramRouting245.program = TreeRouting245.tree := TreeRouting245.tree_eq
example (P : List Bool) (i : Nat) :
    walk ProgramRouting245.program 204 202 P i = twalk TreeRouting245.tree (P.drop i) i :=
  TreeRouting245.walk_eq_tree P i
example (P : List Bool) (R : Registers) :
    step ProgramRouting245.program ⟨P, R⟩ = match tsite TreeRouting245.tree P with
      | some (e, Q) => execute e Q R
      | none => none := TreeRouting245.step_eq_tree P R
example : TreeRouting245.leafCount TreeRouting245.tree = 6460 := TreeRouting245.leaf_count
example : TreeRouting245.nodeCount TreeRouting245.tree = 6459 := TreeRouting245.node_count
example : TreeRouting245.depth TreeRouting245.tree = 51 := TreeRouting245.depth_eq
example : TreeRouting245.haltCount TreeRouting245.tree = 1 := TreeRouting245.halt_count

-- Concrete break/continue clients retain their path depths and operands.
example : walk ProgramRouting245.program 204 202 [false, false, true] 0 = some (.brk 1, 3) := by
  calc
    _ = twalk TreeRouting245.tree [false, false, true] 0 :=
      TreeRouting245.walk_eq_tree [false, false, true] 0
    _ = some (.brk 1, 3) := by decide +kernel
example : walk ProgramRouting245.program 204 202 [false, true, false, true, true, true] 0 =
    some (.cont 3, 6) := by
  calc
    _ = twalk TreeRouting245.tree [false, true, false, true, true, true] 0 :=
      TreeRouting245.walk_eq_tree [false, true, false, true, true, true] 0
    _ = some (.cont 3, 6) := by decide +kernel
