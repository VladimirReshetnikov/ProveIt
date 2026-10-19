import BusyBeaver.ZFC.TreeRotation244

/-! Exact complete rotated source tree; no binary runtime or coverage conclusion. -/
open SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim

#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation244.tree_eq_fuel
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation244.tree_eq
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation244.walk_eq_tree
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation244.step_eq_tree
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation244.leaf_count
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation244.node_count
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation244.depth_eq
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation244.halt_count

example (f : Nat) (hf : 51 ≤ f) :
    toTree ProgramRotation244.program f ProgramRotation244.program.root = TreeRotation244.tree :=
  TreeRotation244.tree_eq_fuel f hf
example : ptree ProgramRotation244.program = TreeRotation244.tree := TreeRotation244.tree_eq
example (P : List Bool) (i : Nat) :
    walk ProgramRotation244.program 204 202 P i = twalk TreeRotation244.tree (P.drop i) i :=
  TreeRotation244.walk_eq_tree P i
example (P : List Bool) (R : Registers) :
    step ProgramRotation244.program ⟨P, R⟩ = match tsite TreeRotation244.tree P with
      | some (e, Q) => execute e Q R
      | none => none := TreeRotation244.step_eq_tree P R
example : TreeRotation244.leafCount TreeRotation244.tree = 6459 := TreeRotation244.leaf_count
example : TreeRotation244.nodeCount TreeRotation244.tree = 6458 := TreeRotation244.node_count
example : TreeRotation244.depth TreeRotation244.tree = 51 := TreeRotation244.depth_eq
example : TreeRotation244.haltCount TreeRotation244.tree = 1 := TreeRotation244.halt_count

-- Actual changed subtree at pointer 011: increment first, then decnz/continue.
example : walk ProgramRotation244.program 204 202 [false, true, true, false] 0 =
    some (.inc 0, 4) := by
  calc
    _ = twalk TreeRotation244.tree [false, true, true, false] 0 :=
      TreeRotation244.walk_eq_tree [false, true, true, false] 0
    _ = some (.inc 0, 4) := by decide +kernel
example : walk ProgramRotation244.program 204 202 [false, true, true, true, true] 0 =
    some (.cont 2, 5) := by
  calc
    _ = twalk TreeRotation244.tree [false, true, true, true, true] 0 :=
      TreeRotation244.walk_eq_tree [false, true, true, true, true] 0
    _ = some (.cont 2, 5) := by decide +kernel
