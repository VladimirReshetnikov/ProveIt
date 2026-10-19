import BusyBeaver.ZFC.TreeRotation240

/-! Exact complete source tree; no binary runtime or all-sites conclusion. -/
open SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim

#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation240.tree_eq_fuel
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation240.tree_eq
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation240.walk_eq_tree
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation240.step_eq_tree
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation240.leaf_count
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation240.node_count
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation240.depth_eq
#print axioms SetTheory.BusyBeaver.ZFC.TreeRotation240.halt_count

example (f : Nat) (hf : 51 ≤ f) :
    toTree SourceRotation240.program f SourceRotation240.program.root = TreeRotation240.tree :=
  TreeRotation240.tree_eq_fuel f hf
example : ptree SourceRotation240.program = TreeRotation240.tree := TreeRotation240.tree_eq
example (P : List Bool) (i : Nat) :
    walk SourceRotation240.program 204 202 P i = twalk TreeRotation240.tree (P.drop i) i :=
  TreeRotation240.walk_eq_tree P i
example (P : List Bool) (R : Registers) :
    step SourceRotation240.program ⟨P, R⟩ = match tsite TreeRotation240.tree P with
      | some (e, Q) => execute e Q R
      | none => none := TreeRotation240.step_eq_tree P R
example : TreeRotation240.leafCount TreeRotation240.tree = 6455 := TreeRotation240.leaf_count
example : TreeRotation240.nodeCount TreeRotation240.tree = 6454 := TreeRotation240.node_count
example : TreeRotation240.depth TreeRotation240.tree = 51 := TreeRotation240.depth_eq
example : TreeRotation240.haltCount TreeRotation240.tree = 1 := TreeRotation240.halt_count

-- One of the four row169 occurrences: increment5, then decrement6/continue2.
example : walk SourceRotation240.program 204 202
    [true, true, true, true, true, false, false, true, true, false] 0 =
    some (.inc 5, 10) := by
  calc
    _ = twalk TreeRotation240.tree
        [true, true, true, true, true, false, false, true, true, false] 0 :=
      TreeRotation240.walk_eq_tree
        [true, true, true, true, true, false, false, true, true, false] 0
    _ = some (.inc 5, 10) := by decide +kernel
example : walk SourceRotation240.program 204 202
    [true, true, true, true, true, false, false, true, true, true, true] 0 =
    some (.cont 2, 11) := by
  calc
    _ = twalk TreeRotation240.tree
        [true, true, true, true, true, false, false, true, true, true, true] 0 :=
      TreeRotation240.walk_eq_tree
        [true, true, true, true, true, false, false, true, true, true, true] 0
    _ = some (.cont 2, 11) := by decide +kernel
