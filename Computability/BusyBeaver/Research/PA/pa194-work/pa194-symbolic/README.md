# PA194 symbolic contract soundness

`PA194Symbolic.lean` supplies a reusable symbolic-contract representation and
proves that a successful checked symbolic test gives positive physical
reachability on any machine satisfying the imported M6 register-box lemmas,
for every valid register file and gap. For a frame target, normalization
identifies the exact physical endpoint.

The exact PA194 parent-machine binding is in `../pa194-runtime`. The source-tree-derived physical coverage checker is in `../pa194-coverage`;
it builds this module as part of its clean check. These are standard-Lean results, not
PRA/iPRA consistency theorems.
