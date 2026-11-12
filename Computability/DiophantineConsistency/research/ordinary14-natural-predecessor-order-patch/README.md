# Inert predecessor-witness order alternatives

The unelaborated natural-81 and natural-82 drafts contain potential witness
orientation problems. The inspected Mathlib `ExistsAddOfLE` source gives
`b = a + c`; with `a=1`, its witnesses have the form `v = 1+c`. The draft
interfaces `Related` and `HasThreePredecessors` ask for `v = c+1`. In
`Natural81JShift.lean` the existing `simpa [w] using hj` may or may not
resolve that commutation automatically. In `Predecessors82.lean` the final
`exact` uses the three witnesses directly, a likely generic-type mismatch
unless Lean resolves a different declaration. No Lean run has confirmed an
error or a repair. A separate repository proof explicitly uses `add_comm` to
reverse the same kind of witness equation.

The two `.lean.src` files are **inert alternatives**, not imported modules.
They preserve the original declarations and proof text except for explicit
`add_comm` conversions at those witness uses. The original committed drafts,
their pinned source receipts and the existing slim overlay are unchanged.
A future build would need to select, review and authenticate whichever source
versions it uses, update the affected dependency snapshots and perform Lean
elaboration; this packet does not establish a working proof, iPRA theorem,
provider closure or file binding.

The checker pins both original sources, both alternative byte-for-byte
snapshots, the inspected Mathlib declaration source and the repository example.
It confirms the exact two edits and selected declaration text. It does not
resolve the actual imported theorem or run Lean. The current natural-80 gamma
shift draft uses its own explicit `add_comm` conversion; that unelaborated
source is not changed here.

An [independent source review](../../reviews/ordinary14-natural-predecessor-order-patch-independent/README.md)
checks both exact changes and the witness orientation. The alternatives are
not included in the existing endpoint inventory or slim overlay.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural-predecessor-order-patch/check.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural-predecessor-order-patch/result.json
```
