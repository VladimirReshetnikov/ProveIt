# PA194 AX computational core

The generated `PA194AXPlan.source_core` proves the exact effect of the AX
source from site 50 to site 3519 for arbitrary natural register values,
remaining input tail, stack bottom, and untouched registers. It reaches the
unguarded `oldBundle` as the top; its new stack is the separate diagonal
formula followed by the eight PA196 heads and the saved incoming top. The
code respects the constructor argument conventions of `PA196.Commands.Code`.

The theorem composes 251 source-semantic macro contracts checked against the
actual 3,673-site source array. The kernel also checks that their operation
list is exactly the 251 operations expanded from the first 187 of the 190 AX
tokens bound to the source tree in `../pa194-ax-source`. The remaining three
tokens implement guard-copy, guard comparison, and exit; they are outside this
theorem. Guard correctness, the PA-calculus soundness/completeness argument,
and all internal PRA/iPRA claims remain open. Source-tree generation retains
the pinned Python translation boundary described in `../pa194-source-tree`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-ax-core/check.sh
```

The script checks pinned upstream source hashes, rebuilds the dependencies,
generates 26 batches of local source contracts, and kernel-checks their
aggregate. The generated batch statements and operation-list binding are
checked by Lean; the Python generator is not trusted to establish them.
