# Revised AX fall-through source tail

`PA194AX11HAXTail.ax_tail_returns` proves that, in every PRA model whose arithmetic reduct satisfies IΣ₁, the generated revised AX11H source started at `sourceState 3553 a tail` reaches dispatch site 25 with the exact file `PA194ModelMPCompare.values (compareInput a) 0 0`, provided registers 5, 6 and 7 of `a` are zero. The source clock and register values may be nonstandard. This includes the inserted gate push, field reader, second push, comparison preparation, both comparison branches, and return. It does not claim a positive clock.

`PA194AX11HAXTailValues.tail_values` gives the output coordinates: register 0 is retained, 1 is zero, 2 is `cantor (a 1) (a 2)`, 3 is retained, 4 is `a 4 + fixedFirst(a 8)`, 5–7 are zero, and 8 is `fixedSecond(a 8)`. `PA194AX11HZeroGuard.zero_guard_iff` proves `impValue 0 z = 0 ↔ z = 0`; this is why the equality branch of the fall-through can return the same file without an additional copy. In the AX frame where input register 4 is also zero, the output offset is the fourth field itself.

This is a source-tail theorem. It does not prove the preceding AX body reaches site 3553, a full source-to-scheduler command contract, site-10 equivalence for a concrete scheduler, or literal Turing-machine correctness.

After building the preparation and candidate comparison/return prerequisites, run:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/check-ax-tail.sh \
  /path/to/fresh/output /path/to/prep-output /path/to/comparison-output
```

The checker compiles the three local modules from repository sources, snapshots and rechecks source and direct prerequisite object hashes, and records the Lean path. The prerequisite outputs retain their documented transitive baselines, including Python-generated source pinned to the candidate JSON; Lean does not parse the JSON.
