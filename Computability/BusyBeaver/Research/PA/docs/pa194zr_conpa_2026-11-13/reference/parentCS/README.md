# PA194CS: symmetric-guard cached-head machine

The complete table is `machine/pa194CS.tm`: 194 working states, start 0,
halt 194, 388 transitions, blank two-way binary tape, head initially at zero.
Rows have format `state read write direction next`, with direction L or R.
The halt label has no rows and is excluded from the working-state count.

SHA-256 of the dense table:

```
1c71002e5b8a2ddd1dd1311a2c54c424764624b611b69c8efbee1ac23c2e6f5f
```

This machine shortens the cached-head Shift implementation. Instead of
restoring scratch X back to H and incrementing X, it leaves H zero and
increments H. The existing symmetric comparison then tests `(H,X)=(1,h)`
instead of `(h,1)`. On mismatch that comparison clears both registers,
so the entire surviving command-store effect is unchanged.

The source loses three primitive sites (3,646 instead of 3,649). One new
reader initially brings the table to 195 states; the exact contextual fold
41 into 330 recovers 194. It changes a fixed decrement interface as well
as the command source, beyond the seven inherited AX reader folds.

## Reproduce

Python 3.10 or later, standard library only, assertions enabled:

```sh
python3 build.py
python3 verification/check.py
```

The builder checks exact source binding, 4,745 arbitrary-register contracts,
the new fold on all four history/read-bit cases, and whole-tape startup.
The independent verifier imports neither compiler nor arithmetic-box oracle;
it rederives four list-sweep lemmas from the literal table and verifies
all 4,745 source outcomes plus the full blank seed using a separate simulator.
It checks the changed source tail, not a false equality claim with PA195C's
source graph.

The delivered folded table's startup is **57,768** transitions. The
unfolded 195-state intermediate uses 57,594 transitions. State counts and
startup lengths in the main claim refer to the folded table.

`proof_symmetric.tex` gives the guard proof, exact source edit, all-tape
contextual quotient, and consistency-calibration interface. Logical
calibration to PA is inherited from the supplied separate-head calculus;
the symmetric guard preserves the cached command semantics. Executable
certificates and this ordinary proof are not a newly kernel-checked Lean
or Rocq endpoint.

This folder is self-contained. Inputs pin PA194C and the unchanged axiom
grammar, source comparator and parent source graph. The copied source and
symbolic engines retain the licenses and attribution supplied in the
primary PA194 packet and the independent runtime's `reference/README.md`.
