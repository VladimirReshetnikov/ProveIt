# PA194HX: a distinct physical register layout

PA194HX is a binary single-tape deterministic machine with 194 working states.
It uses the exact source instruction graph of the primary PA194 machine while
exchanging the physical H and X register blocks. It is a new relative
implementation, not an established solution of the requested iPRA calibration.

The logical register order is `(N,T,W,A,D,H,X,Y,L)`. The logical-to-physical
map changes from `[6,2,0,4,3,7,8,5,1]` to `[6,2,0,4,3,8,7,5,1]`.
In the baseline's native labels exactly two rows change:

```
21 1 0 R 60  ->  21 1 0 R 55
45 1 0 R 55  ->  45 1 0 R 60
```

These are live register-routing transitions. This operation exchanges data
locations on the tape, rather than relabeling finite-control states. The
underlying arithmetic routines, the AX grammar, every source address, and all
3,673 source instructions remain unchanged. A separate whole-corpus graph
comparison (in the parent report) excludes arbitrary state renaming, reflection,
global bit exchange, and differences only in terminal write/move actions.

## Machine convention

`machine/pa194hx.tm` has states 0..193, initial state 0 and terminal halt 194.
The head begins at cell 0 on an all-zero, two-way infinite tape. Every row has
format `state read write direction next`. Every working state has both rows.
The halt state is not counted. `pa194hx.native.tm` uses native start 74 and
halt 254; `pa194hx.labels.json` maps dense labels to native labels.

## Verification

Run from any directory:

```
python3 build.py
python3 verify_literal.py
```

The first command reconstructs the new table byte-for-byte from the pinned
baseline and checks dense/native conjugacy. Add `--write` to regenerate table
files. The second command uses the inherited independent whole-tape symbolic
executor against the literal table. Four generic list-sweep lemmas are
rederived from its rows, and all 4,780 source-instruction outcomes are checked.
The symbolic domain has nine independent arbitrary natural register values,
an arbitrary finite nonempty spare tail, and arbitrary padding 48+n, n>=0.
This checker imports no compiler or register-box oracle.

The completed verification used 1,068,062 symbolic operations, with maximum
392 per outcome. Every duration has nonnegative coefficients and constant at
least three. A separate bytearray execution establishes the entire blank-start
tape after exactly 56,134 transitions: native control 84, head -2, source site
25 (`100000`), logical registers `[2,0,0,0,0,0,0,0,0]`, and 26 one-valued spares.
The baseline takes 58,154 transitions to the identical physical seed tape,
so this initialization is shorter by 2,020 transitions. No uniform speed claim
is made for later computation.

`evidence/` preserves the fresh receipts, every symbolic contract, the four
list lemmas, and the complete finite support of the startup tape. The second
command refreshes those files. Assertions must remain enabled.

## Mathematical scope

At source frames, swapping physical blocks 7 and 8 preserves the logical
register vector. The two new router transitions select the swapped blocks;
all register primitives have the same logical effects. Positive-duration
source simulation and exact initialization therefore transport the baseline's
blank-halting behavior to PA194HX. The attached proof note explains the
primitive-recursive witness-transport route.

This relative machine result does not fill the baseline's unresolved
machine/refutation calibration in iPRA. Python checks are executable
mathematical evidence, not a newly kernel-checked theorem. In particular this
package does not assert `iPRA ⊢ Con(PA) ↔ ¬Halt(PA194HX)` unconditionally.

## Attribution

The baseline, source encoding, arithmetic routines and symbolic checker derive
from the ProveIt research cited in `PROVENANCE.json` and `vendor/PROVENANCE.md`.
Imported files retain their supplied licenses. The new contribution is the
H/X register allocation, its table and fresh verification, together with the
comparison and bounded reduction searches in the surrounding research report.
