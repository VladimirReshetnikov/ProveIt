# A 252-state candidate with a clean blank-tape startup

The frozen binary table reaches a clean root frame after **82,552 actual
blank-tape steps**. It has **252 working states, 504 transitions and one
halting transition**. All 8,391 conditional instruction cases pass for the
complete original register program under a new assignment of physical
registers. The full nonhalting/Con(ZFC) equivalence has not yet been proved
for this table; the general binary simulation and consistency endpoint remain
open in Lean.

The idea is to change where the existing runtime stores its registers. This
preserves the intended program while changing what the same states do during
startup. The previously known runtime-only deletion of old state 5 into 64
becomes a clean initializer after a suitable permutation. No separate writer,
prepared tape, additional state or reduced logical calculus is supplied.

## Exact artifact and attribution

- [Canonical table](zfc_permutation252.tm): working states 0 through 251,
  start 0, separate halt label 252.
- [Original-label table](zfc_permutation252_old.tm): working labels
  `{0,…,253} \ {5,8}`, start 64, separate halt label 254.
- [Renumbering and exact startup data](renumbering.json): a bijection of the
  working labels and every nonblank tape position at the endpoint.

The canonical SHA-256 is
`8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797`;
the original-label SHA-256 is
`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`.
The sole halting row retains its final write and movement.

This is derived from Mira-Cult's original 254-state machine, Jeff's
verification, and Wade's compiler framework, imported at
`297ab8df7e5de329605c3875b4934643b371a5e3`; see the
[upstream attribution](../../../../../lib/jeff-busy-beaver-zfc254/README.proveit.md).
It incorporates mira-emmy's [public 253-state reduction, PR 20](https://github.com/jeff87654/busy-beaver/pull/20),
head `0d544f2a2e3c18f12278441a74b7879f31cbe856`, and the previously documented
runtime-only fold 5→64. The additional register permutation and this clean
startup were found in the ProveIt investigation on 16 October 2026. The
instruction audit reuses the attributed strict affine checker preserved as
closure-kernel source 27; it has four explicit register-operation contracts.

## What changed

The old-physical-slot to new-physical-slot permutation is

```text
[0,3,4,5,8,1,6,2,7].
```

It fixes the stack and next-candidate slots. On the remaining slots it consists
of cycles `(1 3 5)` and `(2 4 8 7)`. Twelve read-1 selector-entry targets change
from the runtime-252 table. Their write symbols and movements stay the same.
All 55 transition pairs used by the four register-operation contracts remain
literally identical to the original 254 table.

| Logical register | N | T | W | A | D | H | X | Y | L |
|---|---|---|---|---|---|---|---|---|---|
| Old physical slot | 6 | 7 | 0 | 2 | 1 | 8 | 4 | 3 | 5 |
| New physical slot | 6 | 2 | 0 | 4 | 3 | 7 | 8 | 5 | 1 |

The independent generator uses an explicit selector-entry whitelist and
reconstructs the entire table from the attributed baseline. It checks equality
with the frozen artifact, rather than trusting the searcher's table export.
All 252 working states are graph-reachable; ordinary exact state bisimulation
finds no redundant pair. Neither fact proves a lower bound.

## Complete startup frame

After exactly 82,552 transitions, the machine is in original state 96
(canonical state 94), with head at coordinate 2. Its complete tape is

```text
marker at 1; 40 zeros; header at 42;
74 unary blocks, each encoded as 0 followed by value+1 ones;
all other cells blank.
```

The first nine blocks all have value zero. The remaining 65 are spare blocks;
only spare index 8 has value one. There are exactly 77 one-cells. The program
counter is empty, and the distance from the head to the header is 40.
The original register-box contracts allow arbitrary spare values: they require
at least nine blocks, and positive decrement appends a zero spare. This suffix
does not require an additional zero-spare or capacity hypothesis. Physical
spares do not encode logical registers at indices 9 and above.

The search used the common first-write prefix as a speed optimization. Its
nine literal moves leave old state 1, head 7, and the single one at coordinate 8.
The normalized run starts with head 0 and the one at 1. It reaches the target
after 82,543 further moves, at normalized head −5. Adding the prefix gives
82,552 moves and absolute head 2. Independent interpreters also execute the
entire run directly from the blank tape.

## Evidence and proof boundary

The [4,096-permutation census](../results/breakthrough-permutation-census4096.json)
includes the previous 65 controls and seeded distinct random bijections. Each
normalized run has a one-million-step bound and stops at its first sufficient
structural root. It records 3,737 fuel cutoffs, 358 literal halts and this one
structural root. This root has the sufficient certificate truth/truth/empty
stack. A failed or unsafe first root would require further investigation;
the census is not an exhaustive rejection of other permutations.

The [independent audit](../results/candidate252-independent-audit.json)
regenerates the table, checks the complete blank prefix, replays subsequent
instructions literally, and checks all 8,391 affine instruction cases. The
latter are universally parameterized by the extra nonnegative gap and the
register values, with the correct physical register in each decrement guard.
They rely on the four stated register-box contracts. Finite sampling alone
is not the reason for claiming those conditional instruction contracts.

`TablePerm252.lean` and `BootPerm252.lean` contain the literal finite table and
25 kernel-checked bootstrap chunks, transferred to the existing Core
semantics through `FiniteZipper`. They are distinct from the older
`Table252.lean` reduced-calculus experiment. The four `Register*Perm252` modules
instantiate the existing register-operation proofs on the new table. The
complete bootstrap passed Lean 4.32.0 in 93.39 seconds; its axiom dependencies
are only `propext` and `Quot.sound`. All six modules passed, including the
four register operations with arbitrary spare suffixes. Their
[build and axiom audit](../results/permutation252-boot-verification.json)
and [105-unit integration check](../results/permutation252-integration-verification.json)
record the fresh checks and exact dependency-cache scope; the integration
did not rebuild all prior modules.

The remaining argument must combine the finite startup with a proved symbolic
instruction checker, the complete dispatch invariant under this register
permutation, and the existing abstract proof-search results. The zero initial
register vector is safe; completeness from an arbitrary initial candidate
counter, including zero, is already handled by `DirtyProgram254`. The actual
literal-program adapter and full arithmetic consistency endpoint are separate
proof obligations. No claim that PA proves the final equivalence is made yet.

Reproduce the finite candidate audit and the exact generated artifacts with:

```sh
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/candidate252_independent_audit.py --source-table Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm --output /tmp/candidate252-audit.json
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/generate_boot_perm252.py --check
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/generate_register_boxes_perm252.py --check
```
