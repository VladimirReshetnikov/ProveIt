# Literal-table audit and experimental variants

**The 254-state blank-tape record was not beaten in this audit.** This folder
contains a reproducible 252-state *prepared-tape* core and a new 256-state
blank-tape implementation of a rearranged register program. The latter improves
an initially emitted 267-state table, but remains two states larger than the
record. Every claimed table is included as an actual total, transition-closed
binary machine.

## Run the checks

From this folder, with Python 3 and only its standard library:

```sh
python verify.py
```

This checks source hashes, table well-formedness and target closure, every
affine dispatch obligation, protected register-engine transitions, and the
complete finite initialization of each blank-tape machine. It writes
`results/verification.json` and coverage files. To regenerate the three
variants from the frozen baseline, exact decoder DAG and eleven folds:

```sh
python build_variants.py
```

The builder rechecks all dispatch obligations and the exact blank-tape
initialization **after each accepted fold**, then prunes and rechecks the
actual output tables. It records every removed state and every changed unread
branch in `results/*.pruning.json`; only the 267-state intermediate needs
unread-branch rewiring. The 256-state final machine needs none.

## Machines and conventions

| File | Working states | Initial tape | Initial state | Role |
|---|---:|---|---:|---|
| `machines/baseline254.tm` | 254 | all zero | 0 | Exact pinned published record |
| `machines/prepared252.tm` | 252 | `data/prepared252_seed.json` | 96 | Runtime-only reduction; no blank-tape claim |
| `machines/decoder267.tm` | 267 | all zero | 0 | Re-emitted 202-node decoder, before extra folds |
| `machines/decoder256.tm` | 256 | all zero | 0 | Same decoder after eleven verified substitutions |

Each row has `state read write direction next`. Directions are L/R. The
terminal state is label **254**, which has no row. Labels are deliberately
inherited from the source and need not be contiguous: **count rows divided
by two, not the greatest label**. All four files have exactly two transitions
for every working state and every target is a working state or the terminal
state. The tape is two-way infinite and the blank symbol is 0.

The prepared seed starts at head 0 in state 96, with a marker 1 at -1, a gap
of 40 zero cells, a header 1, and nine unary register blocks. Physical register
order is wffstack, param1, axiomcode, scratch2, scratch1, prooflist, nextproof,
topwff, param2. Only nextproof is nonzero, with value 2. All unlisted cells
are zero. The seed is part of this variant's specification and cannot be
ignored when comparing blank-tape state records.

## What the checks establish, and the proof boundary

The pinned published Python affine executor represents a program-counter
region of `D0+n` cells, including the path bits and trailing zeros, with a
free natural parameter n. Thus `D0+n = |P|+k`, where P is the path and k
is the number of trailing zero cells. It verifies all 6,460 register-program
leaves, branching both ways at decrement sites: 8,387 normal, 3 overflow,
and 1 halt obligation, hence **8,391 cases per table**. This is symbolic
checking over arbitrary gaps and register contents under register-box
contracts; it is stronger than testing selected numerical inputs. Baseline
and prepared-core checks use D0=40. The new decoder uses D0=41 and depth35.

The four abstract register-box contracts are mark/skip, increment, zero
decrement and positive decrement. Their generic proofs exist in the pinned
upstream Coq development. This Python audit does not rerun or instantiate a
new Coq theorem. Its trusted boundary includes those contracts, the affine
executor implementation, and the adequacy of the selected protected
transition set. Fifty-five state/symbol pairs are required byte-for-byte
equivalent to the baseline. State 96 is a changed decoder entry and is not
protected. The exterior `(3,0)` transition is also outside the protected
set: the zero-decrement contract exits at state 3 before this transition;
inside the restored register representation there are no adjacent zero
separators to trigger it. The prepared-core fold changes its target from
5 to 48. All other conservatively protected transitions are unchanged.

Finite initialization is checked by literal execution from the all-zero
tape: exactly 264,982 transitions, ending in state 96 with head -8, gap 62,
the expected register values and the complete expected finite tape. This
finite check is not used as a substitute for symbolic dispatch checking.

The candidate DAG's register-machine equivalence certificate is in the
companion decoder package; it must be combined with these backend checks
and the published baseline consistency theorem. This folder alone is **not
a new proof-assistant certificate of the full Con(ZFC) equivalence**. No
claim that ZFC proves its own consistency is made. The proposed formal
endpoint is a theorem inside ZFC equating this machine's nonhalting with
the arithmetized statement Con(ZFC).

## Why two runtime states disappear, but the blank record does not

From valid dispatch states, old state 8 is never used. State5 reads only 0,
and its read-0 transition equals state 48's read-0 transition. Redirecting
5 to 48 and removing8 therefore gives a 252-state runtime core, confirmed
by every affine case. On the blank-tape execution both states serve
initialization. The tested reuse attempts did not find a replacement
initializer. Detailed domains and bounds are in
`results/negative_searches.json`; these negative searches are not
impossibility or minimality proofs.

The strict decoder experiment reduced the register-program DAG from 203
to 202 nodes but initially produced267 working states because exact old
contextual state sharing was lost. Eleven further substitutions, verified
sequentially, recover256. A201-node alternative with longer zero runs in
program-counter words failed38 affine obligations even with an enlarged
gap. Thus a smaller DAG is not itself a smaller or valid Turing machine.

## Optional search reproduction

The search programs are secondary experiments, separate from the positive
verification above. A C++17 compiler is needed for bootstrap searches:

```sh
g++ -O3 -std=c++17 search/boot_search.cpp -o /tmp/zfc_boot_search
/tmp/zfc_boot_search machines/baseline254.tm 0 2000000
/tmp/zfc_boot_search machines/baseline254.tm 1 2000000
/tmp/zfc_boot_search machines/baseline254.tm 2 3000000
/tmp/zfc_boot_search machines/baseline254.tm 3 3000000
g++ -O3 -std=c++17 search/fold_boot_check.cpp -o /tmp/zfc_fold_boot
/tmp/zfc_fold_boot machines/decoder256.tm data/final_boot_pairs.txt data/boot_target.txt 2000000
python search/fold_search.py
```

These finite searches can terminate a candidate on a step limit, tape
boundary or rejected state. No failure is interpreted as a theorem of
semantic impossibility. The direct fold search excludes register-box
source states, root 96, and the bootstrap-specific states 5 and8; it uses
500 units of affine-executor fuel per case. Its recorded result is zero
surviving candidates out of 57,375 tested directed identifications.

## Provenance and attribution

The original 254-state machine is by **Mira-Cult**, mirrored and formally
verified in **Jeff's busy-beaver development**. The exact
machine and the two small published Python helpers are reproduced here
only as necessary analysis inputs, with their original contents intact.
No license grant for them is asserted by this package. The remaining
scripts, derived DAG metadata, transformations and reports were created
for this research audit.

First verification commit:
`c132d7eae8158cd3a9850ea3eb7251158c3dd821` (2026-10-14).
Imported snapshot (byte-matched analysis inputs):
`297ab8df7e5de329605c3875b4934643b371a5e3`.

Pinned ProveIt mirror used for retrieval:
`67086c8d8802ea7b3625a2fc0765d39e2181e335`.

Sources:

- <https://github.com/jeff87654/busy-beaver/tree/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254>
- <https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/e2e/E2E254.v>
- <https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/design/tm.md>
- <https://github.com/VladimirReshetnikov/ProveIt/tree/67086c8d8802ea7b3625a2fc0765d39e2181e335/lib/jeff-busy-beaver-zfc254>

See `provenance.json` for exact byte hashes and individual input paths.
