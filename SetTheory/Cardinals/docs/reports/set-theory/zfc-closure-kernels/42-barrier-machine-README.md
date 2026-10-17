# A 252-state blank-tape consistency-machine proposal

This package gives the explicit 252-state binary machine and the complete
finite physical certificate for its newly identified blank-tape bootstrap.
The accompanying report supplies the logical protected-stack argument and
the composition with the published consistency calibration.

The transition table is the previously studied **runtime252** fold of the
Mira-Cult/mira-emmy construction. The new result is that its own blank-tape
orbit reaches a usable proof-enumerator root, despite two enormous short-gap
header collisions and a dirty initial formula stack. Earlier bounded runs
were far too short to see this root.

## What is proved by these artifacts

Starting on the completely blank tape, the supplied machine reaches a
dispatch root whose physical registers are

```
[W, 0, 0, 0, 0, 0, 0, T, 0]
```

in the order stack, additive parameter, axiom selector, second scratch,
first scratch, proof list, next candidate, current formula, cached formula.
The decoder gap is 37. Both W and T are explicit finite natural-number
expressions, stored in the arithmetic DAG rather than expanded. The entire
spare suffix is retained, including its nonzero block values.

Every one of the 8,391 instruction/branch cases passes the universal
register-box decoder check at exact gaps 37, 38, 39 and at the symbolic gap
40+n for every n >= 0. Thus all gaps >= 37 are covered. The universal box
laws accept arbitrary finite spare block values, as the included original
Coq statements in `Box.v` and `Sim.v` show.

The final W is deliberately not represented as a theorem-only stack: code
1, the falsity code, remains at depth 10. The logical repair is a new
enumeration-order invariant. Replacing a marked NIP (opcode 2) by DROP
(opcode 1) gives a strictly smaller candidate with a uniquely corresponding
earlier push. At every NIP the prior pushes therefore exceed prior pops.
The initial stack is never read. Candidate 0 first resets T and the cache
to truth, independently of their initial contents. Completeness from an
arbitrary starting stack follows from the established reset/padding
argument. The detailed proof belongs to the accompanying report.

**Formal status:** the new physical calculation is an ordinary-mathematical
proof with executable finite certificates, using the explicitly identified
universal block laws. The package does not claim a new end-to-end Coq/Lean
kernel build. The included Coq sources document existing results and their
exact hypotheses; their complete build dependencies are not vendored here.

## Reproduce offline

Requirements: Python 3.11 or later, standard library only. No network,
third-party Python package, theorem prover, or expanded enormous integer
tape is needed.

From this directory:

```sh
python code/reproduce.py
```

The command regenerates the full calculation under `replayed/` and compares
the resulting objects with `certificates/`. It checks the six upstream
source hashes and the exact renumbered machine. A successful run ends with
`COMPLETE: blank input reaches the recorded root; all uniform runtime cases pass.`
The complete replay took about eight seconds in the report's environment.
Elapsed time is not part of the mathematical certificate.

To check only the universal runtime part:

```sh
python code/verify_runtime.py
```

To regenerate the two machine tables and their state map:

```sh
python code/generate_machine.py
```

Do not pass Python's `-O` flag: assertions are part of the certificate
checks. `--write-canonical` on the full replay is an authoring option that
replaces the stored objects; it is unnecessary for verification.

## The exact machine

`machines/runtime252.tm` has one row `state read write direction target`
for each of the 504 state/symbol pairs. Working states are 0 through 251,
the blank symbol is 0, the starting state is 0, and the terminal state is
252. The tape is doubly infinite, as in the usual two-symbol busy-beaver
model. There is one head and one tape.

SHA-256, including the two comment lines:

```
5919a993e3c539c91636cdeb1a43461e630ad43bd03e39faed141202a6945987
```

The unrenumbered version uses the source's labels and starts in old state
64, with terminal state 254. Relative to the original 254-state machine,
delete old states 5 and 8 and change exactly one surviving transition:
old state 3 reading 0 changes from `0 L 5` to `0 L 48`. All other surviving
rows are identical. The generator independently checks this fact and the
full old-to-new bijection.

## Certificate layout

| File | Meaning |
| --- | --- |
| `certificates/macro32.json` | Exact algebraic continuation from the 999,186-step literal checkpoint to the first actual short-gap collision. |
| `certificates/recovered34.json` | Exact periodic tape replay of the first collision; complete restored frame and spare suffix. |
| `certificates/macro34.json` | Exact algebraic continuation to the second short-gap collision. |
| `certificates/recovered36.json` | Exact periodic replay to the gap-36 frame. |
| `certificates/lazy36.json` | Complete exact arithmetic DAG and operation ledger to the first root at gap 37. |
| `certificates/root_frame.json` | Full symbolic tape encoding at that root, including absolute head, marker, header and all spare blocks. |
| `certificates/uniform252.json` | All 33,564 universal runtime cases. |
| `certificates/summary.json` | Small machine-readable index of counts and result objects. |
| `source_manifest.json` | Exact upstream revisions, paths, Git blob IDs and SHA-256 hashes. |
| `sections/machine_physical.tex` | Detailed physical proof and results, for inclusion in the main report. |

The first two arithmetic segments represent exactly
1,559,942,868,272,368,994,779 and 16,333,708,580,302,695,167 register
instructions. The two full tape repairs represent exactly
2,079,923,824,320,782,982,672 and 2,101,702,102,394,623,143,846 binary
Turing-machine transitions. These are different units. The total binary
bootstrap time is not claimed to be the sum of those four numbers: the
register instructions themselves each expand to physical tape excursions.
What matters is a proved finite path to the root.

## Why the acceleration is exact

`macro252.py` recognizes fixed finite control graphs for transfer, pair and
inverse-pair loops in the actual pinned program. It applies algebraic
identities for their results and counts, after checking all the local
decoder contracts used by each macro. It never extrapolates a guessed
pattern from a long run. The supplementary small-instance check covers
2,172 exact graph executions over 22 semantic patterns.

`periodic_tape252.py` skips a segment only when a literal constant-direction
transition cycle returns to the same state and input-word phase. It records
the output word and the exact number of copies. Every other transition is
performed directly. Its small sparse-interpreter cross-check compares
11,788 complete configurations.

`lazy252.py` records exact arithmetic expressions. Pairing/unpairing cancel
structurally; small unpairings use exact integer square roots. An unresolved
zero test or unpairing stops the calculation. No unresolved case occurs in
the successful certificate. The root values are nodes 2122 and 6217 of its
6,321-node DAG. The appended zero-block count is node 6315.

Every register expression denotes a natural number by induction: the
recognized transfer, pair and unpair operations preserve natural values,
and atomic subtraction is taken only on a proved positive branch. The
structural zero tests for a sum or Cantor pair use this nonnegativity
invariant. Step-count expressions may have signed intermediate terms;
those expressions are never used as control-flow branch operands.

The absolute final head coordinate is derived in the replay: the literal
checkpoint has head 4; both full tape repairs report relative motion 0;
the final register segment has precisely one program-counter overflow,
with head motion -1. Its final head is consequently 3, its marker 2 and
its header 3+37=40. The origin itself is immaterial on a blank doubly
infinite tape, but the certificate retains it exactly.

## Attribution

The underlying logical calculus, optimized register program, binary
construction and prior machine reductions remain attributed to their
authors, including Andrew James Wade, Mira-Cult, mira-emmy, and jeff87654, together with the ProveIt contributors and prior imported
research. The public 253-state PR and its exact inspected head are recorded
in the manifest. The runtime252 transition table itself was already in the
ProveIt research material. This package contributes the newly completed
blank-bootstrap analysis, finite certificates, and the protected-stack
calibration developed in the accompanying report.

See `NOTICE.md` for the licensing boundary between new material and the
selected upstream sources.
