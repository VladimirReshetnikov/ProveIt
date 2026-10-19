# Framework reduction experiments: exact 244-state obstruction

**Status: no verified solution below 245 states is claimed by this component.**

This directory contains a concrete **244-working-state experiment** obtained
by deleting one more scanner state from the supplied 245-state machine. Its
blank initialization succeeds, but the unchanged instruction compiler fails
an intended next-frame transition. The failure is proved for an infinite
family of complete tapes, with arbitrary padding and arbitrary nonempty
spare lists. The resulting obstruction map gives concrete grammar paths to
repair; the finite searches document additional state-elimination attempts.

`machine/scanner5-experiment244-old.tm` is an **UNVALIDATED EXPERIMENT**. It
must not be cited as a proved 244-state consistency machine.

## Reference and reproduction

The required external dependency is the extracted supplied
`zfc245-proof-20261018` package. No network access or third-party Python
packages are required. Run from this directory, replacing the two example
paths with the relevant directories:

```sh
python3 verify.py --reference /path/to/zfc245-proof-20261018 --output /tmp/framework-check
```

The default run takes approximately one second on the development machine.
It reconstructs the exact table patch, checks the local contraction rows,
replays both blank initializations, independently checks the experimental
one using a dense tape, reproduces the concrete wrong successor, proves its
parametric extension using the inherited symbolic checker, regenerates the
grammar-ancestry map, and checks the frozen search/audit summaries for
internal consistency. It also regenerates all 55 semantic word/read pairs
used during the experimental bootstrap and checks that the baseline uses
the same set of pairs.

The pinned baseline is `certificate/machine_old.tm`, SHA-256:

```text
f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267
```

This table uses historical state labels: start 95, dispatcher 96, and a
target-only halt 254. Label 255 is a working state. Counts are numbers of
working states, not the largest numeric state label. The experiment has
488 transition rows: 116 framework states and 128 grammar states.

To rerun the expensive universal scanner audit:

```sh
python3 verify.py --reference /path/to/zfc245-proof-20261018 --output /tmp/framework-full --full-scanner-audit
```

The original complete audit took approximately twelve minutes. The optional
run compares all regenerated fields except elapsed time with the frozen
result. It prints progress every 1,000 cases.

To regenerate the finite fixture corpus from the reference, compile the
four C++17 searches with `g++`, and repeat the bounded searches:

```sh
python3 verify.py --reference /path/to/zfc245-proof-20261018 --output /tmp/framework-search --search
```

This optional route was independently rerun through the packaged entrypoint;
all frozen counters, the 762-option file, and the joint-search results were
reproduced, apart from elapsed time. The corpus and executables are created
only in the requested output directory. They are not distributed here.
The two optional flags can be combined. Do not run Python with `-O`, which
disables the certificate assertions.

## The local scanner contraction

The baseline contains these rows:

| State/read | Write | Move | Next state |
|---|---:|---|---:|
| 41 / 0 | 0 | L | 58 |
| 58 / 0 | 0 | L | 84 |
| 58 / 1 | 1 | L | 4 |
| 84 / 0 | 0 | R | 84 |
| 84 / 1 | 1 | R | 96 |

Delete state 58 and replace `41 / 0` by `(0,L,84)`. No other transition
changes. There are no remaining references to state 58.

**Local lemma.** If the machine is at state 41 with head at cell `x`, and
cells `x`, `x-1`, and `x-2` are all zero, the old machine makes three moves
to state 84 at cell `x-1`; the experiment makes one move to exactly that
same configuration. Every tape cell agrees. The proof is the literal
three-row composition, and the exterior tape is arbitrary.

The premise is essential. This component calls the resulting shorter
scanner “scanner5,” following the zero-run convention in the supplied
construction. This name does not assert that every source program with a
particular zero-run bound has been verified with it.

## Blank initialization: exact success, different endpoint

The supplied 245-state machine reaches its complete root frame after
407,915 moves. During this prefix, the transition `41 / 0` is entered
1,411 times; one entry fails the local lemma's premise. At zero-based tick
46,732, the head is at cell 0 and the three leftward bits are `0,1,1`.
Consequently, the experimental initialization cannot be justified merely
by shortening the old prefix by two moves at each entry.

A fresh sparse simulation, followed by an independent dense replay, gives
this exact experimental endpoint after **818,324 moves**:

| Field | Exact value |
|---|---|
| State | 96 |
| Head / isolated marker | -8 / -9 |
| Empty program counter | `""` |
| Header / header distance | 237 / 245 |
| Physical registers | `(0,1,0,4,0,0,6,0,0)` |
| Logical `(N,T,W,A,D,H,X,Y,L)` | `(6,0,0,0,4,0,0,0,1)` |
| Spare blocks | 233 blocks, each encoding value 1 |
| One cells | 488; all remaining cells are zero |

The complete finite support is in `results/scanner5-exact-boot.json`.
The verifier checks it against a newly painted mathematical frame, rather
than only comparing two stored traces. The register values satisfy the
inherited dirty-root guard `T=W=H=0`. Initialization alone cannot establish
the source-to-machine theorem because the runtime obstruction below remains.

## A proved wrong next-frame family

Use the complete dispatch frame with head 0, program counter
`11101001001000000`, all nine physical registers zero, header distance
`64+g` for arbitrary natural `g`, and **any nonempty finite spare list of
natural values**. The source leaf is `CD(1)` under its zero guard.

The supplied 245-state runtime reaches the intended complete successor

```text
1110100100100001
```

in exactly `574+8*g` moves. The experimental 244-state runtime instead
reaches the complete successor

```text
11101001001001
```

in exactly `650+8*g` moves. Both endpoints have head 0, the same header
distance, unchanged primary registers, and the same entire spare list.
The whole exterior tape is included in the equality check.

The symbolic experimental trace contains 245 checked rewrite steps. Earlier
visits to dispatcher 96 do occur, and they are explicitly excluded as
complete source frames. One has nonblank cells to the left of its required
isolated marker. The other three have a one at relative cell 51, inside
the required zero padding: every source path has length at most 51 and
every normal header distance is at least 64. This establishes the first
complete output, not merely a mismatch at an arbitrary intermediate
dispatcher visit.

The finite instance `g=0`, spare list `[1]`, is also replayed by the direct
literal interpreter. Its first complete successors occur after 574 and
650 moves respectively. Frozen finite and symbolic reports are in
`results/scanner5-literal-wrong-successor.json` and
`results/scanner5-symbolic-wrong-successor.json`.

This proves a failure of the intended next-frame instruction contract. It
does **not** prove that this input is reached from the experiment's blank
tape, nor does it settle whether some different interpretation of that
machine might have a consistency equivalence. The existing compositional
proof cannot be transferred unchanged.

## The complete obstruction map

The inherited whole-frame symbolic verifier was run on all **8,391**
guarded source cases, with independent arbitrary primary values, arbitrary
padding, and an arbitrary nonempty spare suffix. A watcher checked the
local scanner premise along the verified baseline executions.

It found **99 dangerous finite-run entries**, one in each of 99 source
cases, across **50 distinct program-counter paths**:

| Guarded operation | Cases |
|---|---:|
| Zero decrement | 49 |
| Positive decrement | 49 |
| Increment | 1 |

Every listed entry is at a finite zero run of length exactly one in the
leftward representation, immediately followed on its left by a one.
Every offending program-counter path ends in six zeros. Infinite outer
blank atoms are excluded from this finite-run count; they automatically
satisfy the three-zero premise. The numbers are not a count of all literal
scanner visits over arbitrary configurations.

`results/scanner5-contract-audit.json` records all 99 guarded cases and
their symbolic contexts. `results/scanner5-failure-grammar-map.json` maps
the 50 paths to every relevant semantic grammar ancestor. For the first
decrement witness, the trailing chain is:

```text
original AST 206 -> AX root 76 -> W86 -> W98 -> W23 -> atom e -> CD(1)
```

Here W86 is `eijkKCeijkfgqkjGll`, W98 is `eijkKCeijkfg`, and W23 is
`eijk`. The original caller supplies one left edge and the expanded AX
root supplies the remaining five. Therefore optimizing only another known
six-zero word does not remove this obstruction. The map was used to target
reassociation experiments in the companion grammar research.

## Finite state-elimination searches

These searches use the supplied **8,385 interval-admitted finite fixtures**,
which differ from the 8,391 all-values symbolic cases. The direct baseline
passes every fixture, with maximum 2,686 moves, and the corpus exercises all
490 baseline transition rows. Search fuel is 20,000 moves per fixture;
the represented tape coordinates are -64 through 1,983.

| Search | Scope | Result |
|---|---|---|
| One incoming action | 137 possible deleted states; replace the unique external entry by every write/direction/retained-target action | 133,712 recipes; zero survivors |
| Flexible resource endpoint | Same 133,712 recipes; allow whole-frame translation, padding at least 181, and at least 167 arbitrary spare blocks, keeping the program counter and nine primary registers | Zero survivors |
| Separate contextual entries | 467 external incoming transition rows; 455,792 possible replacement actions, changing only that row | 762 individually passing replacements |
| Joint deletion | 13 states have individually passing choices for every incoming row; search joint assignments with direct execution | Zero survivors within the stated budgets |

The 13 possible joint deletion labels are
`2,4,30,39,42,48,67,69,122,161,180,215,240`. Each receives a budget of
100,000,000 literal steps and 50,000 recursive branch calls. The domains
for 11 labels were exhausted. Label 4 reached the literal-step budget;
label 30 reached the branch-call budget. Neither of those two products
was exhaustively searched. The joint search also detects exact cycles
with no intervening tape change.

An individually passing replacement often routes through another incoming
edge to the very state being deleted; hence 762 local choices do not imply
a combined state deletion. No finite joint survivor was found. These
results are bounded search reports, **not lower bounds** on valid machines,
not universal macro proofs, and not an exhaustive search of all possible
microcode modifications.

## Files and trust boundary

- `verify.py`: fast default reproduction and optional full workflows.
- `machine/`: exact experimental table in inherited numeric labels.
- `code/symbolic_wrong_successor.py`: arbitrary-gap/spare wrong-output proof.
- `code/scanner5_contract_audit.py`: complete 8,391-case scanner audit.
- `code/map_scanner5_failures.py`: grammar-ancestry reconstruction.
- `code/*.cpp`: portable finite-search sources and shared inherited interpreter.
- `results/`: frozen detailed certificates and bounded-search summaries.
- `framework-notes.tex`: a report fragment for inclusion in the main manuscript.
- `NOTICE.txt`, `licenses/`: attribution and retained source licenses.

The inherited symbolic checker uses literal transitions, checked unary
run inductions, and checked block/list inductions. It does not replace a
proof-assistant endpoint. The default invocation checks the strong single
wrong-successor family directly; the full scanner census is frozen unless
its optional replay flag is supplied.
