# Independent machine audit for the 223-state construction

## Frozen inputs and result

The frozen inherited-K-labelled table is `candidate.k.tm`, with SHA-256
`7e036b1bd05fe8a7e5877a8c5386cae603f4d689adeeb13754ee98dca998bfef`.
Its source instruction list has SHA-256
`df55079f114a6aa9ada970d7d857726e47e3a3dba2a721245ebbacfd4577c13c`.

The independent replay passed every one of the **6,449 guarded instruction
cases** on the literal table. It used every one of its **446 transition rows**.
The proof derivations total **1,566,562 symbolic rule applications**; their
largest case uses **400** symbolic applications. Every concrete instruction
block has duration at least **13** machine steps.

These results concern a machine with **223 working states**, two tape symbols,
a two-way infinite tape, and a separate halt label. All transitions write a
bit and move left or right. The inherited table starts in K-label 0 and halts
at label 254. Consecutive canonical labels are working states 0 through 222,
with initial state 0 and separate halt state 223.

The canonical table is `candidate223.tm`, with SHA-256
`c89d3f79ab12a3857092bb4b3d30bfc594079edc0f696b066ce4c386fd00f1b2`.
The supplied canonical map is checked as a bijection on all 224 labels,
including halt. The independent checker conjugates all 446 transition rows,
checks the initial and halt labels, and independently verifies breadth-first
numbering, exploring the read-0 edge before the read-1 edge. This also shows
that all 223 working states are reachable in the directed transition graph.
Graph reachability does not claim that each state is reached in the actual
blank run.

## What the runtime proof quantifies over

This is an executable ordinary mathematical induction proof using the
unchanged, hash-pinned K224 symbolic engine. The compiler and its decoder-map
routines are not imported by the checker. The generated machine and source
are read as data.

For each source instruction, the starting frame contains nine independent
natural register values, an arbitrary natural extra gap after the program
address, an arbitrary natural first spare value, and an arbitrary finite
remaining spare list. All tape cells outside the complete frame are blank.
Each decrement instruction is checked in two exhaustive cases: its argument
register is zero, or it is one plus an independent natural value.

The symbolic representation has thirteen affine slots: the constant term,
extra gap, nine registers, first spare value, and total width of the remaining
spare list. The latter width denotes the actual width of the arbitrary finite
list; the proof does not require the list length or its elements to be bounded.

The retained engine permits three kinds of computation rule:

1. A literal transition executes the supplied table row.
2. A unary-run rule is applicable only when that exact row is a self-loop in
   the scan direction. Induction on the arbitrary natural run length proves
   the summarized action, including length zero when allowed by the symbolic
   representation.
3. A list traversal uses an independently rederived one-block schema. The four
   schemas are checked again on the new table, with one arbitrary natural
   block value and opaque exterior contexts. Their one-block duration is
   exactly `v + 2`. The empty-list identity and structural induction extend
   the one-block result to every finite list. No opaque exterior is read in a
   schema proof.

The elementary word identities used to normalize list representations are
also checked by the retained proof engine. Writing
`B(v) = 0 1^(v+1)` and `C(v) = 1 0 1^v`, they express
`C(A) 1 = 1 B(A)` and its reversal for an arbitrary finite list `A`.
These identities justify the changed delimiter position after a list scan.

For a nonhalting instruction, equality of the final normalized symbolic state
requires the correct dispatcher state, head orientation, entire left and right
tape contents, and expected updated address/register frame. It is not merely
equality of decoded register values. The calculated head motion is also
checked against the expected address-overflow displacement. A premature halt
cannot satisfy a nonhalting instruction's target and causes proof failure.
For a halt instruction, the proof reaches the literal halt label in positive
finite time.

The 4,000-rule fuel in the proof engine is a limit on the search for a symbolic
derivation. It is not a bound on register values, gap size, list length, or
concrete execution time. An unsuccessful derivation is reported as failure.
The successful derivations have nonnegative affine duration coefficients and
a constant term at least 13, so an infinite sequence of source instructions
cannot be simulated in finitely many machine steps.

## Source interface and startup

The independent source parser checks 4,962 instruction occurrences forming a
complete binary prefix tree. It checks each opcode and argument, enumerates
all 6,449 guarded cases, resolves every successor address, and rejects stray
nonzero address suffixes. The source has maximum depth 37, maximum zero run 6,
and exactly 209 distinct subtrees, counting instruction leaves. Its independently
resolved control-graph hash is
`542a342bce37c53d297e80cd52223ff8513b39a59dce965d251702a44972f2da`.

These prefix checks establish that the runtime proof covers every instruction
occurrence and every decrement guard of the supplied source, with a defined
next source instruction. The runtime proof then verifies the exact literal
machine's action at every such source address. Together they check the
source-to-machine interface, including inherited decoder aliases and any new
entry contexts introduced by source reassembly. A compiler's internal alias
classification is not assumed as a substitute for this replay.

From the all-zero tape, initial K-state 0, and head position 0, direct execution
for exactly **409,835** steps reaches K-state 84 with head position -5. The
complete finite support equals the independently reconstructed baseline frame:
351 one-cells, logical registers `[3,0,0,0,3,0,0,0,0]`, the inherited physical
register permutation, extra gap 117, and 167 spare registers of value 1.
Every other tape cell is zero. The receipt retains the entire support, not a
bounded neighborhood or tape checksum alone.

## Delta from the 224-state table

The new table deletes inherited K-state 227. It changes 36 retained transition
rows and preserves 410 retained rows. All 98 rows belonging to the following
49 engine states are unchanged:

`0,1,2,3,4,5,6,9,10,14,15,16,17,21,22,23,24,25,32,33,34,35,36,39,40,41,45,48,49,50,51,54,55,56,60,61,64,66,74,75,82,94,97,113,137,144,156,161,198`.

The full row delta is in `machine_delta223.json`. Preservation of these rows is
useful provenance; correctness does not rest on that observation alone. The
universal runtime rules, list schemas, instruction cases, and exact startup
are freshly replayed on the new literal table.

## Mathematical scope and proof-assistant boundary

Subject to the source-program semantics and the theory/enumerator calibration
proved elsewhere in this contribution, the runtime and startup results yield
halting equivalence between the literal 223-state table on blank tape and the
specified source search. The source graph has defined successors, each source
step has a positive finite machine simulation, and halt instructions have the
required literal halting behavior. These ordinary finite and inductive
arguments can be formalized in ZFC.

This audit does not itself prove the new axiom presentation equiconsistent
with ZFC, nor reconstruct the formula emitter's mathematical meaning. Those
are separate obligations. It does not claim a newly compiled end-to-end Rocq
or Lean theorem for this exact 223-state table. The ordinary proof uses the
same explicitly checked natural-number and finite-list induction principles
as its predecessor. Soundness is conditional on the ordinary mathematical
correctness of those principles and the small retained symbolic proof engine;
there is no additional consistency assumption hidden in the machine audit.

## Reproduction

Extract the unchanged K224 predecessor ZIP. Pass its `portable/machine`
directory to the portable checker, which verifies the dependency hashes before
importing anything:

```sh
python3 -B check223.py \
  --baseline-machine-dir PATH/TO/K224/portable/machine \
  --table candidate.k.tm \
  --sites sites.json \
  --canonical-table candidate223.tm \
  --canonical-map canonical_map.json \
  --output fresh-audit
```

`audit.json` contains the complete startup support, induction-schema traces,
source metrics, canonical conjugacy check, dependency and input hashes, row
coverage, and result. `cases.json` contains one ordered record for every
source/guard case, including its affine duration and head motion. The latter
is a derivation summary; a full invocation rederives every instruction proof
from the literal table instead of trusting stored records.

The optional `--skip-runtime` performs source, canonical-map, and startup
checks only and explicitly returns a different status. It must not be described
as a fresh universal runtime replay. Assertions must remain enabled. Failures
write a `FAILED` receipt and return a nonzero process exit code.

## Scope of the unsuccessful fixed-table explorations

Before the source/theory reduction was available, several specific local
optimization families were searched on the 224-state table. None yielded an
accepted smaller table:

- Predecessor-bit selector folds with a two-cell excursion through existing
  helper states, rejecting circular dependence on a state being deleted.
- Same-head state elimination and replacement of a state's two rows by
  existing bounded helper blocks. Reachable tape windows of radii 3, 4, and 5
  were computed by finite abstract interpretation, starting with every binary
  local window at initial state 0. The radius-4 fixed point contains 27,929
  state/window pairs.
- Bounded local bypasses of the incoming rows of one state; local multistep
  matching; and equivalence-preserving row rewrites followed by selector-fold
  discovery. These searches had finite path and neighborhood limits and made
  conservative exclusions on recursive use of modified rows.
- A two-cell head-offset quotient: when every external predecessor enters a
  state in direction `d`, delete it and reverse incoming moves so its mapped
  configurations have head offset `-2d`. Positive replacement blocks of at
  most 40 steps were checked within the available radius-4 windows.
- Shared-branch folds retaining an unchanged common branch, including its use
  inside replacement blocks. The tighter runtime-window search examined 278
  candidate state-pair/common-branch combinations, with bounded local blocks.

A separate instrumentation of all 6,238 predecessor instruction cases
collected tighter radius-4 tape windows. It included unary-loop interiors,
processed-list prefixes, the one-block schema interiors with opaque contexts,
and the complete blank initialization. It produced 14,613 state/window pairs;
the intersection with the all-tape abstraction contains 14,101. Repeating the
specified local searches with these stronger invariants did not find a
reduction. Full-tape finite samples were also used as a discovery heuristic;
no surviving candidate from that search passed the required checks.

These are scoped negative computational findings, not a lower bound of 224,
223, or any other state count. They are not ingredients of the positive K223
proof. The successful reduction instead changes the axiom/source presentation
and shares its repeated closed instruction sequences more effectively.
