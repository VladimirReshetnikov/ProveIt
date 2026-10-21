# Independent review of the four marker machines

Reviewed against ProveIt commit `b6fb232916d008383e7cf2990d68ddb30fded7db`,
whose accepted native K215 bytes have SHA-256
`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.

## Finding

The ordinary all-tape simulation argument in `engine_work/MARKER_PROOF.md`
is sound for all four supplied variants. I found no hidden source-runtime,
spare-list, blank-only, or tape-exterior assumption. This conclusion is about
the exact finite premises and the ordinary induction; it is not a new Lean
or Rocq kernel theorem.

The review read the proof and builder in full, then used `audit.py`, written
independently and importing none of the builder/checker code, to parse the
literal tables and check the following.

* Every table is total on exactly 215 working states and two symbols, with
  the separate halt and start conventions as stated.
* All incoming rows of each merged old role are enumerated from the entire
  old table. The unconditional predecessor-marker premises for 124, 127,
  160, 190, and 52 hold literally.
* The only exceptional incoming path for old 176 is fully accounted for:
  old 189/read1 writes 1 and moves left into156; old 156/read1 writes 1 and
  moves right into176. Thus that route necessarily leaves the current
  symbol 1, and cannot reach the exceptional read 0 branch of old 176. The
  start is neither 156 nor any merged role.
* For every one of the 430 old rows, the new table simulates it in one or
  three transitions with exactly the same complete local tape, head, and
  mapped target. The checker allows both predecessor values on all common
  branches. Exceptional branches use only the marker justified above.
  Every read in a local simulation is of one of the two declared cells;
  hence arbitrary values elsewhere on an infinite tape are untouched.
* The dense table is exactly isomorphic to its native table. Each new graph
  differs from all 84 distinct rooted graphs represented by 321 parseable
  215-state tables in the pinned Research/ZFC corpus, including their global
  tape reflections. This is a bounded corpus comparison, not a historical
  novelty or behavioral-inequivalence claim.

There are 858 local two-cell cases for each single-selector variant,856 for
M124+M160, and 854 for the triple composition. These include 2, 4, and 6
exceptional three-step cases respectively. The independent receipt is
`actual.json`.

## Why composition does not invalidate the invariant

The predecessor claims concern the old machine at simulation boundaries.
They need not hold at every internal new-machine visit to a provider state.
Each three-step block is checked in the fully composed new table, and its
endpoint is the composed state map applied to the old endpoint. Thus an
internal provider visit is never mistaken for a new boundary. In particular,
M160 can end at old role 52 while M052 is also active: the final step writes 1
immediately left of the new boundary, exactly matching old190/read1. The next
M052 exceptional block therefore has its required marker.

For ordinary rows the proof uses the target map as well as the current-state
map. For the nonexceptional branch of a merged pair the retained common row
is checked explicitly. This covers the rows excluded from the builder's
ordinary-row loop and is also checked by the independent reader.

## Both directions of halting equivalence

For any initial binary tape and any integer head location, start both
machines in state 0. Induct on old transitions until halting. At old time n,
the new machine reaches a corresponding configuration after t(n) transitions,
with equal head and tape and mapped control. Each increment of t is either 1
or 3. Every intermediate state in a three-step block is a working state.

Old halting therefore gives new halting. Conversely, if the old run were
infinite, the synchronized new configurations would exist at all the
unbounded times t(n), because t(n)>=n. The new machine could not halt at a
finite earlier time and still have those later configurations. It also cannot
halt inside a simulated block. Thus new halting gives old halting. No
fairness, amortization, or nonhalting oracle is used.

The accepted exact-K215 theorem then transfers directly to these literal
machines. A fresh numerical-calculus or unbounded register-runtime proof is
unnecessary for this route: the theorem is a complete binary-machine
simulation from the original start. The original source file is explanatory
provenance and is not an extra unchecked premise of this simulation.

## Own-reader execution history

The first reader attempt had a Python whitespace typo (`else1`) and stopped
at parsing; `audit-attempt1.py` preserves it. After that correction, the reader
stopped because it initially treated the newly added `novelty_corpus`
directory as a machine directory. The final reader selects directories
containing `machine.native.tm`, still requiring a recognized specification
for every selected table. It then passed. Neither correction changed a
machine, a marker premise, or a local simulation contract. The failed
attempts are not represented as successful executions.
