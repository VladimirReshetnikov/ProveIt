# Independent audit of the accepted K225 baseline

The independently rerun `portable/reproduce.py --full` passed. It checked 274
sealed input files, reconstructed the table and source, rechecked the source
graph and exact startup, and freshly derived all 6,656 K225 runtime cases.
The case digest is `1937bfce292c6ffaa3e8a28c44df4a1fc0a59e6de7a2cb2f955b961a051fcaac`.
There are 450 rows and 1,608,136 symbolic rule applications. Every instruction
case has strictly positive concrete duration; the smallest constant term is 13.
The exact startup takes 409,835 transitions and reaches the full calibrated
351-one-cell seed, including 167 nonempty spare blocks.

The newly rerun evidence is in `baseline225_replay/replay.json` and its runtime
and audit files. This replay does not rebuild K230 in Rocq.

## Proof status and the local fold

The literal K230 calibration is the inherited external Rocq theorem connecting
blank halting with a finite refutation of the syntactic first-order theory
`StandardZFC`. Its recorded final theorems have no additional assumptions.
The accepted K225 package supplies an ordinary mathematical proof of transport,
with executable finite and inductive certificates. It does not supply a new
K225 Rocq theorem, an internal PA proof-code endpoint, or a serialized ZFC
derivation. These levels should remain distinguished in any new report.

In normalized K labels, the final local K225 fold identifies 229 with 152 after
four source reassociations. The old 229 role has immediate-left bit zero; the
old 152 role has immediate-left bit one. The latter fact must include the
left-moving call from state 76. Counting only right-moving callers would leave
a gap. The invariant in the accepted packet includes this call and is rechecked
row by row. All 452 old rows are covered: 448 commute in one transition, and
four exceptional rows use three literal transitions. The exceptional steps
read and rewrite only the old head cell and its immediate left neighbor; all
exterior cells remain arbitrary and untouched.

The local theorem starts from the rotated 226-state basis on every binary tape.
It does not identify arbitrary-tape behavior before and after source rotations.
Connecting the rotated basis to the accepted K226 source requires the separate
complete source graph, per-instruction runtime, and exact blank startup chain.

## Runtime checker review

No soundness gap was found in the reviewed generic engine. Affine run lengths
have nonnegative coefficients; a non-self-loop literal step requires a positive
constant term, so it cannot inspect a cell that disappears when a symbolic
counter is zero. Self-loop run traversal is justified by induction on its length.
The four opaque spare-list traversals are derived on the exact input table using
arbitrary contexts and a symbolic one-block value, then extended by finite-list
induction. No unknown exterior context is inspected in those derivations.

Whole relative tape equality, final displacement, control state, and source
successor are checked at each nonhalting endpoint. The spare list is nonempty,
containing an arbitrary first value and an arbitrary finite remaining tail.
The runtime adapter independently checks that source-word normalization removes
only zero suffixes, so consecutive instruction theorems apply to the same
physical frame. It also checks the nine-register permutation and positive time.
The proof-construction fuel bounds symbolic derivation search, not counter
values, tail lengths, or the machine's execution time.

## Generic kernel-checked progress theorem

`PositiveTransport.v` proves the reusable deterministic-machine statement:
if related halting states map to halting states and every old transition maps
to a positive finite new block ending in a related state, then halting and
nonhalting agree at related starts. The reverse direction consumes the new
machine's finite halting budget along each positive block. It therefore handles
the progress issue explicitly instead of assuming that one simulation direction
automatically gives an equivalence.

This standalone theorem compiles with Rocq 9.1.0, prints two closed assumption
reports, and passes independent `coqchk` with no axioms or unsafe declarations.
`check_positive_transport.py` reproduces those checks. No exact transition-table
certificate is instantiated in this generic file; it must not be described as
a formal K225 consistency theorem.

## Rejected scanner contraction

Removing normalized scanner phase 50 and redirecting its incoming targets to
75 gives a syntactic 224-state table but fails the universal instruction
contract. K225 has 48 source leaves containing a six-zero run; all 48 end with
six zeros, and they comprise 47 decrement leaves and one increment leaf.
All 95 corresponding guarded cases fail the shortened scanner.

At source index 40, `11101001001000000`, decrement register 1 on its zero branch,
the first reset scan sees six zeros at positions 11 through 16 and continues
normally. Before a second reset scan, a zero has also been written at position
17, creating seven consecutive zeros. The eight-zero scanner correctly sees
the preceding one; the seven-zero scanner mistakes the temporary run for the
exterior blank region. With all registers zero and first spare zero, the
unmodified machine redispatches correctly after 586 transitions; the contracted
machine redispatches incorrectly after 662. This is a counterexample to the
claimed instruction contract, not a claim about the entire blank-start run.

The rejected table and case diagnostics remain explicitly marked as failed
discovery artifacts. They must not be promoted to a consistency candidate.

## Search scope

The local finite searches are discovery tools. Their bounds constrain window
width and macro search, and a negative result establishes no state-count lower
bound. Every hit still needs a complete source correspondence, unbounded runtime
proof, and exact blank startup, or a sound complete local simulation certificate.

`runtime_windows.py` computes an inductive finite-window projection beginning
at all valid source dispatcher prefixes, with arbitrary newly exposed boundary
bits. Its closure is a rigorous overapproximation of all source-frame runs,
rather than a sample of bounded executions. Any proposed mutation using this
stronger invariant must separately prove its actual blank startup.
