# Further simplification: contract 1,059 drain loops

## Leading result

The 1,426-vertex canonical test graph has **1,059 exact drain loops**. Each is a
single register-decrement test whose nonzero edge returns to itself, adds a fixed
nonnegative vector to OTHER registers, and whose zero edge exits with a fixed
increment vector. The tested register is never incremented on the self-loop.

Proving this loop pattern once permits its replacement by a total affine
register update. Contracting all such loops leaves:

- 367 vertices: 366 genuine branch tests and one halt;
- 732 labelled edges;
- only 33 distinct affine update matrices;
- largest matrix coefficient4;
- at most six drain macros on any contracted edge;
- 24 distinct local drain shapes among the1,059 occurrences.

The compact graph and shared matrix dictionary occupy the exact byte count in
`DRAIN_AUDIT.json`. This is a smaller auxiliary proof graph, **not a smaller
Turing machine**. The certified machine still has215 working states.

All structural recognitions, matrix products, rank obligations and shared-matrix
round trips were checked by new independent Python code. Additionally5,295
concrete local runs were checked against the affine updates. The finite tests
are only regression checks; the generic arithmetic proof below is what would
establish validity for arbitrary register values. There is no newly compiled
Lean/Rocq theorem and no measured build-time speedup.

## Alignment with recent commits

The commit-review worker identified current main as
`53269bcab1efc0f82d3022645bd7cf0c22d84959`.
I independently compared the entire `t215` and `tD` tree literals from its
`KSource215Data.lean` against the earlier pinned formal source at
`c9dc79323429112c698100f3226a6e4d56c8b782`: they are exactly equal.
`CURRENT_ALIGNMENT.json` records this check and the current materialized file's
SHA-256. The graph input is therefore aligned with those current tree literals;
this report does not infer that all current dependency files are unchanged.

## Generic drain theorem

At vertex v testing register r, suppose its nonzero edge is `(v,c)` and its zero
edge is `(w,d)`, with c[r]=0 and w≠v. Here c,d are nonnegative increment vectors;
the ordinary graph transition decrements r BEFORE adding c on the nonzero edge.

For every natural-valued initial register file R, put n=R[r]. After exactly n
nonzero iterations, register r is0 and each other register j equals
R[j]+n·c[j]. The zero edge then exits at w and adds d. Thus the resulting register
file F(R) is:

- F(R)[r] = d[r];
- F(R)[j] = R[j] + R[r]·c[j] + d[j], for j≠r.

Prove this by induction on n. For n=0 the zero edge is taken immediately. For
n+1, the first nonzero edge lowers the tested register by exactly1 because
c[r]=0, and adds c to all others; apply the induction hypothesis. The exit
constants d are applied once, including a possible nonzero d[r].

Exactly n+1 original graph steps are consumed, so every macro terminates and
makes positive progress. This is valid for arbitrary natural register files,
not only a finite set of tested values, a bound on n, or the blank-start state.
No register invariant beyond the syntactic shape c[r]=0 is needed.

In the code, F is represented by a10×10 homogeneous matrix acting on the column
vector `(R0,...,R8,1)`. It has nonnegative integer entries. The tested row is
zero except for its constant d[r]; other rows have their identity term, c[j]
in column r, and d[j] in the constant column. The last row preserves1.

## Compose the macros without hiding divergence

A core vertex is a non-drain test or halt. For each outgoing edge of a core
vertex, begin with its increment vector, follow the zero-exit destination of
each recognized drain, and compose the corresponding matrices. Stop at the next
core vertex. The nonzero decrement at the original core vertex remains explicit
and precedes this matrix; it must not be forgotten or folded into an unsigned
matrix incorrectly.

`drain_ranks.json` supplies a natural rank for every eliminated vertex. Each
drain-to-drain exit strictly decreases rank, and the maximum rank is6. These
inequalities were checked for all1,059 eliminated vertices. They certify that
no infinite chain of total drain macros is silently contracted into an edge.
All1,059 drain vertices occur in the generated core-edge paths. Halt vertices
are never eliminated or given outgoing edges.

For any entry into a drain (including an initial state at a drain), the same
finite ranked composition gives its core state and register update. Here the
original initial vertex0 is already a core vertex, so the entry matrix is the
identity.

The resulting generic contraction theorem states that the original graph halts
iff the affine core graph halts, preserving the final register file if desired.
One direction expands every affine edge into its finite drain runs. The other
contracts them using the total drain theorem and strict rank decrease. Every
core step still contains its original decrement-test transition, so positive
progress remains explicit. This composes with the preceding canonical graph
adequacy theorem and preserves the original machine/ZFC endpoint.

## Small checker interface

The proof-producing transformation need not trust an optimizer or a Python
matrix calculation. A kernel-checkable certificate/checker can verify:

1. Every removed node has the exact self-loop/drain shape and c[r]=0.
2. Every exit is either a retained core vertex or has a strictly smaller rank.
3. Every core edge's certified path follows the literal graph edges.
4. Its affine matrix is the exact product of the local drain matrices and the
   incoming edge's increment matrix, in the correct order.
5. Entry data, retained branch registers/polarities and halt markers match.

The matrix dictionary can be computed or supplied as untrusted data and checked.
Equality must be full coefficient equality, not equality of a hash. The local
rule needs one arithmetic proof; all1,059 instances then discharge by finite
shape checks. No1,059 new loop inductions are necessary.

This is useful beyond shrinking a presentation: future variants whose sources
implement the same transfer/copy/clear macros using different numbers of tests
can compare their affine cores instead of requiring identical low-level test
ordinals. A separate correspondence is still needed if the core order differs.
The present data does not prove equivalence to any unexamined alternative.

## Negative results that guide priorities

### Strong labelled graph minimization

Full deterministic labelled-bisimulation refinement reduces1,426 vertices to
only1,423. The three nontrivial equivalence classes are:

- {4583,4666};
- {4585,4668};
- {4721,4748}.

All1,426 vertices are reachable if zero/nonzero guards are treated as choices.
Thus an ordinary graph reachability sweep or exact labelled quotient does not
provide a large further reduction. `QUOTIENT_AUDIT.json` records the full result
and an independent homomorphism check. This is a coarsest quotient for the stated
labels, not a lower bound on semantic minimization under register relations.

### Simple interval invariants

A conservative interval analysis beginning with ALL nine registers arbitrary
finds only two tests forced to their zero branch: ordinal4671 tests register1,
and ordinal4733 tests register6. A separate complete edge-closure check verifies
that the resulting interval assignment is inductive. The first node is already
a drain; the second is a core node. The tiny extra gain does not justify making
these invariants a dependency of the leading drain-contraction proposal.

This negative result is specific to the finite interval domain used. It is not
proof that stronger relational invariants cannot simplify additional tests.

## Verification detail and limitations

`contract_drains.py` validates each output edge matrix two different ways:
ordinary matrix multiplication, and direct symbolic affine-coordinate updates
for every drain in its path. It also checks all local concrete regressions,
rank decreases, complete drain coverage and compact-graph expansion. Matrices
have only small coefficients, so arbitrary-precision Python integers suffice
without overflow assumptions.

The original graph input comes from the independently checked full formal-tree
canonicalization of the prior report, including the corrected wrap semantics of
`incRev`. Its exact SHA-256 is
`1bb3dbf084ef69d4c0464381afd200bb8ac3330d521890697344c6c8e0bbf0c3`.
All current tree-literal equality checks passed, as noted above.

A proof assistant must still check the source-to-graph compiler, the generic
drain theorem, the contraction checker, and the resulting concrete checks.
Reducing the retained graph does not eliminate the need to inspect the removed
nodes' shapes. The useful claim is a substantially smaller, reusable proof
interface, not that75% of compiler time has been saved. No original transition
table, source program, endpoint statement or remote repository was changed.

## Reproduction

Run with Python3 standard library:

    python minimize_graph.py
    python interval_invariants.py
    python contract_drains.py

These are newly written owned scripts. They do not import or execute downloaded
repository scripts. All input/output data and concise audits accompany them.

## Independent adversarial review

`validate_drains.py` is a second owned checker, which reads emitted artifacts
without importing or executing the generator. It independently reconstructs
edge transformations by symbolic coordinate substitution, checks every removed
node's literal graph binding and strictly decreasing rank, and checks the full
retained-node partition, labels, targets, entry and matrix coefficients. Its
explicit `nonzero_update` contract is `decrement_before_affine`.

All nine adversarial mutations were rejected:

- adding an increment of the tested register to a drain self-loop;
- making a drain exit rank nondecreasing;
- changing the core semantics to omit the nonzero decrement;
- changing the entry transform;
- reversing a genuinely noncommuting edge's affine composition order;
- duplicate tested-register increment entries that try to hide a self increment;
- a negative increment coefficient;
- an out-of-range increment register;
- an out-of-range retained test register.

In addition, 1,098 complete core-edge concrete regressions execute the original
graph through all intervening drain iterations and compare its output with the
core transition, including the retained decrement. These supplement the earlier
5,295 local drain regressions, not replace the universal mathematical proof.
An explicit missed-decrement counterexample occurs already at vertex 0: with
R8=1 and all other registers 2, the correct next core is vertex 9 with R8=0;
omitting the decrement incorrectly leaves R8=1. Both alternatives choose the
same graph target, so checking targets alone would miss this bug.
`ADVERSARIAL_AUDIT.json` records the full outcomes and counterexample.

### All-register halting proof obligations, precisely

Let a core configuration be `(v,R)`, with v retained and R an arbitrary vector
of naturals. On a nonzero branch at register r, define Q by Q[r]=R[r]-1 and
Q[j]=R[j] otherwise. On the zero branch Q=R. If the branch has increment vector
a and drain path d1,...,dk, the core successor is

    (target, F_dk(...F_d1(Q+a)...)).

For column-vector matrices the edge matrix is therefore
`M_dk * ... * M_d1 * Add_a`, applied to Q, NOT to R on the nonzero branch.
The homogeneous coordinate remains 1. Natural subtraction is used only after
establishing R[r]>0. There is no negative matrix coefficient and no implicit
assumption that arbitrary natural register values are small.

The local drain induction gives exactly n+1 concrete graph steps with identical
exit registers, for each n=R[r]. Since its body never halts and its nonzero edge
returns to the same vertex, that exit is unique and no halt can occur inside a
drain. The rank induction then proves that every entry into removed nodes has
a finite, uniquely determined exit to a retained node. Rank decreases between
drain macros, not between individual iterations of one drain. The latter are
justified separately by the decreasing natural tested register. A drain whose
zero edge increments its own register is still sound: that increment is applied
only at the final exit, and the exit cannot re-enter the same or a higher-ranked
drain. No unproved global invariant is needed.

For forward halting preservation, expand each finite core transition into its
one retained test step followed by the finite ranked drain runs. For reverse
preservation, take a finite original run to halt. Starting at a retained node,
either it is already halt (zero steps), or determinism fixes the first test
step and the ensuing finite drain chain. That chain cannot contain halt; hence
the run must reach its next retained configuration before its final halt.
Remove this nonempty prefix and induct on the remaining original run length.
This proves both implications, including exact final registers. If an arbitrary
initial vertex were removed, first apply the finite entry normalization. For
this concrete graph the actual entry is retained vertex 0 with identity matrix,
so there is no hidden initial decrement or initialization assumption.

These are proof obligations for a future generic Lean/Rocq implementation.
The Python checks validate finite premises and regressions, not this theorem.

### Priority against the recent compiled normalization lane

Recent incoming artifacts contain a normalized 1,426-entry source-equivalence
lane and recorded kernel receipts, as well as an ordinary zero-offset lane.
This report does not claim to have recompiled those artifacts. More importantly,
for the presently identical canonical source graphs, affine contraction is not
needed to establish equality: checking the two full 1,426-node graphs directly
is likely the simpler proof architecture. Contraction requires extra shape,
rank and arithmetic checks and could increase total verification work.

Its practical benefit is a reusable semantic macro interface: future candidates
can differ in transfer/clear-loop implementation while sharing a much smaller
affine core. It also offers a compact human-auditable representation. A smaller
retained graph does NOT itself imply fewer formal obligations, faster builds,
or a better proof for the current identical pair. Prioritize direct normalized
or canonical equality for that pair; add drain contraction when it removes a
real low-level mismatch or supports another downstream analysis.

### Input and assertion hardening

All four owned entrypoints now reject optimized Python execution explicitly via
a `__debug__` guard before performing any checks or writing results. All four
normal runs passed again, and all four `python -O` runs failed with the intended
guard message; see `OPTIMIZATION_GUARD_AUDIT.json`.

The independent validator checks the complete graph's test-register ranges,
including retained nodes, and nonnegative natural increment coefficients with
valid register indices. It sums duplicate increment entries, so a final zero
entry cannot hide an earlier positive tested-register increment. The generator
uses a stricter canonical-input contract and rejects duplicate increment keys
altogether before recognizing drain shapes. No malformed-input tolerance is
assumed in the generic theorem.
