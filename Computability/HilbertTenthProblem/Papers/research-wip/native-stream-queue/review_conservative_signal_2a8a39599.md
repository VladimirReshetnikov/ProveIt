# Conservative signal frontend: complete report and source review

**PASS for the stated mathematical construction, with a repaired generic
packet API.** This review covers the complete article and Morita table, the
numeric proof/ledger, all ten Python modules, provenance, and all ten original
replay commands in `Conservative_Signal_Diophantine_Frontend.zip`, arriving at
`2a8a3959980457aeb0fcf62e26860c809b5a2f42`. Its SHA256 is
`43eaf888d4d93942ab7cf311bcc2f53a1853efa0715805fb13cd14d706fa6f73`.
The delivered archive remains unchanged. There is no new fixed-arity universal
operation bound.

## Reproducible evidence

Run from the repository root:

```sh
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_conservative_signal_2a8a39599.py
```

The [checker](review_conservative_signal_2a8a39599.py) authenticates the archive,
records all 38 member hashes, extracts a private copy, executes all ten author
commands, and compares all 17 saved JSON objects exactly. It applies the pinned
[repair](conservative_signal_packet_domains.patch) only in that copy and reruns
the affected generic packet command with the same valid receipt. The default
compares the complete [saved review receipt](review_conservative_signal_2a8a39599.json);
`--write` explicitly regenerates it. An absent incoming archive can be recovered
from its pinned arrival Git object. Temporary imports restore caller-owned
module objects, including on failure.

Independent enumeration checks the complete outgoing successor set of every
one of the 49,700 modes, its reachability and BFS depth, and all 80,501 literal
event branches. This is the least **mode-only closure**. Every branch has an
explicit positive-gap realization; neither assertion says that every graph
path is realizable from one initial geometry. The 321 maximum BFS depth is
not a universal runtime bound.

The independent packet [second review](review_conservative_signal_independent.md)
and [checker](review_conservative_signal_independent.py) verify 400 complete
old/new/literal-formula packet evaluations, 25 canonical sections, 42 malformed
calls, and nested immutable snapshots. The full checker additionally verifies
200 unchanged valid packets, 33 malformed calls, all branch matrices/guards,
and the full compact ledger. It does not expand the trillion-term polynomial.

## Delivered API defects and repair

For the identity branch in dimension one, the delivered generic evaluator
returns zero for source `(1,)`, target `(1,999)`, and the valid identity witness:
it silently ignores the extra output coordinate. It also returns zero with
source `(1.0,)`, outside the declared natural-integer domain, and accepts an
extra `(None,)` slack row when there are no inequality guards. Frozen guard and
branch records retain mutable coefficient/matrix/guard lists supplied by a
caller.

The patch checks exact integer types, natural packet coordinates, complete
endpoint and witness dimensions, exact slack counts, matching guard dimensions,
and immutable copies of nested mathematical data before evaluation. Exact
signed integer vectors remain available for the branch's algebraic output
method. All correctly shaped natural residual and complementarity formulas are
unchanged. Generic overlapping branch domains remain possible; the canonical
section helper rejects ambiguity. Unique witnesses in the report use the
disjointness of its actual event domains.

The original packet SHA256 is
`94fb0aa513fc4c07860e2edab98bbb9d75fe713ed724f94e437e297a09a8666e`;
the patch SHA256 is
`c811f6e552531f614e1fcaefffc9a296d313fe80a94a3e65aa4cf033306f2033`;
the repaired packet SHA256 is
`96d4c2b634d465dfcd4df421d57d7f71da44efa201d00fa2518660e600507eef`.

## Simulation, input, and acceptance

The literal frontend has 114 meta-signals, 445 injective two-to-two collision
rules, seven speeds, and 18 simultaneously live signals. It implements the
15-state, six-symbol Morita machine with 62 quintuples through two conservative
rational stacks. The rational stack code is the eventual blank-tail code
`sum(d_i/b^i) + 1/(l*b^m)`, with `b=l+1` and digits `1,...,l`. Push and pop
preserve that code. An arbitrary rational in the containing interval need not
encode a finite tape. The number of live signals is `2l+6`, independent of input
length. The ten-live-signal binary existence result is not an instantiated
literal binary rule table in this package.

The encoded computation cannot accumulate infinitely many collisions in finite
time: controller exchanges cross the separated stack boundaries with bounded
speeds, and only boundedly many collisions occur per exchange. Only the stated
accepting pair `(q1,b)` is accepted. The nonaccepting null pair `(q2,$)` and the
other 26 undefined pairs are treated separately. The package documents the
source prose's YN/NY discrepancy and its chosen transition-table interpretation;
its table and 184-step figure replay agree.

The imported conservative-stack construction was checked against
[Durand-Lose's primary article, Sections 3–4](https://www.univ-orleans.fr/lifo/Members/Jerome.Durand-Lose/Recherche/Publications/2012_IJUC_UC_HC.pdf).
The later acceleration construction is not needed for this non-Zeno frontend.
The older two-symbol reversible-machine existence statement is supported by
the [IEICE publisher record](https://globals.ieice.org/en_transactions/transactions/10.1587/e72-e_3_223/_p).
The package's literal Morita transcription and all its executable audits were
read and replayed. The external 2008 institutional PDF was unavailable during
this review, so this review does not claim a new visual authentication of its
printed transition table. Universality still imports the cited machine theorem.

## Exact event geometry and integer lift

A post-event germ with zero adjacent gap requires strictly increasing outgoing
velocities there. Legal events select every earliest tie, use the least selected
edge as pivot, and impose strict endpoint inequalities on every unselected edge,
including undefined collisions. This excludes an earlier forbidden collision,
missing simultaneous collisions, and a triple collision falsely resolved as a
single pair. Each literal two-to-two event preserves the sorted position
multiset at the event time.

For relative-speed vector `c` and pivot `j`, the gap lift is exactly
`N = c_j I - c e_j^T`, with rank 16 and `N^2=c_j N`. Its 17-gap block has at most
32 nonzero entries of absolute value at most 24. These are **gap-block bounds**;
they do not bound the much larger mode-code row. The cumulative scale obeys
`lambda' = c_j lambda`, so it needs no additional integer coordinate. The
eighteenth coordinate is `u=q*sum(h)`. Active endpoint velocities coincide, so
`sum(c)=0` and the output-mode row has coefficient `c_j*q_new` in every gap
column. The checker verifies this on every active branch.

On encoded cuts the span is 16: decoding uses `g=16h/sum(h)` and event delay
`16h_j/(sum(h)*c_j)`. All 18 particles cannot collapse into a legal pairwise
event, so the positive-span condition is preserved. Optional elapsed time adds
one coordinate via `p'=c_j*p+h_j`. The graph's 1,728 sinks include 36 collision-free
modes and 1,692 modes blocked by forbidden collisions; sink status alone is not
acceptance. The accepting target is a separately designated mode.

## Quadratic packet and audited ledger

The one-step polynomial sums affine residual squares and terms
`b_other_sum * sum(active_copy_coordinates)` for each branch. Here
`b_other_sum` means the sum of all *other* selector variables. It is globally
nonnegative on natural assignments. At a zero, the selector-sum equation forces
one active branch, inactive copies and their homogeneous slacks vanish, and the
active copy and its canonical guard slacks certify precisely the chosen step.
Disjoint event domains then give the unique section.

With dimension `d`, branch count `B`, and equality/strict/weak guard counts
`E,T,W`, the auxiliary count is `B(d+1)+T+W`; the affine-square count is
`1+2d+E+T+W`. The literal instance has:

| Quantity | Exact value |
|---|---:|
| Modes / branches | 49,700 / 80,501 |
| Equality / strict guards | 95,445 / 2,667,479 |
| Auxiliary / total variables | 4,196,998 / 4,197,034 |
| Affine squares / complementarity products | 2,762,961 / 80,501 |
| Affine variable incidences | 15,323,489 |
| Expanded nonzero monomials | 1,059,563,096,023 |
| Maximum affine / expanded coefficient bit length | 124 / 248 |

Every ledger entry above is derived independently from the authenticated finite
closure. The expansion count partitions disjoint monomial families. Its dense
gap pairs cannot cancel because the minimum positive output-mode weight is
`1406268092635393017921167382337534476`, whose square exceeds the signed small-gap
correction bound `17*24^2+1=9793`. Each summed strict form has positive coefficient
in every gap coordinate, with minimum 2, preventing cancellation in the
own-selector/gap family. The maximum coefficient is bounded for every family
and attained by an actual coefficient query in branch 79,695. This is an exact
compact expansion count, not a materialized expansion or an optimized gate
count. The additional [ledger receipt](review_conservative_signal_independent_ledger.json)
records the second review's numerical checks; the maintained full replay now
reproduces those dominance checks too.

## Consequences for the universal-equation search

For an externally supplied positive horizon `K`, composing steps requires
`4,197,016*K - 18` natural witnesses when endpoints are parameters. The report
does not replace that external horizon by a fixed ordinary integer tuple.
Prepared rational tape data require input-dependent arithmetic and bit length;
an ordinary binary input loader is not included in a fixed-size operation
ledger. Fixed integer point-to-point reachability has a decidable scale bound
from `sum(h') >= 3*sum(h)`, while the accepting cone permits unbounded span.
These are distinct relations.

The useful result is a complete, literal, order-free finite event frontend with
small gap matrices and a fully counted quadratic step certificate. Its large
mode closure, growing horizon, and missing fixed-arity history decoder remain
explicit costs. The universal 87-operation benchmark is unchanged.
