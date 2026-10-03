# Independent five-gate clean-clock folding audit

**Verdict: PASS.** This audit covers the final eight five-gate native/phase4
candidates, not the superseded six-gate phase4 proposal. Each complete folded
output is the identical integer polynomial to its own frozen original for every
assignment of all coordinates. The saving is one addition for native/spatial
blocking, and one addition plus one multiplication for phase4.

The frozen original manifest is pinned by SHA256:

`1bf1225aa950ad1d4f842c8bf098e1935925cd1d52c90453b7696c1321648f95`.

All 44 files listed in that live frozen manifest were independently checked for
both byte length and SHA256 before and after the audit. The base was not modified.
Eight copied original circuit JSONs are authenticated against that manifest, so
normal replay is self-contained and does not require the live frozen sibling.

## Independently recounted complete circuits

These counts include the entire inherited arithmetic core, five clean-clock
bridge operations, and all 59 operations of the twenty-comparison SOS finalizer.
Native and phase4 have the same new counts, but remain different clock models.

| Fixture | Native total | Phase4 total | M | A | Strictly positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| INC2;DEC2 | 603 | 603 | 239 | 364 | 60 | 2344 |
| ZERO3 | 478 | 478 | 184 | 294 | 58 | 1192 |
| NOP | 476 | 476 | 182 | 294 | 58 | 1192 |
| POSITIVE3 | 479 | 479 | 189 | 290 | 58 | 1192 |

Here A counts both addition and subtraction. Integer constants are literal
operands; multiplication by a literal remains a paid multiplication. Nothing is
hidden as a precomputed coordinate or external operation. The eight full DAGs
contain 4,072 counted arithmetic gates, twelve fewer than their eight originals.
No optimality claim is made.

## All-tuple complete polynomial identity

Write F for `final_positive` and theta for `theta_positive`. The frozen native
clock is

    C_native = 2 theta + 192(F + x + 1) + 16
             = 192(F + x) + 2 theta + 208.

The frozen phase4 clock is

    C_phase4 = 4[2 theta + 192(F + x + 1) + 16]
             = 768(F + x) + 8 theta + 832.

Each right-hand expression is implemented with exactly five gates:

1. Add F and x
2. Multiply that sum by 192 (native) or 768 (phase4)
3. Multiply theta by 2 (native) or 8 (phase4)
4. Add the two products
5. Add 208 (native) or 832 (phase4)

The checker does not infer these identities from the metadata. It expands both
original and folded bridges using exact sparse polynomials over the four formal
indeterminates F, x, theta, and Tclean. It verifies every integer coefficient of
the clock polynomial and of `(C - Tclean)^2`.

For each fixture/model pair it additionally verifies:

- Every inherited core gate is literally identical, in the same order
- All natural ports and all ordered positive witness ports are identical
- All twenty comparison rows are literally identical
- The first nineteen comparison pairs refer exclusively to the unchanged core
  or ports
- The entire 59-gate SOS suffix is literally identical
- The final residual compares the newly computed clock with Tclean

Thus, if the common first nineteen residual polynomials are R_0,...,R_18, both
complete circuits are exactly

    sum_(i=0,...,18) R_i^2 + (C - Tclean)^2.

The clock identity proves equality of these entire output polynomials in the
integer polynomial ring. No comparison needs to vanish, no source execution
needs to be accepted, and no positivity or other domain assumption is used to
establish this identity. It is stronger than equality only on satisfying tuples.

Consequently, on the stated natural x,Tclean and strictly positive integer
witness domain, the zero set is exactly unchanged, with the identity map on
witness tuples. In particular, every individual positive-witness fiber is
unchanged. The frozen base's infinite positive fibers remain infinite; folding
does not make the representation finite-fold.

## Closure, liveness, and complete SOS

The checker independently parses every arithmetic row, rejecting booleans as
integer literals, unknown operators, repeated coordinate or gate names, and
forward or undeclared operands. A reverse topological dependency pass proves
that every declared gate and every natural/positive coordinate is output-live.
There are no extra dead gates or hidden raw input coordinates y or T.

For all eight circuits it proves that the final 59 rows consist of twenty exact
comparison subtractions, twenty corresponding self-products, and nineteen
additions collecting every square exactly once. Therefore over integers the
output is nonnegative and vanishes if and only if all twenty comparisons hold.
All nineteen retained raw guards, positive F, and the paid positive theta remain.
The output-copy equality F=y stays projected out just as in the frozen originals.

The independently rebuilt ledger agrees in every field with each emitted
ledger, including integer-literal sets, natural/witness counts, exact degree,
comparison count, SOS-gate count, and liveness flags. Text DAG files match their
JSON instructions and interface declarations. Emission receipt hashes, original
reference hashes, and complete ledgers are independently authenticated.

## Exact degrees, without relying only on top propagation

Every coordinate in the ordered `parameters + auxiliaries` list is assigned
`(i+2) z`, with i starting at zero. The checker propagates formal total-degree
upper bounds and, separately, computes **every coefficient** of the specialized
univariate polynomial modulo 1,000,003. At each gate it cross-checks the actual
coefficient at the formal bound against the separately propagated formal-top
component and checks the emitted full gate trace.

A zero formal-top component does not lower the formal bound. Each complete
circuit has two such zero entries, and their bounds are retained. The specialized
output reaches the full formal bound with nonzero leading coefficient:

| Fixture/model | Formal upper bound | Actual specialized degree | Leading coefficient modulo 1,000,003 |
|---|---:|---:|---:|
| INC2;DEC2, native | 2344 | 2344 | 135347 |
| INC2;DEC2, phase4 | 2344 | 2344 | 135347 |
| ZERO3, native and phase4 | 1192 | 1192 | 977370 |
| NOP, native and phase4 | 1192 | 1192 | 977370 |
| POSITIVE3, native and phase4 | 1192 | 1192 | 977370 |

Each degree-2344 specialization has 2,345 nonzero coefficients; each degree-1192
specialization has 1,193. Their complete coefficient-list hashes are in the
machine-readable audit receipt. A nonzero specialized coefficient at the
formal upper bound proves that the integer multivariate polynomial has exactly
that degree. These degrees and formal-top values match the pinned originals.

## Additional tests and negative controls

For each of the eight pairs, twelve arbitrary signed-integer assignments and
32 deterministic modular assignments are evaluated through both complete DAGs.
Every output matches its original and a separate direct sum of the twenty
residual squares: 96 signed and 256 modular pairwise checks in total. Integer
runs additionally check nonnegativity and zero iff all comparisons vanish.
These tests supplement the coefficientwise proof; they do not replace it.

Eleven deliberate in-memory corruptions are rejected independently in each
model, for 22 rejection checks:

- Wrong folded constant
- Changed inherited core literal
- Removed positive witness
- Changed positive witness domain
- Undeclared operand
- Extra dead gate
- Removed retained comparison
- Incorrect residual square
- Underreported total operation count
- Wrong exact-degree ledger claim
- False formal-top coefficient

Only copies in memory are mutated. The actual original and folded circuits are
not changed by these negative tests.

## Reproduce

From the new addendum directory, using only standard Python 3:

    python audit/check_folded_clocks.py --expect audit/independent_folded_clock_audit.json

This is a deterministic read-only replay. It uses only local JSON and DAG text
as data, not the source/emitter Python or earlier auditor code. It also succeeds
when invoked from an unrelated current directory: supply the checker path and
`--expect` receipt path as absolute paths (or paths correctly relative to that
current directory). Circuit and reference-data paths resolve from the checker's
own addendum root. The receipt includes the checker's own SHA256.

To additionally verify the live frozen base before and after:

    python audit/check_folded_clocks.py --expect audit/independent_folded_clock_audit.json --check-live-base /path/to/original-base-packet

Without `--expect`, the checker writes only its deterministic audit receipt into
this addendum's audit directory. The initial live-base and portable read-only
replay outputs are saved alongside this report.

## Scope and unchanged limitations

This addendum proves an arithmetic constant-folding improvement and exact
all-tuple polynomial equality. The accepted-time interpretation remains
conditional on the already documented raw/native and clean reverse-lift
results. The audit does not materialize enormous positive native/Pell witness
tuples, and signed/modular tests are not represented as doing so.

No new universal source, ordinary-input universal loader, universal operation
bound, rational-zero characterization, unique/finite-fold witness claim,
stationary-halt statement, later-recurrence statement, or arithmetic optimality
claim is established. The separate four-gate zero-step circuits are unchanged
in the frozen base and are not among these eight folded nonempty circuits.
