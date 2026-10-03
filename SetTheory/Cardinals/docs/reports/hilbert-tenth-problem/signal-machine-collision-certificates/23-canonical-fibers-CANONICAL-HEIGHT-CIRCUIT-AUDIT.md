# Independent audit of the complete canonical-height circuits

## Verdict

**PASS.** All eight complete nonempty-history circuits are closed, fully live literal arithmetic DAGs. Their inherited arithmetic core differs from the frozen five-gate-folded parent at precisely the two explicitly authorized height-reassociation gates. All twenty inherited comparison pairs, all 22 supplied native coordinates, positive terminal payload F, raw fixture tables and guards, chronological transport, physical-clock congruence, and five-gate clean-clock bridge are retained. One positive coordinate and one comparison are appended. The finalizer is the complete 21-row sum of squares.

The independently traversed ledgers, for **each** of native and phase4, are:

| Fixture | M | A | Complete operations | Positive witnesses | Exact total degree |
|---|---:|---:|---:|---:|---:|
| INC2;DEC2 | 240 | 368 | 608 | 61 | 2344 |
| ZERO3 | 185 | 298 | 483 | 59 | 1192 |
| NOP | 183 | 298 | 481 | 59 | 1192 |
| POSITIVE3 | 190 | 294 | 484 | 59 | 1192 |

There are two natural parameters in every circuit. The eight DAGs contain 4,112 arithmetic gates altogether. Every fixed scalar multiplication, residual subtraction, square and accumulator addition is charged. These are literal-integer arithmetic counts, not constant-synthesis counts or optimality assertions.

Both separate zero-step files are byte-identical to their authenticated frozen originals. Each has four operations (2M+2A), no witnesses, one comparison and exact degree two.

## Independence and trust boundary

`check_canonical_height.py` was written independently as a standard-library data-only checker. It does not import, call or execute any upstream Python, folded emitter, canonical-height emitter or inherited checker. It parses JSON as inert data, rejects duplicate JSON keys, and implements its own DAG validation, integer evaluation, affine polynomial arithmetic, formal-degree propagation, complete modular univariate polynomial arithmetic, and negative tests. Textual DAGs are parsed by a restricted grammar, never evaluated as Python.

The checker hard-pins the folded manifest hash

`774a4498984ebccf8216897e21bf597084e70b148557ba4fa12b597bba44ba91`

and the original base manifest hash

`1bf1225aa950ad1d4f842c8bf098e1935925cd1d52c90453b7696c1321648f95`.

Every folded arithmetic reference is checked for its exact SHA-256 and byte length against the first authenticated manifest. The two zero-step references are similarly checked against the base manifest. Each canonical circuit's parent hash and reassociation metadata are checked against the authenticated data and actual arithmetic.

Portable replay uses only the included references. The optional live-tree check compares every file in the two original frozen directories against the independent before-audit snapshot in `frozen-before.json`. Both live trees passed before and after the complete audit; no file there was edited or executed.

This audit proves arithmetic/interface preservation and the stated all-tuple polynomial identity. It does not independently prove the inherited native/Pell existence theorem or construct a complete positive native witness. The canonical zero-fiber semantics and completeness argument are treated in the separate proof audit. In particular, no native-fiber finiteness or uniqueness is claimed here.

## Exact all-tuple identity

Write the frozen intermediate endpoint sum as d = n_initial + n_target. The actual frozen gates are

    old_mid = d + height_slack
    h = old_mid + theta_positive

where old_mid is `bridge_height_without_time`. The checker verifies, in each authenticated reference, that this intermediate has exactly one gate consumer, namely the h-producing addition, and occurs in no comparison. It is not a pre-existing S producer.

The canonical DAG replaces precisely those two gates by

    S = d + theta_positive
    h = S + height_slack

with S named `canonical_endpoint_clock_sum`. Exact sparse-affine arithmetic over the integers confirms equality of the old and new h polynomials. Every other inherited core gate has the same name, operation and literal ordered operands as before. Induction through the topological source therefore preserves every remaining old core register and each of the twenty old residual polynomials. This is a structural algebraic proof, not a randomized identity inference.

Two new additions then compute

    canonical_slack_sum = height_slack + canonical_height_slack
    canonical_sum_plus_one = S + 1.

The new positive coordinate `canonical_height_slack` is appended in the supplied-coordinate order. The twenty-first residual is thus exactly η+κ−S−1. The checker reconstructs every residual subtraction, its self-product and the full left-associated accumulator for both the original twenty-row and new twenty-one-row finalizers. Consequently, in the integer polynomial ring,

    Q_new = Q_folded + (η + κ − S − 1)^2.

This identity holds on all integer tuples, and formally over any commutative coefficient ring. It does **not** assert equality of old and new zero fibers. On natural external ports and strictly positive integer witnesses, the added square imposes a real additional condition. It does not provide an all-input polynomial coordinate change or a polynomial algorithm for computing the least dyadic ceiling. This distinction agrees with the main theorem, especially §§6–7.

The identity uses the same supplied native θ in both physical models. The retained clean clocks are respectively 192(F+x)+2θ+208 and 768(F+x)+8θ+832. Neither U nor U/4 is substituted into the new height comparison.

## Independently derived complete cost

The old twenty-row finalizer has 20 residual subtractions, 20 squares and 19 accumulator additions: 20M+39A = 59 gates. The new finalizer has 21 residual subtractions, 21 squares and 20 accumulator additions: 21M+41A = 62 gates. The two row producers contribute another 2A. The two-gate reassociation preserves the old height-construction allocation.

Thus the complete net increase is precisely 1M+4A = 5 gates, with one additional strictly positive witness. Traversing the full candidate lists gives the table above, independently of their ledger fields. In fixture order INC2;DEC2, ZERO3, NOP, POSITIVE3, the folded totals 603/478/476/479 become 608/483/481/484. The native and phase4 schedules have equal gate counts because their different physical factors are already folded into paid literal scalar multiplications.

## Closure, liveness, inheritance and text checks

The checker rejects duplicate names, gate/port collisions, unknown operations, noninteger constants, unbound or forward operands, missing outputs, malformed comparisons, dead gates and unused supplied coordinates. It traverses the complete output-ancestor graph rather than trusting the liveness flags in the ledger. It checks the natural ports, complete ordered positive list, original domain, full 22-coordinate native block, positive F, native θ, raw source-machine description and mapping, source and folding provenance, exact old comparison list, all inherited non-reassociated gates, row producers, complete finalizer, literals, counts and degree fields.

Each of the eight textual DAGs parses to exactly the corresponding JSON gate list; textual natural/positive ports and output declarations also agree. The unchanged first two outer comparisons, all sixteen native comparisons, clock congruence and clean clock row remain literal. Therefore no chronology, raw-residue guard or native bound was removed to obtain the new cost.

## Exact degree certificates by two methods

First, the checker independently propagates a formal total-degree upper bound and the coefficient at that bound after substituting coordinate i by (i+2)z modulo the prime 1,000,003. Bounds are retained even when a chosen top coefficient cancels. Every emitted per-gate certificate entry, the complete substitution map and the output certificate are compared to this recomputation.

Second, a separate implementation evaluates the **entire univariate polynomial at every gate**, storing all coefficients modulo 1,000,003 and using full convolution for multiplication. This method is not truncated leading-term propagation. It checks all 4,112 gate coefficient-at-bound values, obtains the actual specialized output degrees, and independently verifies the complete specialized polynomial identity against the folded output plus the full extra squared residual.

The specialized leading coefficient is 135347 at degree 2344 for both INC2;DEC2 outputs, and 977370 at degree 1192 for all six other outputs. Each is nonzero. A nonzero modular coefficient gives a genuine integer-polynomial degree lower bound; it matches the independently propagated upper bound. The reported degrees are therefore exact for these emitted polynomials. Full specialized output coefficient-vector hashes are recorded in the machine-readable receipt.

The zero-step outputs are independently checked as (384x+400−Tclean)^2 and (1536x+1600−Tclean)^2, with nonzero degree-two specialization coefficients 585225 and 418734 respectively.

## Sanity evaluations and deliberate corruptions

Supplementary complete-DAG evaluation covers 96 deterministic signed integer assignments and 256 deterministic modular assignments across the eight circuits. Every case checks the entire output identity and all twenty old residual values. The signed cases also check nonnegativity of the complete integer SOS. These evaluations supplement the structural proof; they are not used as a replacement for it or as a purported positive Pell witness test.

Twenty-nine independent in-memory corruptions are rejected. They cover missing or duplicate positive coordinates; relaxing the domain; dropping F or a native coordinate; unsupported operations; unbound inputs; duplicate or dead gates; wrong output or inherited scalar; source pin, raw mapping and guard changes; removal of chronology, native, clock-congruence, clean-time or canonical rows; both incorrect reassociations; the canonical off-by-one; unsquared residual or missing final sum; false ledger/degree/top/substitution certificates; and textual DAG disagreement. The receipt records each rejected case and the detected reason. Frozen input files are never mutated for negative testing.

## Read-only replay

From the packet root, run:

    python -B audit/check_canonical_height.py --expect audit/independent-canonical-height-audit.json

For an optional check of the still-present original frozen directories, add `--live-frozen`. The checker performs no writes; direct its JSON stdout elsewhere if a fresh receipt is wanted.

`portable-read-only-replay.json` records a successful relocated replay with both code and data in an independent temporary directory, all 40 files mode 0444 and all directories mode 0555. It ran in isolated Python mode with bytecode generation disabled. The recomputed report was identical to the included path-independent receipt, and every input file hash was unchanged after replay. The temporary copy was removed after the test. The source packet and both frozen trees were not altered by that replay.
