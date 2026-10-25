# Independent finite audit of the eleven-integer family

## Verdict

**PASS for the frozen six literal polynomials, their authentic fixed numeral tuple, exact total degrees, essential variables, operation counts, and finite algebraic identities.** The independent ordinary mathematical review of the unbounded reduction is in `ORDINARY_REVIEW.md`. Neither review is an end-to-end proof-assistant certificate, a proof of the consistency of ZFC, a proof of global optimality, or a ten-variable construction.

The finite checker is `check_independent.py`. It imports only the Python standard library and SymPy; it imports or executes no producer Python module, including the coefficient builder. It was separately written from the displayed formulas and pinned transition data. The producer checker, its polynomial ring, and its arithmetic DAG class are not used.

The technical input inventory is `FROZEN_INPUTS.json`. At freeze, the producer manifest SHA-256 was `a1bfa743a95ee53a2fbbed773b896adf1786d86d98fd6b40c9dddf0f846b2eda`. The inventory excludes only producer `RESULTS.json` and `MANIFEST.json`, which may be updated to record completed external review, and Python cache files. It includes the proof, literal graphs, coefficient payloads, recipe inputs, producer programs, source dependencies, licenses, and ancillary technical documents. The independent checker verifies the inventory on each run.

## Results

| Literal polynomial | Variables | Exact degree | Live binary operations | Nonzero degree-certificate coefficient mod 65521 |
|---|---:|---:|---:|---:|
| `main_saturated11_none` | 11 | 428 | 123 | 50520 |
| `main_saturated11_simple` | 11 | 412 | 127 | 21661 |
| `main_saturated11_sharp` | 11 | 396 | 128 | 60450 |
| `free_main_saturated11_none` | 11 | 376 | 127 | 36197 |
| `free_main_saturated11_simple` | 11 | 364 | 131 | 20587 |
| `free_main_saturated11_sharp` | 11 | 352 | 132 | 22121 |

These are costs of the actual reachable binary addition/subtraction/multiplication DAGs, not counts of displayed abbreviations. Integer/coefficient/variable leaves and reuse are free; scalar multiplication and squaring are charged. There are 768 charged gates across the six graphs. Every graph has exactly the same eleven integer coordinates `j,C,z,h,r,v,w,T,c,n,s`, exactly six coefficient ports, valid topological edges, and no unreachable node. All eleven variables are algebraically essential, not merely named or reachable.

The primary literal graph SHA-256 is `c6398086dfcda00a44e27c8c5085e8f59588c9b37bef04b500c88e184d9238b4`.

## Literal equality and identity coverage

The checker independently transcribes the displayed equation into local polynomial identities, replacing previously specified registers by independent commuting indeterminates. It expands each resulting local difference exactly over the integers with SymPy. It verifies every named abbreviation and covers every arithmetic gate in the literal graph. Consequently, these are universal algebraic checks, not evaluations on selected integer points and not comparisons against producer-generated expression hashes.

In particular, it checks the stronger free-scale budget

`Y^2 [k^2(q^2-Derr)-4q^2 eta^2] - k^2 q^8`,

the main-square-root-saturated strong radicand, the auxiliary `4 U Dm T` term, the carrier `S=srH M^5`, the quintic homogenization, the two choices of integral center, and the exact final cleared four-conjugate equation. Factored register checks compose to the displayed definitions; for example `UbDm=Ub Dm`, `U=A Ub`, and `UDm=A UbDm` imply `UDm=U Dm`, so the checked `strong=Delta U UDm` is precisely `Delta U^2 Dm`.

Separate exact identities verify:

- All four conjugate factors and the denominator-cleared norm identity.
- The congruences `Df=1 (mod Dm)`, `Da=1 (mod Dm)`, `Da=A^2 Dm (mod Df)`, and `Df=1 (mod A)` as polynomial remainder identities. Positivity and their use for gcd arguments belong to the ordinary review.
- Both center cancellations, using `Delta=A^2-1`.
- The complete expanded centered-inner cancellation formula used for degree upper bounds.
- The short projector identity, the integer rescaling identity, and the quintic valuation expansion.

## Authentication of the actual fixed tuple

The checker decompresses all six supplied payloads and checks minimal unsigned little-endian encoding, actual byte count, actual bit length, the producer binding, and six independent hard-coded raw SHA-256 pins. It does not treat a self-reported manifest hash as sufficient authentication.

It then independently parses the pinned 430-transition `k215.tm` table, reconstructs the signal classes and ordered 943-tile list, and checks every tile against the supplied literal list. Starting from that independently reconstructed list, it rebuilds the 989-position packing and derives the six enormous integers using the radix-121, length-8801 formulas. Integer equality is checked against every actual payload, including the already shifted `MF=MF_native+beta`, with the shift applied exactly once. The checker does not simulate the machine and does not claim that reconstructing a tile list proves the unbounded compiler theorem.

The authentic payload bit lengths are 1,064,921 (`beta`), 1,065,043 (`K0`), 1,064,921 (`MC`), 1,064,922 (`MF`), 1,114 (`cone_A`), and 666,105 (`cone_B`). All 108 dependencies in `SOURCE_PINS.json` are checked against their actual bytes. That preservation check establishes which retained sources accompany the argument, not the correctness of every unbounded statement in them.

## Exact degree, not merely an upper bound

For direct equations, ordinary gate degree propagation gives bounds 428 (weak scale) and 376 (free scale).

For a centered equation put `W0=Sn-Ac`, `delta=Q-1`, and let `lambda` be the stated center. The exact identity is

`inner = delta W0^2 + 2 delta S lambda V W0 + delta S^2 P`

`        + S^2 {[delta(lambda^2-4Dm Df)-4Dm Df]V^2+4Dm Df}`.

For the sharp center, `lambda^2-4Dm Df=Dm^2 Ub^2-4Dm`; for the simple center it is `4U^2 Dm^2-4Dm`. These identities are checked symbolically before the checker uses them as degree cuts. Propagating genuine polynomial degree upper bounds gives the following bounds for the five displayed summands:

| Family/center | Five summand bounds | Inner bound | Final bound |
|---|---|---:|---:|
| Weak/simple | 110, 162, 134, 206, 74 | 206 | 412 |
| Weak/sharp | 110, 162, 134, 198, 74 | 198 | 396 |
| Free/simple | 102, 145, 128, 182, 74 | 182 | 364 |
| Free/sharp | 102, 145, 128, 176, 74 | 176 | 352 |

The remaining final correction has smaller degree in each case. The upper bounds therefore apply over the integers after substituting the actual fixed coefficients; no generic-coefficient or noncancellation assumption is used to obtain them.

For an independent lower bound, the checker reduces each authentic integer coefficient modulo the prime 65521 and substitutes `(j,C,z,h,r,v,w,T,c,n,s)=(t,2t,3t,...,11t)` into the literal DAG itself. It computes the complete resulting univariate polynomial exactly in that finite field. Its degree attains the upper bound, with the nonzero leading coefficient recorded in the results table. An exact specialization cannot increase total degree, so this is a deterministic proof of the matching lower bound at the actual coefficients, not a probabilistic heuristic. The two bounds prove each claimed exact degree.

For variable essentiality, exact forward differentiation of the literal DAG modulo 65521 supplies a point with nonzero partial derivative for each coordinate. The receipt records every point and derivative. Such a witness excludes algebraic independence from that coordinate over the integers.

## Negative controls and optimized execution

The checker deliberately changes the opcode at each of the 768 live arithmetic gates, one gate at a time. Every corrupted graph is rejected by the exact symbolic identity layer with operation-count and freeze checks deliberately bypassed. Thus rejection does not rely on the easier metadata or byte-hash mismatch.

It also rejects three wrong register bindings, a cyclic edge, and a false degree for each of the six graphs, plus a bit flip in each of the six actual numeral payloads. There are **804 negative controls** in total. Normal and optimized-Python runs both reject all 804. No correctness check uses Python `assert`, so `python -O` does not disable them.

Run from any working directory:

```sh
python check_independent.py --receipt receipt-normal.json
python -O check_independent.py --receipt receipt-optimized.json
```

The script expects the distributed `review/integer` and `integer` directory layout, or accepts `--source /path/to/integer`. SymPy 1.14.0 was used for these receipts. The full receipts retain all payload hashes, graph hashes, checked identities, source inventory digest, upper-bound cuts, exact finite-field degree witnesses, essential-variable witnesses, and individual mutation rejection messages.

## Proof boundary and disposition

The separate ordinary proof review checks the unconditional bootstrap, parity squareclass separation, pairwise coprimality, adjacent-Pell denominator descent, signed rank hypotheses, strengthened fifth-power projection, late CRT recovery, and fixed-strong-pair completeness/interpolation ordering. The finite program checks algebra and fixed finite artifacts; it does not decide those unbounded implications by sampling.

An initial stale operation-count paragraph was reported before freeze and corrected by the producer. No frozen evaluator change was required by this audit. There is no outstanding finite-audit defect. See `ORDINARY_REVIEW.md` for the independently reviewed ordinary-mathematical verdict and inherited calibration boundary.
