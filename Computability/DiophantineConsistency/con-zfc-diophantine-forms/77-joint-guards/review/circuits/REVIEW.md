# Independent shared-DAG review

Review date: 24 October 2026. All six delivered circuits pass the independent
literal, symbolic, liveness, and arithmetic-count audit. The reviewer is
distinct from the circuit author. No author builder, checker, or polynomial
ring is imported by this review's checker.

## Verified counts

| Source packet | Integer variables | Exact degree | Shared residual gates | Final SOS gates | Total binary gates |
|---|---:|---:|---:|---:|---:|
| joint19_degree88 | 19 | 88 | 96 | 13 | 109 |
| joint20_degree32 | 20 | 32 | 97 | 15 | 112 |
| joint21_degree20 | 21 | 20 | 98 | 17 | 115 |
| joint22_degree16 | 22 | 16 | 99 | 19 | 118 |
| joint23_degree12 | 23 | 12 | 100 | 21 | 121 |
| joint25_octic | 25 | 8 | 102 | 25 | 127 |

Every live binary addition, subtraction, and multiplication counts, including
scalar multiplication, squaring, residual formation, and the final sum of
squares. Integer numeral leaves and reuse of an existing register cost zero.
For m residuals, the finalizer uses m square multiplications and m-1 additions,
accounting for all 2m-1 displayed finalizer gates. Every serialized gate is
live in the final output, every declared variable and coefficient is live,
and all references point backward to a declared input or earlier gate.
The count is an exact count of this implementation, not a minimum-circuit
theorem or a bit-complexity estimate for arithmetic on enormous integers.

The 121-operation circuit targets the V-eliminated 23-variable packet, whose
actual expanded support is 3,713 monomials. It does not target the alternative
I-eliminated packet with 2,968 monomials. Those two secondary metrics must not
be combined as if they described one delivered polynomial.

## Exact identity proof, without numerical sampling

The checker first independently constructs the compact source equations
already reviewed in `../guards/MATHEMATICAL_REVIEW.md` and applies the exact
coordinate restorations for each endpoint. For the higher-degree factored
packets, the fully inlined AST is literally identical to the source packet.
For the lower-degree expanded packets, the reviewer-owned sparse integer
polynomial ring verifies every source residual exactly. The expected row
order includes the extra zeta-restoration row for the 25-variable octic.

The circuit's W, X and Y cut registers are then evaluated symbolically over
the original declared input ring and checked against

    W=4(3w3+1), q=beta(3J3+1)+1,
    X=qW, Y=(2v_scale+1)q^3.

Their definitions are therefore actual polynomial identities, not assumed
annotations. Next, W, X and Y are treated as independent formal variables
and every circuit residual is compared with its intended compact polynomial
by exact sparse algebra. Equality with these independent variables implies
equality after substituting the now-validated original-input definitions.
This staged universal identity proof avoids expanding a degree-88 final
polynomial, without weakening the claim to tests at selected points.

Finally each residual root is replaced by a distinct independent variable.
The remaining gates are checked to equal exactly the sum of their squares.
Combining the cut, residual, and finalizer identities proves that every
delivered DAG evaluates its pinned literal source polynomial, on every
integer assignment and indeed over any commutative ring. There is no new
row-equivalence transformation or sign assumption inside these evaluators.

The exact fixed-coefficient binding and input list agree with the source
JSON byte-for-byte. Source and DAG SHA256 identities, operation histograms,
and staged support counts are included in the receipts. The source packets'
exact degrees consequently carry over to the circuit outputs. Their logical
connection with finite ZFC refutability is inherited unchanged; this circuit
audit is not a new proof-assistant certificate of that connection.

## Reproduction

Run `review/circuits/independent_check.py` normally and with Python `-O`.
It uses only Python's standard library and the reviewer-owned code in
`review/guards/`. Results are `CHECKS.json` and `CHECKS_OPTIMIZED.json` in
this directory. Acceptance checks are not removable Python assertions.
