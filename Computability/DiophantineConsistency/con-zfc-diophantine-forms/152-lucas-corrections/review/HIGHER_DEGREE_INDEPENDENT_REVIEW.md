# Independent review of the composed higher-degree equations

**Verdict: PASS.** No hidden domain restriction, nonunit-pivot assumption,
or defect in the degree and coefficient-height arguments was found in the
eight frozen profiles under `alternative/composed_release`.

This is an independent review by the direct-quartic agent of the
higher-degree agent's construction. It covers the new algebraic
transformation and its binding to the 248-variable source. It does not
re-prove the inherited C222/ZF/ZFC calibration or repeat the complete octic
expansion.

## Source binding

`source/equation248.json` is byte-for-byte identical to the independently
verified principal quartic in `direct_quartic/release`. Its SHA-256 is

```text
c51ebc12534db042bd1c7bf7c59f84602f51625e2d952dffa82fa054b5d92192
```

The source has 248 unrestricted integer coordinates and 182 quadratic
residuals. Both the program and its separate pivot certificate bind to
this exact digest for every profile. The programs' retained-coordinate
maps agree with the source metadata.

## Integer zero-set bijection

Every selected pivot row has coefficient exactly `+1` or `-1` on its
selected coordinate, and that coordinate has no other occurrence in that
row. Thus solving the row introduces an integer polynomial, with no
division or nonzero-denominator assumption. Selected coordinates and
selected rows are unique. Their dependency graphs are acyclic; the emitted
definition blocks follow a valid dependency order. Every source coordinate
is either retained or restored, and every source residual is either a
defining pivot or a remaining residual.

These conditions give a genuine bijection of the **integer zero sets**:
project a source zero to retained coordinates, and restore every removed
coordinate uniquely by the defining polynomials. Conversely, a zero of
the new sum of squares makes each remaining integer residual zero, while
the defining substitutions make all selected rows zero. No positivity
claim for restored coordinates is required, since the starting domain is
already all integers. The statement would need additional hypotheses over
the natural numbers, as the report correctly says.

The arithmetic DAG is an explicit ordinary polynomial expression: its only
leaves are integer constants and retained variables, and its operations
are addition, subtraction and multiplication. Its intermediate registers
are expressions, not extra quantified unknowns.

## Exact degree

The propagated coordinate degrees are upper bounds, which is sufficient
even when an intermediate highest-degree part cancels. The propagated
top value is precisely the coefficient at that upper degree after the
univariate specialization `x_i = (i+3)t` on retained **source indices**.
Taking only terms of maximum weighted degree is therefore valid; a zero
top value simply records cancellation or a lower actual degree.

For each profile, a remaining residual at the largest degree bound has a
verified nonzero top value modulo `1,000,000,007`. Consequently its integer
leading homogeneous part is nonzero at the corresponding integer point.
The highest homogeneous part of the final polynomial is a sum of the
squares of the highest residual parts. At that point it is a positive
integer, so cancellation cannot reduce the stated total degree. Primality
of the modulus is unnecessary; no inversion is used. This is an exact
nonvanishing witness, not a probabilistic identity test.

## Coefficient height

The recursive quantity `L` bounds the sum of the absolute values of the
collected coefficients of each restored polynomial. This follows from
the triangle inequality for sums and the convolution inequality for
products. Thus `B = sum(L_residual**2)` bounds the coefficient norm of the
entire sum of squares and hence each individual coefficient. With
`b = B.bit_length()`, the reported strict inequality `height < 2**b` is
correct. All values were recomputed using exact integers, including the
164,870-bit bound for the largest-degree profile. The largest circuit
literal, 256, is correctly distinguished from the expanded height.

| Integer variables | Removed unit pivots | Remaining residuals | Exact degree | Strict height bound |
|---:|---:|---:|---:|---:|
| 225 | 23 | 159 | 6 | 2^27 |
| 153 | 95 | 87 | 8 | 2^47 |
| 144 | 104 | 78 | 12 | 2^50 |
| 125 | 123 | 59 | 16 | 2^80 |
| 117 | 131 | 51 | 32 | 2^144 |
| 111 | 137 | 45 | 64 | 2^173 |
| 102 | 146 | 36 | 256 | 2^691 |
| 94 | 154 | 28 | 65,540 | 2^164870 |

## Independent finite replay

The separate `direct_quartic/review_higher_degree.py` imports neither the
reviewed producer nor its verifier. It independently expands every circuit
block over formal source-coordinate registers and checks its complete
local polynomial identity. It verifies the final sum of squares, row and
coordinate partitions, unit pivots, acyclic restoration, degree witnesses,
and height bounds. It also computes every input derivative by forward
automatic differentiation modulo the stated modulus; all are nonzero and
agree with the package's independently implemented reverse-mode witnesses.
Thus every declared input occurs in the collected polynomial.

All eight profiles pass. The JSON receipt records their immutable hashes,
the exact degree witnesses, hashes of the large integer height bounds,
and the audit script's hash. No expensive full expansion was repeated.
The exact octic support and height are outside this additional review's
scope; their separate complete-expansion certificate remains the relevant
check for those two finer statistics.
