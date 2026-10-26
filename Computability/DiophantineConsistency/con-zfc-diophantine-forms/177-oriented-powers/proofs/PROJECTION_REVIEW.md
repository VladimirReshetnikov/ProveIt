# Independent audit of the acyclic projection circuits

25 October 2026. This is a separately assigned AI-assisted mathematical and
finite-algebra audit, not external human peer review or a proof-assistant
formalization.

## Ordinary proof behind the certificate

Let the frozen integer source system have residuals r_0,...,r_{m-1}.
Each selected pivot row has the literal form

    r_j = epsilon_j x_v + f_j(x),  epsilon_j in {-1,+1},

where x_v does not occur in f_j. Distinct pivots use distinct rows and
distinct variables. The dependency graph between eliminated variables is
acyclic. Successively substituting x_v=-epsilon_j f_j therefore defines
each eliminated coordinate as an integer polynomial in the retained
coordinates. No division by a nonunit and no divisibility assumption occurs.

Every original zero projects to a zero of the retained residuals after
substitution, and recursively restoring these integer polynomials gives
the unique original zero over any projected zero. Thus projection is an
integer zero-set bijection. Summing the squares of the retained residuals
preserves exactly their simultaneous vanishing.

This argument applies to a pivot in the contracted singleton pool row
as well as to other rows, provided its actual literal pivot is unit-linear.
There is no reason to prohibit that pivot because of the row's semantic
label. The checker validates the literal polynomial condition.

## Independent checker

`deliverable/code/verify_projections.py` imports no construction, search,
or optimizer module. It checks:

1. Exact source hash, unrestricted-integer domain, variables and source
   coordinate order, all pivot slopes, distinctness, and dependency acyclicity.
2. Every arithmetic circuit node and a complete partition into definition,
   residual, macro, factored-pool, and final sum-of-squares blocks.
3. Exact local polynomial identities for each block. Source variables and
   macros are cut registers; they are not expanded recursively. Unused
   local temporaries are released after their last use.
4. Every factored pool independently expanded back to its literal frozen
   source row, and every retained source row represented exactly once.
5. The final output equal to exactly the sum of the squares of all retained
   residual registers, with no added or omitted summand.
6. Weighted source-degree bounds, the actual highest homogeneous component
   specialized modulo 1,000,000,007, and a nonzero residue for one residual
   at the maximum bound. That residual has the claimed exact degree. Over
   the reals its top square cannot cancel with other top squares, so the
   final polynomial has twice that exact degree.
7. Submultiplicative coefficient l1 bounds through every definition and
   residual. If these residual bounds are B_j, then the final coefficient
   height is at most sum_j B_j^2, strictly below the reported power of two.
   The reported exponents are upper bounds, not exact heights.
8. Binary arithmetic operations and literal constants in the live output
   ancestry. Dead stored macro nodes are excluded from the live operation
   count; the stored-node metric is stated separately.
9. Polynomial occurrence of every input: reverse differentiation of the
   exact arithmetic circuit at explicitly recorded modular input tuples
   gives a nonzero partial derivative for each declared variable. Such a
   witness proves the corresponding integer polynomial derivative is
   nonzero. This is stronger than a graph-reachability check and does not
   invoke a probabilistic identity-test conclusion.

## Completed results

All eleven profiles passed in normal and optimized Python. Their complete
receipts are `verification/PROJECTION_NORMAL.json` and
`verification/PROJECTION_OPTIMIZED.json`; these receipts agree exactly.
They cover 1,227 unit pivots, 1,903 circuit blocks, and 1,160 nonzero
partial-derivative witnesses across the eleven equations. The first
deterministic evaluation tuple sufficed for every equation.

| Variables | Exact degree | Residuals | Live binary operations | Height bound |
|---:|---:|---:|---:|---:|
| 137 | 12 | 74 | 2548 | <2^55 |
| 121 | 16 | 58 | 2502 | <2^84 |
| 118 | 22 | 55 | 2523 | <2^58 |
| 111 | 32 | 48 | 2502 | <2^107 |
| 106 | 38 | 43 | 2457 | <2^147 |
| 104 | 64 | 41 | 2451 | <2^223 |
| 99 | 128 | 36 | 2483 | <2^556 |
| 94 | 256 | 31 | 2468 | <2^788 |
| 93 | 328 | 30 | 2448 | <2^788 |
| 89 | 32768 | 26 | 2453 | <2^82436 |
| 88 | 65540 | 25 | 2450 | <2^164875 |

The largest live literal constant is 256 in every circuit. This does not
mean the expanded coefficients are at most 256.

Five deliberately corrupted artifacts were rejected for every profile:
wrong domain, changed arithmetic gate, changed pivot, changed leading-degree
witness, and changed pool selector. The 55 rejection controls pass with
Python optimization enabled as well; validity checks do not use `assert`.

These exact finite checks authenticate the delivered polynomials and their
explicit polynomial projection maps. The all-base pooling theorem and
the retained C222/ZF/ZFC calibration are separate unbounded mathematical
dependencies. No consistency, global minimality, or standalone full formal
verification claim follows from the tests.

## Addendum: the 87-variable endpoint

The final package adds a twelfth profile,
`integer87_degree8388612`. This addendum records a separate actual run of
the independent checker with Python optimization enabled:

```text
python3 -O -B code/verify_projections.py \
  --profile integer87_degree8388612 \
  --receipt verification/PROJECTION87_OPTIMIZED.json
```

The run passed. Its receipt agrees exactly with the normal-run receipt
`verification/PROJECTION87.json`, including all derivative witnesses and
all corruption-test results.

| Quantity | Independently checked value |
|---|---:|
| Unrestricted integer variables | 87 |
| Exact degree | 8,388,612 |
| Retained residuals | 24 |
| Unit pivots | 129 |
| Circuit blocks checked | 172 |
| Live binary operations | 2,447 |
| Stored circuit nodes | 3,261 |
| Largest live literal constant | 256 |
| Expanded coefficient height | strictly below 2^21,104,473 |
| Nonzero partial-derivative witnesses | 87 |
| Deliberate corruption controls rejected | 5 |

The new pivot selection is the previous 88-variable selection together
with the unit pivot `(row 46, variable 61)` in the 216-variable all-five
pooled source. Its literal row is

```text
u_10 - 25u_10^2 - 40u_10 u_24 - 20u_10 u_60
     - 16u_24^2 - 16u_24 u_60 - 4u_60^2 + u_61 = 0.
```

Thus the extra restoration polynomial is explicitly

```text
u_61 = (5u_10 + 4u_24 + 2u_60)^2 - u_10.
```

This is an integral unit-linear elimination. The complete dependency
graph, including this extra definition and all 128 earlier definitions,
was checked to be acyclic. The large degree increase comes from the
resulting composed substitution; the all-five pooling theorem is
unchanged. A smaller number of variables here does not imply a smaller
degree or coefficient bound.

For the exact-degree lower bound, the independently evaluated highest
homogeneous part of source residual 102 has nonzero value 217,412,373
modulo 1,000,000,007 at the prescribed specialization. Its weighted upper
degree is 4,194,306, so that residual has exactly this degree. The final
sum of squares consequently has degree exactly 8,388,612: its nonzero
highest-degree real squares cannot cancel. Every one of the 87 retained
inputs has a nonzero partial derivative of the final polynomial at the
first recorded modular evaluation tuple. Thus no declared variable is
merely a syntactically reachable input that cancels out of the polynomial.

As in the first eleven profiles, the changed-domain, changed-gate,
changed-pivot, changed-degree-witness, and changed-pool-selector controls
were all rejected under `-O`. Across the twelve separately recorded
profiles, the checks now cover 1,356 unit pivots, 2,075 circuit blocks,
1,247 nonzero derivative witnesses, and 60 corruption rejections. These
are aggregate audit counts, not claims that the different profiles have
disjoint definitions or witnesses.

## Addendum: final report and retained-parent checks

The final report review also checked the generated polynomial appendices.
Running `python3 -O -B code/check_article.py` successfully parsed all 162
literal parent residuals and all twelve pivot lists, containing 1,356
pivot pairs. The displayed profile metrics were compared with the frozen
equation artifacts.

The request table received an additional independent check: its actual
TeX rows were parsed directly without importing the exporter, builder,
or any checker. The 17 entries, including their group/base, index,
output, D, Y, and Z expressions, reconstructed all 28 literal AY/norm
rows for the 14 distinct Pell pairs. The index assignments reconstructed
parent row 150 exactly, using, for each distinct pair, the polynomial

```text
Z^2 - 2D - 2Z + 2 - 2kY + k^2.
```

The three singleton entries reconstructed rows 106, 108, and 110; the
three-member and eleven-member groups reconstructed rows 158--161.
Finally, all five reconstructed base and E polynomials matched the
frozen pooling certificate under its explicit coordinate map. This
checks the inherited nonconsecutive request numbers and the affine
offsets directly against the frozen coefficients, including the
`x_9 - 1`, `x_159 - 1`, `x_102 - 1`, and `x_184 + 1` expressions. No
request-table discrepancy was found.

The retained `sources/parent225.json` is exactly 29,598 bytes. Its SHA-256
is

```text
fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56
```

and its Git blob identifier, recomputed from the actual bytes with the
Git blob header, is

```text
425a70a4960e0c60ebedfcae641f08be15dbdcc0
```

These checks authenticate the exact retained coefficients, rather than
just the equation's dimensions or a similar normalized copy.

The ordinary oriented-pooling proof, its zero-base bootstrap, and the
acyclic projection proof were reviewed against the report. No new
mathematical gap was found in these steps. The asserted equivalence with
syntactic `Con(ZFC)` still depends on the retained C222/ZF/ZFC calibration
and the source parent construction. The inherited calibration audit
documents that dependency; this final review does not constitute a fresh
compilation of the complete transitive Lean source closure. The finite
checker is not a replacement for the unbounded arithmetic proof, and
the arithmetic-circuit degree and height certificates are not a proof
of consistency. The 87-variable result is an explicit additional point
in the delivered tradeoff family. Neither this audit nor the search
establishes a global minimum, historical priority, or complete
proof-assistant verification of the entire new package.
