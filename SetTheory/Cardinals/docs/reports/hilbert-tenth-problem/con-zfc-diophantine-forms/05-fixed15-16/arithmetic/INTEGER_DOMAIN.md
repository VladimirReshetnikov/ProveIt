# Unrestricted-integer versions

These two optional JSON files are complete arithmetic circuits. Their unknowns
range over all integers, without positivity constraints. No abbreviated call to
the positive-variable circuit remains in either JSON instruction array.

| JSON stem | Integer unknowns | Degree | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|---:|---:|
| `integer45_product187_degree590` | 45 | 590 | 91 | 96 | 187 |
| `integer48_sos198_degree136` | 48 | 136 | 90 | 108 | 198 |

For each original positive witness `z`, substitute

```
z = 1 + a*a + b*b + c*(c+1).
```

This costs three multiplications and four additions. Its value is positive for
every integer triple, because `c*(c+1)` is nonnegative for every integer `c`.
Every positive integer occurs. Indeed, for `n=z-1 >= 0`, Legendre's three-square
theorem represents `4*n+1` as a sum of three integer squares. Reduction modulo
four shows that exactly one square is odd and two are even. After permutation,
write them as `(2*c+1)^2`, `(2*a)^2`, and `(2*b)^2`. Subtracting one and dividing
by four gives `n=a*a+b*b+c*(c+1)`.

It follows that the new equation has an integer zero exactly when its parent
has a strictly positive zero. The main paper proves that this is equivalent in
ZFC to the existence of a finite ZFC refutation. Consequently absence of integer
zeros for either of these complete circuits is equivalent in ZFC to Con(ZFC).

Degrees double exactly, not merely as upper bounds. Substitution of quadratic
polynomials gives the upper bound. For the reverse bound, set all `b=c=0`; the
highest homogeneous part of the parent is then evaluated at the distinct
squares `a_j^2`. Distinct parent monomials remain distinct, so its nonzero
highest homogeneous part remains nonzero.

## Reproduction and evidence

From this folder, run:

```
python3 build_integer_sources.py
```

Default mode is read-only. It checks the pinned parent-source hashes, rebuilds
both complete instruction arrays, verifies their receipts, graph order,
liveness, counts, and degrees, and compares each complete source with the
independent displayed closed forms on twelve signed-integer and twelve rational
fixtures. The full univariate modular degree evaluation is a supplementary
diagnostic; the mathematical degree proof above supplies uniform exactness.

`python3 build_integer_sources.py --write` regenerates only these two integer
JSON files. It does not change the existing positive-variable sources. The
generator uses only Python's standard library and the sibling verification
modules included in this artifact folder. The checks neither materialize the
astronomical fixed compiler numerals nor construct any halting witness.
