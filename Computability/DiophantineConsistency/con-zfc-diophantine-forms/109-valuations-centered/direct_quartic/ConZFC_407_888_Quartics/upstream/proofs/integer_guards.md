# A quartic companion over unrestricted integers

Let the synchronized and contracted source have 522 nonnegative coordinates
`x_0,...,x_521`, and let `r_0,...,r_399` be its 400 literal quadratic
residuals. Their simultaneous vanishing is equivalent to the vanishing of
the delivered natural-domain quartic `sum(r_j^2)`.

Retain all 522 source coordinates, now quantified over the unrestricted
integers. For each `i` introduce three additional unrestricted integer
coordinates `a_i,b_i,c_i`, and put

```
g_i = 8*x_i + 1 - a_i^2 - b_i^2 - c_i^2.

Q_Z = sum_{j=0}^{399} r_j^2 + sum_{i=0}^{521} g_i^2.
```

This is a literal integer-coefficient polynomial in 2,088 unrestricted
integer variables. Its defining system has 922 quadratic residuals.

## Soundness of the projection

At an integer zero of `Q_Z`, every squared residual is zero. In particular
`8*x_i+1=a_i^2+b_i^2+c_i^2>=0`. Since `x_i` is an integer, a negative value
would give `8*x_i+1<=-7`, a contradiction. Thus every source coordinate is
nonnegative, and the first 400 rows restore a source solution.

## Completeness of the lift

Given a nonnegative source solution, each positive integer `8*x_i+1` is
1 modulo 8. Legendre's three-square theorem states that a nonnegative integer
is a sum of three integer squares exactly when it is not of the form
`4^a*(8*b+7)` for nonnegative integers `a,b`. The integer `8*x_i+1` is odd
and 1 modulo 8, so it cannot be exceptional. Choose its three-square
representation independently for each `i`. Every `g_i` then vanishes.

Therefore `Q_Z` has an unrestricted integer zero if and only if the source
has a nonnegative integer zero. This is an existence equivalence; different
three-square representations can give multiple lifts of one source point.
Composing with the inherited direct source theorem gives the same consistency
equivalence. The domain conversion itself adds no computational calibration
assumption and does not prove consistency or unsolvability.

## Exact degree and numerical metrics

All residuals have degree at most two. The fresh coordinate `a_0` appears
only in `g_0`, with coefficient -1 at `a_0^2`. Consequently the coefficient
of `a_0^4` in `Q_Z` is exactly 1, establishing exact total degree four.

The generated unrestricted-integer equation has:

| Quantity | Exact value |
| --- | ---: |
| Original coordinates | 522 |
| Added three-square coordinates | 1,566 |
| Total unrestricted coordinates | 2,088 |
| Quadratic residuals | 922 |
| Total degree | 4 |
| Expanded nonzero monomials | 26,791 |
| Maximum absolute expanded coefficient | 83,901,150 |
| Maximum absolute residual coefficient | 4,556 |

The original natural polynomial has 20,225 monomials and maximum absolute
coefficient 83,900,628. No four-square substitution or doubling of total
degree is used. Its literal residuals are retained without changing a byte
of their coefficients.

## Portable construction and independent audit

Run:

```
python3 make_integer.py /absolute/path/to/source/equation.json /output/directory
```

Only the Python standard library is required. The helper emits the complete
residual system, the fully expanded ordinary polynomial, a coordinate binding
and source-hash certificate, and a verification receipt.

The primary expansion multiplies every ordered pair of residual terms.
The independent verifier instead expands source rows using diagonal terms and
twice each unordered cross term, then adds the explicit fifteen-term identity
for each new guard square. It checks the complete polynomial coefficient list,
every guard allocation and row, source preservation, counts, and the exact
quartic leading-coefficient certificate. Normal and optimized Python runs
produce identical equation, expanded polynomial, certificate, and receipt
bytes; no acceptance condition relies on Python assertions.

The finite algebraic checks supplement the unbounded three-square theorem.
They are not offered as a finite verification that every positive integer
admits the required representation.
