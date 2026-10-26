# Exact polynomial format

`equation.json` specifies one single polynomial:

```text
P(x) = sum(R(x)^2 for R in residuals)
```

The `variables` array fixes the coordinate count and order. Every coordinate
ranges independently over the unrestricted integers. Names in this array are
historical annotations; after shears and translations they need not describe a
coordinate's original semantic value. Use the exact ordered certificates for
that correspondence.

Each residual has a `terms` array. An entry `[c, [i_1, ..., i_d]]` means
`c * x[i_1] * ... * x[i_d]`. The coefficient is a nonzero integer; indices are
sorted and may repeat. An empty index list means the constant monomial.
For example, `[3,[2,2]]` means `3*x[2]^2`, and `[-1,[]]` means `-1`.
There are no duplicate monomials within a row. The degree is at most two.

The neighboring `expanded_polynomial.json` uses the same term representation
for the fully collected quartic. It lists only nonzero coefficients, each once.
Its `variables` field, where present, is a count rather than the descriptive
array. Different inherited stages have different `schema` labels and JSON
indentation; the sparse coefficient convention is the same.

`metrics.json` reports:

- `variables`: unrestricted integer coordinate count;
- `rows`: number of squared residuals;
- `degree`: exact total degree of the collected polynomial;
- `monomials`: number of its nonzero monomials;
- `height`: largest absolute coefficient in the collected polynomial;
- `row_height`: largest absolute coefficient in any residual.

All printed metrics are recomputed from coefficients by the independent
release checker. The principal polynomial is fixed by its complete residual
data and integer domain, not by historical labels or the abbreviated formulas
used to explain its construction.
