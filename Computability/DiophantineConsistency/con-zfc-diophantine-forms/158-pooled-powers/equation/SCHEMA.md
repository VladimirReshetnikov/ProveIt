# Exact sparse polynomial format

`equation.json` fixes an ordered list of 225 independent integer variables
and 162 ordered quadratic residuals. An index is its zero-based position
in the `variables` list. Variable `name` and `kind` fields are provenance
labels, not extra restrictions or expressions. All coordinates range over Z.

A residual contains a `terms` list. Each element is

```json
[coefficient, [index_1, index_2]]
```

and means the integer coefficient times the product of the listed
coordinates. The empty list is the constant monomial; `[i]` is `x_i`;
`[i,i]` is `x_i^2`; `[i,j]` is `x_i*x_j`. Indices and monomials are sorted,
each monomial occurs once per residual, and zero coefficients are omitted.

For example, the first delivered row is exactly

```json
{"label":"multiplication","terms":[[-1,[2,2]],[1,[3]]]}
```

so `R0=-x2^2+x3`. Its label is descriptive only.

The single polynomial is **the sum of the squares of every listed residual**.
It is not their product and not their unsquared sum. Since every value is
an integer, its zero set is exactly the common zero set of the 162 rows.

`expanded_polynomial.json` uses the same term convention for the fully
collected quartic. Its monomials have length at most four. It includes all
7,867 nonzero terms, including the constant term. Coefficient height means
the maximum absolute integer coefficient after collection.

`METRICS.json` is independently recomputed by `verify.py`.
`variables.tsv` records the ordered provenance names.
`residual_labels.tsv` records the ordered row labels and support sizes.
`residuals.txt` is an explicit human-readable arithmetic specification;
`report/residuals.tex` is its independently parsed mathematical counterpart.

The stored semantic translations inherited from the centered source must
not be inferred from variable names alone. For example, the coordinate
named `pow2.output` represents `q+1`, while the actual radix is that
coordinate minus one; `crt.encoded.a` represents `a+1`. After the beta
contraction, `pow0.output=V=y+1`. The transformation certificates and
frame checkers explicitly authenticate these offsets.
