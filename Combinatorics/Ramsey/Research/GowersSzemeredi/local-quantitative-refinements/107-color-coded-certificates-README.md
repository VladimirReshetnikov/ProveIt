# Exact finite line certificates

Each JSON certificate records `q`, `s`, `m`, the construction method, and a list of affine lines. A line is represented by `arms`, `anchor`, and `direction`, each of length `m`.

Arms are labelled `0,...,s-1`. In block i, the field value on that arm is

```text
anchor[i] + lambda * direction[i],    lambda in F_q.
```

Field elements are labelled `0,...,q-1`. Prime fields use ordinary modular arithmetic. For q=4 the labels encode binary polynomials modulo `x^2+x+1`, not arithmetic modulo four.

Every archived line has one boundary point. Any torus point not lying on a listed line is implicitly a singleton cell. The checker verifies full disjointness, complete boundary coverage, and equality with the proved lower bound; the implicit complement does not hide an unchecked optimization step.

The archived examples are an elementary q=3, s=3, m=2 partition and a color-coded q=4, s=6, m=3 partition. Run `python3 code/verify.py` from the package root to regenerate these and all other reported tests.
