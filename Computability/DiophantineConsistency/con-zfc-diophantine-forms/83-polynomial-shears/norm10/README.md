# Ten integer equations by polynomial shears

The complete literal graphs use ten unrestricted integer variables and
the same twelve actual fixed integer leaves as the pinned Round11 H1868
norm-saturated predecessor. No source or calibration parameter changes.

| Variant | Exact degree | Live binary operations |
|---|---:|---:|
| Predecessor | 1,245,324 | 480 |
| `integer10_linear.json` | 1,179,788 | 484 |
| `integer10_cubic.json` | 1,114,252 | 487 |
| `integer10_sixterm.json` | 1,081,125 | 521 |

The new polynomial is literally `P_old(v,m+R(v))`. The inverse map is
`m_old-R(v)`, over all integers, so existence equivalence needs no new
positivity or canonical-witness premise. The full proof and explicit
formulas are in Sections 2--4 of `../report.pdf` / `../report.tex`.

For the two short variants, respectively,

```
R = 2 A E G H
R = 2 A E0 (D-2 C^2) G H.
```

The degree reduction is certified by exact radical-core identities and
the lower-degree defect `a1-R^2`. The six-term formula has 26 monomials
in `(halfA,B1,C,xi,y)`. Its full defect certificate is supplied. The odd
degree of the unchanged cross term proves that its degree is minimal
among all polynomial translations of the last coordinate with the four
norm inputs fixed. This is only a restricted-family optimum.

Run `python3 build.py` to regenerate the three graphs. Run `python3
verify.py` for the standard-library exact algebra/data/graph/degree checks.
`audit_independent.py` uses SymPy and imports neither the builder nor
the standard verifier. Optimized Python is supported.

The JSON field `degree_upper_bound` records the naive unreduced DAG
bound. It intentionally remains 1,245,324: the exact degrees are lower
because of proved cancellations, and are recorded in `exact_degree`.
Changing that syntactic field to a smaller unjustified value would hide
the essential proof.

The inherited mathematical proof and packing interface are retained under
`upstream/`. Actual coefficient leaves, complete source kernels and ports,
and their checksums are included. The unbounded native/compiler/refutation
calibration is inherited, not inferred from finite arithmetic checks.
