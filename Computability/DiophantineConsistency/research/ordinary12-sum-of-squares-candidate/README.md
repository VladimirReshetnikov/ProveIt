# A 94-operation free-J candidate

Replace the 95-operation parent's final expression
`(1 + A0) * (1 + A1) * (1 + N) - 1` with
`A0*A0 + A1*A1 + N*N`. The common prefix has 89 live operations;
the new tail uses five, giving 94 live operations: 53 multiplications,
24 additions, and 17 subtractions. The 12 witnesses and the four fixed
coefficient ports are inherited. This candidate optimizes operation count,
not degree: its degree is 84, compared with the parent's stated 70.

`FreeJSumSquares.lean` defines the three residual expressions by projecting the
right operand of the three existing `1 + residual` factor expressions and
constructs their sum of squares. `zero_iff_literal` proves that the new
expression and the old literal vanish at the **same valuation** in every
`IΣ₁` model, without requiring positivity of that valuation. Its proof uses
`FreeJCompletenessFactorBridge.zero_iff_factor_units`, `internalZero_iff`, and
the order and no-zero-divisors structure on `DiffRing V`. This is a Lean
model-level theorem with fixed integer ports as parameters, not a syntactic
internal derivation in iPRA. The accepted author check is
`observations/attempt03/`; its log reports `[propext, Classical.choice,
Quot.sound]` and no warnings or `sorryAx`. The earlier failed attempt01 and
warning-bearing attempt02 are retained. The receipt checks direct and
companion guards and inherited provider inventory before and after; it does
not establish their entire historical source-to-object ancestry.

`check_lean_graph.py` separately compares the pinned Lean literal source with
`candidate.json`: all 89 common rows, the old six-row factor tail, the new
five-row square tail, the 12 variable indices, four port indices, and the
residual projections. `observations/graph-check01/` records a successful run.
This is an external text/JSON check; Lean has not proved an equality between
its expression and the JSON file, a PDF, or any decoded coefficient file.

## Degree evidence

`build.py` checks the pinned parent graph and coefficient binding and generates
`candidate.json`. The ordinary syntactic degree bound is 104. For a sharper
bound it checks by expansion over `ℤ[Q,V,n]` the identity

```
h = (1-Q)*(V+n)^2 + Q*V^2 - 1
  = (V+n)^2 - 1 - Q*n*(2*V+n).
```

The pinned graph has `deg Q ≤ 6`, `deg V ≤ 6`, and `deg n = 1`, so
`deg h ≤ 13`. The graph then gives `deg den ≤ 8`, `deg polarT ≤ 12`,
`deg polarA ≤ 21`, `deg polarCorrection ≤ 38`, and `deg N ≤ 42`.
As `deg A0 ≤ 16` and `deg A1 ≤ 14`, the output degree is at most 84.
For the matching lower bound, the script decodes each hash-pinned retained
coefficient, reduces it modulo 1,000,000,007, and substitutes `(i+2)*t`
for witness number `i` starting at zero. The resulting univariate polynomial
has degree 84, with leading coefficient 436671052 modulo that prime. Thus the
integer polynomial has exact total degree 84. The complete output is in
`observations/build01/stdout`. Both the coefficient decoding and degree
computation are external checks; they are not Lean theorems about the files.

The graph builder and the graph comparison can be repeated with
`python3 -I -S -B build.py` and `python3 -I -S -B check_lean_graph.py` from
this directory. The Lean runner uses pinned temporary providers, which must
still exist to replay it. The candidate does not complete the end-to-end iPRA
consistency equivalence, the coefficient-file binding, or the PDF binding.
