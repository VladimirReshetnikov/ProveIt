# Strict horizons and free quotient scales

**Four explicit Diophantine equations for `Con(ZFC)` — 25 October 2026.**

This package supplies complete ordinary integer polynomials, mathematical
proofs, exact algebraic verification, and retained source dependencies.
For each equation, the supplied proof and identified inherited calibration
establish the following equivalence in ZFC:

> The equation has no solution in its stated domain if and only if ZFC is
> syntactically consistent.

The principal result is a **quartic in 236 unrestricted integer variables,
with 4,876 collected monomials and coefficient height 7,968**. Its construction
uses the direct numerical C222 calculus route. A separate compact construction
provides a **degree-278 polynomial in ten strictly positive integer variables,
computed by 89 binary arithmetic operations**, retaining the fixed coefficient
encoding of its compact native parent.

## Which equation to use

Use **`direct/principal236/`** as the main small-coefficient equation. Its
complete definition is

\[
P_{236}(x_0,\ldots,x_{235})
   =\sum_{j=0}^{172}R_j(x_0,\ldots,x_{235})^2=0,
\qquad x_i\in\mathbb Z,
\]

where every quadratic residual is supplied literally in `equation.json`,
and every coefficient of the collected quartic is supplied in
`expanded_polynomial.json`. The residual registers introduce no additional
quantified variables. The dense companion uses one fewer integer variable.

| Direct quartic | Integer variables | Quadratic residuals | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Matched factorial-free parent, principal | 242 | 178 | 5,018 | 7,968 |
| **New principal** | **236** | **173** | **4,876** | **7,968** |
| Matched factorial-free parent, dense | 241 | 177 | 12,774 | 7,968 |
| **New dense companion** | **235** | **172** | **12,566** | **7,968** |

Both new direct equations have exact degree four. Each removes six variables
and five residuals from its matched parent while also reducing support at
the same coefficient height.

Use **`compact/equation_89_degree278.json`** when the size of an arithmetic
expression is the main metric. Its companion offers fewer operations:

| Compact equation | Strictly positive integer variables | Binary operations | Exact degree |
|---|---:|---:|---:|
| `equation_83_degree312.json` | 10 | 83 | 312 |
| `equation_89_degree278.json` | 10 | 89 | 278 |

The compact equations include four large fixed integer coefficients, whose
complete payloads and finite reconstruction are retained. Their operation
counts do not measure the bit lengths of those coefficients. The direct
and compact tables therefore describe distinct notions of simplicity and
different solution domains.

## The mathematical changes

The direct construction chooses its proof horizon strictly beyond every
local schema parameter and derived label. This allows five range tests to
share the existing `q^t` denominator and removes the separate `q^(t+1)`
certificate. Exact coefficient bounds allow the growth majorant `F=t^t`;
an elementary least-common-multiple estimate allows the CRT radius `F`;
and signed binomial recovery permits the affine radix condition `q=4z+1`.
All powers and binomial expressions in this explanation are proof notation:
the delivered equation contains only integer polynomial operations.

Constructive completeness chooses an **even** cofinal parameter `h` in
`t=16+h^2`. This makes `F=t^t` sufficiently divisible by two and keeps
`binom(F+t,t)` odd, preserving the simultaneous canonical CRT and Pell
witnesses. Earlier retained notes concern earlier choices of the growth
majorant; the current proof records the required parity choice.

The compact construction sets the quotient `Y=s` and moves its former scale
into the Pell bases through `lambda=q`. This reduces the degree of a heavily
reused expression. The proof restores the missing divisibility after the
exponential projection, and constructs fresh witnesses at the new scale.

## Reading and verification

Start with **`report/main.pdf`**, with editable source in **`report/main.tex`**.
The literal direct equations are in `direct/principal236/` and
`direct/dense235/`; the compact equations and their full proof are in
`compact/`. Transformation certificates, independent reviews, and exact
verification receipts accompany the data.

Run the package checks from this directory:

```sh
python3 -B verify.py
python3 -B -O verify.py
```

The algebraic checks authenticate the finite equations and transformations.
The ordinary proofs supply the unbounded arithmetic and constructive
existence arguments. This release supplies no new end-to-end Lean/Rocq
formalization or encoded internal-ZFC proof.

## Sources, credit, and status

The comparison snapshot is ProveIt commit
`7a8da414376a80b90ecf799f37ceb26fb9ac674e`. The direct family builds on
**Factorial Free Binomial CRT**, incorporates the signed-radix method of
**Shared Factorial Error**, and retains the earlier C222, Pell, normalized
remainder, and exact-elimination dependencies. The compact family builds on
**Cofinal Witnesses and Centered Carriers** and **Lucas Corrections and
Witness Elimination**, retaining their native/BFS943 coefficient encoding
and its machine ancestry. The direct route does not require K215 or Jones'
universal polynomial as its encoding source.

The required source closure, coefficient payloads, licenses, and notices are
retained under `sources/` and `compact/upstream_lucas/`. The work was prepared
with AI assistance. These are proved improvements over specified matched
constructions, with explicit inherited dependencies; no global minimum,
historical priority, or proof of `Con(ZFC)` itself is claimed.

See **`INTEGRATION.md`** for suggested ProveIt incorporation. This package
does not modify or publish to the repository.
