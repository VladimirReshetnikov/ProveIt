# Linear-factor proof certificates with a coefficient budget

This component supplies a proved mathematical certificate theorem, a literal
local polynomial, and reproducible exact checks. It is **not a completed
fixed-dimensional Con(ZFC) polynomial** and makes no final variable-count or
degree record claim.

## New source idea

Use one factor `X+j` for every natural formula label `j`, including zero.
Respect each Horn rule's actual arity: axioms have no premises,
generalization has one, and modus ponens has two. Treat truth code zero as
an actual zero-premise axiom.

For rule `P_i -> c_i`, where the premise list has length at most two, put

```
B_i = product(1+p for p in P_i) + c_i
T_0 = 1
T_(i+1) = T_i B_i
M = T_N + 1
```

Then require

```
S_0 = M+1,   S_N = 1,
S_(i+1) (M+c_i) = S_i product(M+p for p in P_i).
```

The telescoped identity is `C(M)=(M+1)Q(M)`, where `C` is the product of
conclusion factors and `Q` the product of all actual premise factors.
Every coefficient of `C-(X+1)Q` has absolute value at most `T_N`: `T_N`
bounds both `C(1)` and `Q(1)`, and a coefficient of `(X+1)Q` is the sum
of two distinct coefficients of `Q`. Evaluation at `M=T_N+1` is therefore
injective for the zero test. Unique linear-factor multiplicities give exact
Horn flow. The single-conclusion flow theorem rules out circular fake
proofs. A genuine proof tree constructs both accumulators, with the budget
chosen before `M` and the obligation accumulator.

The full proof, beta-trace interface, optional normalized variant, and
limitations are in `section.tex`, included by the root `report.tex`.

## Exact local comparison

The new JSON retains the original 90 residual rows of the source-68 C222
Horn branches. It adds 26 quadratic residuals. The binary branch uses its
otherwise unused shared `q0,q1` slots for `S(M+p)` and `pq`; these do not
overlap with any other value in that branch. Other branches need no new
wire slots. This is the same unflattened branch-product representation as
the original source.

| Source-interface quantity | Source 68 | New source |
|---|---:|---:|
| Local existential coordinates | 23 | 20 |
| Exposed local coordinates | 4 | 5 |
| Local degree | 50 | 52 |
| Outer certificate coordinates | 5 | 4 |
| Bounded universal families | 2 | 1 |
| Beta outputs per local step | 2 | 4 |

The new source removes the separate common-multiple bounded family and
three label-bound slack coordinates. Its second accumulator increases the
number of beta values. Those extra graph costs must be included before
claiming a net improvement after compilation.

## Files and reproduction

Run Python 3 from any directory:

```
python3 /path/to/budget_certificates/build.py
python3 /path/to/budget_certificates/verify.py
```

No network or third-party Python packages are required. `build.py` reads
the supplied `horn_source_rows.json` and regenerates
`linear_budget_local.json` and `LOCAL_METRICS.json`. The provenance block
pins the exact repository commit, original path, and SHA-256 of the source
from which the unchanged rows were extracted. The source bundle's
historical field `quadratic_residuals` contains some quartic bundle rows;
the new artifact calls the field `residuals` and retains the exact rows.

`verify.py` independently reconstructs all factor expansions, checks the
unchanged source rows, validates exact natural fixtures against independent
constructor formulas, and exercises the coefficient lemma on all 60,880
small rule lists. `TOY_CERTIFICATES.json` contains artificial finite Horn
proofs, never an actual ZFC refutation. `CHECKS.json` records the results.
The expensive exact bundle fixtures manipulate integers up to about
1.6 million bits; the values are not serialized.

## Negative control

With `M=11`, the source consisting of rule `10 -> 3` and axiom `7` does not
derive `1`. Nevertheless `S=[12,18,1]` satisfies both multiplicative local
updates, since `14*18=12*21`. The base is larger than every label. The
budget `T=[1,14,112]` forces `M=113` and rejects this fake. Thus merely
asserting that a scale is large cannot replace the coefficient-budget
endpoint.

## Scope of the remaining work

The interleaved beta trace uses four outer coordinates `N,x,y,M`, with
`S_i=beta(x,y,2i)` and `T_i=beta(x,y,2i+1)`. It has one bounded universal
family of local zeros. To obtain a final ordinary polynomial one must
substitute the beta graphs, perform bounded-universal elimination, quantify
the outer coordinates, and measure the resulting polynomial. No artifact
here claims that work has already been done. The source uses the inherited
C222 calculus calibration; it is independent of K215 simulation and the
Jones finalizer, but not of that logical calibration.

This idea has been checked against sources 68 and 75 in the pinned
repository. No claim of first discovery in the wider literature is made.
