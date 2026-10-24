# Nine-auxiliary ordinary power graph

The completed result is an ordinary polynomial for positive exponentiation:

- One request m=n^k: **9 auxiliary natural variables, exact degree 20**.
- Two simultaneous requests: **13 auxiliaries, exact degree 32**.
- Two-request lower-degree sibling: **14 auxiliaries, degree at most 24**.

The inputs n,k,m are not counted as auxiliaries. Thus the first polynomial
has 12 variables in total, with n,k>=1 and m>=0. Substituting n=n0+1 and
k=k0+1 expresses the positive-domain contract using natural coordinates.
Every variable is listed in the literal JSON DAG. Only ordinary integer
polynomial operations occur; there are no hidden exponentiation graphs.

The structural step is a signed elimination of a shared Pell base.
Negative values are not forbidden by an extra witness: an elementary
factorization proves that this branch can represent only the already
correct exponent-one identities. Full proof: PROOF.md. Concise report:
standalone.pdf and section.tex.

## Ordinary tiling composition, not a consistency endpoint

The previously uncompiled two-power strict-boundary tiling certificate
now has a literal 21-natural-variable ordinary composition (or 22 variables
at lower degree). The four-corner fixture is fully emitted. Its actual
syntactic degree bounds are 6920 and 4616 respectively, including all
substituted ports. No graph's standalone degree is copied through a
high-degree substitution unchanged.

This is **not a new 21-variable Con(ZFC) equation**. A correctly initialized,
strict-boundary tile set calibrated to a ZFC proof checker remains absent.
In particular, the raw 943-tile list cannot simply be substituted: it
contains an all-zero tile, giving a trivial one-cell strict rectangle.
The current calibrated 9/10-positive and 11-integer frontiers are not
claimed improved by this component.

## Artifacts and reproduction

- POWER_ONE_9AUX.json: full degree 20 ordinary polynomial, four residuals.
- POWER_TWO_13AUX.json: shared graph, six residuals.
- POWER_TWO_14AUX.json: retained-base lower-degree sibling.
- FOUR_CORNER_21NAT.json and FOUR_CORNER_22NAT.json: complete compositions.
- METRICS.json: whole-DAG counts, bounds and artifact hashes.
- SOURCE_PINS.json and prior/: exact reviewed mathematical dependencies.
- check.py: separately transcribed evaluator, full positive/negative
  exponent-one witnesses, shared CRT fixtures and corruption controls.

Run from this directory, with Python 3.11 or newer and no third-party package:

    python build.py --check
    python -O build.py --check
    python check.py
    python -O check.py

Both normal and optimized modes pass. Checks use explicit exceptions, not
assert statements, so optimized mode does not disable them. The universal
proof, not finite testing, establishes the graph theorem. No new Lean run,
formal internal ZFC proof, proof of consistency, or global optimality is
claimed. All delivered artifacts are local; no external state was changed.
