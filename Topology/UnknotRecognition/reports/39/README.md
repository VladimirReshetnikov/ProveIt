# Compressed knot groups and degree-budgeted SU(2) recognition

Research continuation for `VladimirReshetnikov/ProveIt`, 8 October 2026.

The article proves a complete representation-feasibility reduction with cost
`poly(N) (Delta+2)^{O(r+c)}` for an explicitly checkpointed group presentation.
It also proves and implements a stronger special result: exact noncommuting
traceless SU(2) feasibility on **two certified meridian generators** is polynomial
in the **compressed** presentation size. A word is evaluated as an integer
exponent and two parity bits; a gcd and parity criterion replace real elimination.

This is a research-stage addition, not a replacement for `fastunknot`.
The general multivariate path compiles exact formulas but does **not** implement
the singly exponential real-feasibility algorithm invoked by the theorem.
No general quasi-polynomial bound for the maintained recognizer is proved.
No full upstream regression suite or whole-recognizer benchmark was run.

## Contents

`article.pdf` and `article.tex` contain the proofs, complexity conditions, measured
results, source audit, limitations, and fourteen further research questions.
`code/su2budget/` is a standard-library Python package. `tests/`, `experiments/`,
`examples/`, and `data/` contain tests, independent implementations, replayable
certificates, complete inputs, and raw measurements. `INTEGRATION.md` describes
the proof obligations at the proposed repository call sites.

## Run

Python 3.10 or newer is required. Recorded runs used CPython 3.13.5.

```sh
PYTHONPATH=code python -m unittest discover -s tests -v
PYTHONPATH=code python -m su2budget two-meridians examples/trefoil.json
PYTHONPATH=code python -m su2budget two-meridians examples/compressed_torus_1024.json
PYTHONPATH=code python -m su2budget univariate examples/figure_eight.json
PYTHONPATH=code python -m su2budget wolfram examples/trefoil_nonmeridional.json
```

The command `wolfram` **emits** an exact real query; it does not execute a solver.
The last presentation has nonmeridional generators, so the two-meridian commands
correctly reject it rather than falsely concluding that the trefoil is trivial.

```sh
# Optional independent validation; requires SymPy (recorded version 1.14.0).
PYTHONPATH=code python experiments/validate_independent.py
# Paired presentation-level timing, not a whole-recognizer benchmark.
PYTHONPATH=code python experiments/benchmark.py
PYTHONPATH=code python experiments/make_artifacts.py
# Requires a standard LaTeX installation with pdflatex.
sh build.sh
```

`reproduce.sh` runs all local checks and rebuilds the article. Reproduction
replaces measured timing files with new machine-specific samples. Copies of the
delivered files can be checked using `sha256sum -c CHECKSUMS.sha256` before reruns.

## Safety contract

An `EXISTS`/`NONE` result is about a specified representation slice.
Only a caller that independently verifies the original **one-component knot**,
the entire presentation transformation trace, and the meridian identities may
convert it to `KNOTTED`/`UNKNOT`. The JSON Boolean `meridian_generators` is only
a declaration of a precondition, not its proof. It is intentionally not a
self-authenticating topology flag.

`UNKNOWN`, a failed seed search, a malformed input, a solver timeout, or a
numerical failure is never interpreted as infeasibility. An unrestricted
Whitehead move does not automatically preserve meridian provenance. An ordinary
generator-rank bound is not a meridional-rank bound.

Integer and polynomial replay start from the source presentation. They share
arithmetic code with their producers; they are not separately formalized proof
checkers. Independence is supplied by symbolic matrix and rational-quaternion
comparisons. Hard memory containment and adversarial-file sandboxing are not
implemented; the resource caps are cooperative arithmetic/allocation guards.

## Results delivered

All 30 unit-test methods pass. Their internal checks include 8,000 triple
associativity cases, 640 rational-quaternion comparisons, 300 integer/univariate
presentation comparisons, and 400 propagation/relaxation comparisons. Separate
SymPy validation passes 115 independently compiled matrix presentations and 200
Sturm comparisons. Exact Wolfram checks and the service's warning are preserved.

Capacity tests include a 10,005-node presentation encoding the torus parameter
`2^10001+1`. This is compressed algebraic input, **not** an explicit diagram with
that many crossings. Timing comparisons are against the included univariate
reference, not against the upstream recognizer.

## Suggested location

A non-conflicting initial integration location is:

`Topology/UnknotRecognition/research/su2-degree-budget-20261008/`

No existing report number or default pipeline behavior is assumed. A production
adapter should be added only after the call-site proof obligations and full
upstream tests in `INTEGRATION.md` have been completed.
