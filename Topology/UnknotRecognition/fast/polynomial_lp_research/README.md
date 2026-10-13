# Exact polynomial LP policy evidence

This package checks the maintained rational LP fallback and compares its default
policy with the explicit legacy Bland policy. It uses no Regina or numerical LP
dependency. Run commands from `Topology/UnknotRecognition` with `PYTHONPATH=fast`.

```
PYTHONPATH=fast python -m polynomial_lp_research.audit --output synthesis/data/polynomial-lp-audit.json
PYTHONPATH=fast python -m polynomial_lp_research.benchmark --output synthesis/data/polynomial-lp-benchmark.json
PYTHONPATH=fast python -m polynomial_lp_research.check_evidence
PYTHONPATH=fast python -m polynomial_lp_research.check_evidence --publication
```

Run the audit after all source files are stable. Run the benchmark separately
with other CPU work paused. The scripts reject a source change during a run.
They retain incomplete output with `passed=false` until the entire run passes.
The checker replays saved mathematical evidence and timing arithmetic; it does
not invoke LP discovery, crushing discovery, or new timing jobs.

The audit includes 15 small rational kernel cones, each queried with both row
policies and both LP policies. The polynomial queries force a zero-pivot prefix;
trivial conclusions can still require no fallback. The independent oracle
enumerates normalized vertices using Leibniz determinants and Cramer's rule,
imported from the pinned `tests/test_polynomial_exact_lp.py`. Every positive
answer is checked against original rows, primitive normalization, support
nullity one, and a nonsingular original slack basis. Every negative answer
replays its original-row dual inequalities. Cases include dependent rational
rows, unsorted pivots, three-dimensional cones, a genuine four-dimensional
negative query, and four seeded small random inputs.

Two additional three-dimensional bounded systems test a singleton and an exact
infeasibility gap. Twelve consecutive updates from each retain full exact
centers, shapes, and separating rows. Replay checks positive definiteness,
outward matrix containment by all principal minors, the spectral floor,
rational volume decrease, nested dyadic precision, and the center error bound.
The accepted perturbed center is labelled only as a decision witness; the
singleton's original feasible point is checked separately. Fifty-one signed
integer-square-root ceilings are verified by exact squared inequalities.

A fresh two-tetrahedron layered torus query forces genuine fallback through
transversal candidate restarts and produces a complete independently checked
negative tree. An authenticated partial crushing chain of the circle supplies
a one-tetrahedron positive sector; forced fallback, normal certificate replay,
support extraction, and a complete independently checked crushing continuation
are retained. These are finite implementation checks, not a structural bound
on all knot complements.

The benchmark uses complete circle, trefoil, and figure-eight transversal
queries, with three randomized paired samples, one Bland A/A pair, and batch
size one by default. `--pairs`, `--aa`, and `--batch` can increase those counts.
Construction, shelling, vertex reduction, discovery, internal replay, and full
JSON serialization are timed. Independent warmup replay is outside the timer.
Every timed result must hash identically to its arm's saved warmup. Cross-arm
full-result equality is required whenever neither arm invokes fallback;
otherwise both full outputs and their differing top-level fields are retained.
When fallback counts are zero, the timings measure common-path overhead and do
not establish a practical speedup for ellipsoid recovery.

Both evidence files pin every native Python module, every file in this research
package, and the exact fixture/oracle dependencies. No historical file is loaded
for the Bland arm: it is the current pinned solver's explicit comparison policy.
`check_evidence` writes `polynomial-lp-table.tex`. Its `--publication` mode also
pins the saved evidence, relevant tests, `exact_polynomial_lp.tex`, the enclosing
article, `report.pdf`, and the fast implementation README in
`polynomial-lp-publication.json`. Existing historical publication bundles are
independent and are not rerun by this package.

The uncapped polynomial LP theorem removes the Bland pivot obligation. The
remaining admissibility/transversal search still lacks a universal
quasi-polynomial bound.
