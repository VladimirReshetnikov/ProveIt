# Collision Geometry Is Linear

**Event-Sparse Quadratic Diophantine Certificates for Rational Signal Machines**  
Research manuscript prepared for Vladimir Reshetnikov's ProveIt program, 2 October 2026.

## Read

`article.pdf` is the compiled 29-page article. `article.tex` is its standalone
LaTeX source, with all bibliography entries and vector diagrams embedded.

The main construction turns a complete finite collision skeleton into an exact
rational linear chamber in the initial gap variables. It handles omitted earlier
collisions, additional simultaneous inputs, and independent simultaneous sites.
It uses at most `3(n-1) + (3m+1)E` raw conditions, where `n` is the initial signal
count, `m` the number of distinct velocities, and `E` the collision-site count.

From integer matrices `E` and `G`, the complete natural-number polynomial is

    P(g,z) = sum_i (E_i g)^2 + sum_j (G_j g - 1 - z_j)^2.

This is a convex quadratic and gives exactly one slack tuple per accepted integer
seed for a fixed skeleton. A finite disjoint first-acceptance family gives one
quartic with unique selector and slack witnesses. Additional results concern
causal-depth denominators, small integral realizations, robustness, bounded
synthesis, exact quasi-polynomial seed counts, and an obstruction to fixed-arity
universal compression within the globally nonnegative quadratic class.

## Reproduce

Requirements: Python 3.10+ (standard library only), and a LaTeX installation with
`latexmk` and the ordinary packages listed in the source.

    python code/run_checks.py
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

Alternatively, run `make test` and `make pdf` on a system with Make.

The exact checks passed **34,560 assertions**. The test command deterministically
regenerates the JSON exports in `data/`. The random tests use seed `20261002`.
No network access or additional Python packages are needed.

## Contents

- `code/signal_certificates.py`: immutable machine interface, independent exact
  all-pairs simulator, symbolic adjacency-interval compiler, polynomial evaluation,
  and finite-family quartic construction.
- `code/run_checks.py`: reproducible examples, counterexample regressions,
  witness tests, counts, inverse thresholds, and randomized cross-comparisons.
- `data/checks.json`: machine-readable test counts and resource ledger.
- `data/tournament_left.json`, `tournament_right.json`, `tournament_triple.json`:
  full integer matrices and event-coordinate forms for the three first events.
- `data/simultaneous_two_sites.json`: a complete simultaneous two-site example.
- `data/zeno_clock_24_batches.json`: all coordinate forms, depths, and the chamber
  for a 24-batch prefix of the four-speed clock.
- `data/first_hit_quartic_union.json`: complete matrix-based quartic for a disjoint
  two-chamber family.
- `PROVENANCE.md`: repository and literature scope.
- `SHA256SUMS`: checksums of the packaged files, excluding itself.

The JSON matrices define the entire polynomials, not only examples of zeros.
Rows are lexicographically ordered, so the order of slack variables can differ
from a displayed formula in the article. This is just a coordinate permutation.

## Scope and trust

These are research-manuscript proofs and exact finite computational checks, not
Lean-certified theorems or a formally verified compiler. Historical priority has
not been established. The published universal signal machine's full rule table
and input loader have not been reimplemented here; the compiler is generic, and
the package implements the worked machines described in the article.

A fixed skeleton and a fixed event budget are not the same thing as fixed-arity
unbounded Diophantine representation. The article makes no claim to solve
single-fold/finite-fold MRDP, to establish a new unrestricted universal polynomial
bound, or to improve the repository's fixed-universal operation ledger. The row
count is not a constant arithmetic-operation count.

Only ordinary finite prefixes are certified. An accumulation point is not given
an automatic continuation. Rational seeds can be scaled to integral seeds only
when that scaling is permitted by the geometric input specification.

No repository files were modified. No third-party papers or font files are
included in this archive.
