# Canonical Trace Polytopes

**Witness-Preserving Diophantine Representations of Computational Substrates**  
Research memorandum prepared for Vladimir Reshetnikov, September 30, 2026.

## Start here

- `article.pdf`: the complete article, proofs, examples, research agenda, and bibliography.
- `article.tex`: self-contained LaTeX source; the bibliography is embedded.
- `code/trace_polytope.py`: exact-arithmetic compiler and witness checker.
- `code/verify.py`: reproducible finite checks against independent semantic oracles.
- `code/demo.py`: small ordinary and zero-guarded examples.
- `results/`: exported sum-of-squares certificates, witnesses, and the full test receipt.
- `build.py`: cross-platform verification and PDF rebuild helper.
- `SHA256SUMS.txt`: checksums of the distributed files, excluding the checksum file itself.

## Main result

For a Petri net with `d` places, `m` distinctly labelled transitions, numerical
endpoints and an exact horizon `T`, the compiler constructs a convex quadratic
integer polynomial in

    (2*T + 1)*d + (7*T + 1)*m

nonnegative integer unknowns. Its entire natural zero set is in bijection with
the enabled length-T executions modulo a sound static commutation relation.
By default that relation is the maximal equality-of-partial-maps relation,
computed exactly from two-step resource demands.

The nonnegative real zero set is a bounded rational polytope; it need not be
integral. Every auxiliary variable has a unique value once the canonical word
is specified. An optional interval-upper-guard interface includes zero tests
and recomputes the correct guarded commutation relation. Each finite upper
guard adds one unique slack and one affine residual per time step.

A smaller quartic presentation and an unquotiented raw-run quadratic
presentation are also implemented. The article proves counting hardness,
Boolean-memory lower bounds, a closed-form example, and the equivalence
between fixed-dimensional finite-fold representation of a canonical universal
trace verifier and the general finite-fold conjecture.

## Scope and mathematical status

This is a bounded-horizon theorem package, not a claimed solution of the
finite-fold or single-fold Diophantine conjecture. The number of variables
grows with the supplied horizon. Classical trace-language and arithmetic
encoding ideas are explicitly attributed. Priority for the combined results
has not been established by an exhaustive literature review.

The article contains complete mathematical arguments, but its new theorems
have not been checked in Lean. Python tests are finite exact checks, not
formal proofs. The existing ProveIt repository was inspected, not rebuilt.
The implemented front ends are Petri nets, interval-guarded translations,
and a Boolean-circuit-to-safe-net reduction. The cellular-automaton and
bounded-rewriting front ends are described and justified mathematically,
not supplied as complete standalone translators.

## Reproduce the checks

Python 3.10 or later, standard library only:

    python -B code/verify.py
    python -B code/demo.py

Run the verification suite **without `-O`**, since its assertions are the
finite tests. The full receipt is written to `results/verification.json`.
The normal-form oracle constructs adjacent-swap connected components instead
of reusing the flag recurrence.

The reported full run includes 358,509 words over all 75 independence graphs
on alphabets of size at most four; a complete 65,536-assignment forced-height
box search; 729 guarded transition-pair checks; four circuit reductions;
and 160 closed-form counting comparisons. The receipt gives all exact scopes.
Wall-clock times and PDF creation timestamps are machine-dependent.

## Build the PDF

Install a standard TeX distribution containing the packages in the source
(including newtx, amsmath/amsthm, geometry, microtype, tcolorbox, hyperref,
cleveref, aliascnt, listings, and xurl). Then use:

    python build.py

This runs the finite checks and demo, then runs pdflatex three times.
`python build.py --verify-only` skips PDF creation;
`python build.py --skip-tests` rebuilds only the PDF.
No external bibliography tool or downloaded assets are required.

## Certificate format and API

`compile_certificate(net, initial, final, horizon, form='quadratic',
independence=None, upper=None)` returns a `Certificate`. `form` is one of
`raw`, `quartic`, or `quadratic`. An explicitly supplied independence relation
must be symmetric and contained in the exactly computed semantic relation.
The `upper` matrix contains natural upper bounds or `None` for infinity,
and has the same shape as the pre/post matrices. Finite upper bounds must
be at least the corresponding lower guard (`pre`).

The polynomial is represented as **the sum of squared residuals**. Each JSON
residual is a list of integer coefficient / variable-name-list monomial pairs.
A repeated variable name denotes a power. It is not the sum of the residuals.
Unknowns range over **nonnegative integers**, not arbitrary integers.

`cert.witness(word)` constructs the full unique natural assignment of a valid
canonical word. `cert.zero(assignment)` validates all variable names, domains,
and equations. `cert.decode(assignment)` validates and recovers the word.
`cert.energy(assignment)` evaluates the squared sum, but unlike `zero` it does
not enforce natural-variable domains. `cert.expanded_polynomial()` supports
small explicit expansions. No general integer or Diophantine solver is used.

The Python label indices are zero-based. A label identifies a transition;
transitions with identical effects but different labels remain distinct.
`Net.run` is the unguarded simulator. For additional upper guards use
`guarded_run`, or the certificate's witness/validation methods.

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected snapshot:

    e8bb0931d67f80d9fce87a8cddb0f661ff19f956

Primary interface:

    Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean

Pinned Git blob:

    08e5796b22fc85ef0cd97255dba8b7527960160b

The source proves `boundedForall_dioph`, `exactIter_dioph`, and
`existsExactIter_dioph`. Those are existential closure interfaces; they do
not assert the witness bijections proved in this memorandum. Immutable
source links and primary literature references appear in the article.
