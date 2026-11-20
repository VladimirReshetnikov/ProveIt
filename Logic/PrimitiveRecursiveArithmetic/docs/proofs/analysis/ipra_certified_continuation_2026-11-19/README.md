# Certified perturbation and continuation in iPRA

Research report for Vladimir Reshetnikov, 19 November 2026.

**Start with `ipra_certified_continuation.pdf`.** Its complete source is
`paper/main.tex` and the included section files. The report is self-contained
at the mathematical level and gives the numerical encodings, finite algorithms,
proofs, admissibility conditions, and an implementation plan for literal iPRA
derivations.

## Main results

1. **Cyclic quantitative contracts.** A nonnegative rational gain matrix `A`
   and a positive rational weight vector `w` satisfying `2 A w <= w` give
   finite contraction, residual comparison, perturbation, and inexact-iteration
   theorems. An explicit geometric clock produces rational Cauchy names.
   The proof handles coupled computations even when an unweighted row sum
   exceeds one.

2. **A polynomial certificate compiler.** Finite coefficient lists produce
   the gain matrix by exact monomial difference bounds. A checked inverse and
   center residual yield a PR algorithm for local implicit equations, with
   invariant box, Cauchy modulus, residual bound, uniqueness, and parameter
   stability. Jacobian preconditioning gives an automatic rational radius
   when its explicit residual test succeeds.

3. **Stable polynomial factor transport.** For an approximate coprime monic
   factorization, a verified Sylvester inverse supplies a convergent rational
   iteration. The report works out `X^2 (X-2)^2 + delta`: the inverse norm is
   `3/2`, radius is `1/6`, and `|delta| <= 1/18` is sufficient. This transports
   whole factors through root collisions *within* each factor.

4. **Corrected multiplicity and labeling interfaces.** Complete occurrence
   covers imply Hall inequalities and hence a computed matching with error
   at most the sum of the enclosure radii. Component balance alone yields a
   component-diameter bound; an exact counterexample has matching distance
   `14/5` despite edge threshold `1`. Stable reference locators replace
   complex lexicographic root labels.

5. **An actual linear-ODE producer.** The report derives the Euler recurrence
   currently assumed by the repository's `OdeRefinement` arithmetic layer.
   It proves interpolation, dyadic Cauchy convergence, input and coefficient
   sensitivity, and finite integral observations. Exact path clearance gives
   explicit Gauss hypergeometric transport data. The same rational companion
   construction applies to the stated Meijer G equations, starting from a
   supplied certified initial jet.

The report also explains why a redundant spanning set does not give an
intrinsic trace, while a finite multiplication matrix still yields an
annihilating polynomial under the stated Cayley-Hamilton premise.

## Relationship to ProveIt

The reviewed baseline is commit
`3ee850b4c2d650cf01263823fd5415963747c5d0` of
<https://github.com/VladimirReshetnikov/ProveIt>.

The current repository already has extensive checked bounded reflection,
realizer composition, finite demand closure, dyadic coherence, and numerical
DAG scheduling. This report builds on those facts and targets specific
remaining mathematical producer/interface gaps. Source URLs, hashes, and
the detailed audit are under `provenance/`.

## Verification status

**The human arguments prove the finite theorems under their stated
hypotheses. The new Lean files were not compiled. No newly checked
`Prf PRAAx` endpoint is claimed.**

`lean/FeedbackReference.lean` contains candidate ambient Lean proofs.
The other Lean files contain explicit definitions and named, unproved
`Prop` goals; they do not assert those goals as axioms or admit them as
proved theorems. `FeedbackObjectPort.md` and the report specify the separate
object-language programs, QF invariants, source interfaces, and endpoints.
There was no Lean compiler in the delivery environment.

All Python assertions use exact rational arithmetic. They provide
reproducible finite evidence and exercise counterexamples and constants;
they are not proofs of the universal theorems. Current counts and outputs
are in `verification/summary.json` and the four detailed JSON reports.

The remaining boundaries are explicit: arbitrary polynomial-root
multiplicity certificates are not generated, singular factor splits are
not transported by the inverse certificate, named special-function initial
jets and contour identities still require their own producers, and no
general Siegel/Faltings or unrestricted real-choice theorem is claimed.

## Reproduce the numerical checks

Python 3 with its standard library suffices:

```bash
python3 code/run_all.py
```

This regenerates the JSON evidence. The exhaustive graph check covers all
531 bipartite Boolean graphs with equal side size at most 3.

## Rebuild the PDF

```bash
python3 code/build_report.py
```

The script runs three LaTeX passes, checks that references resolve, and
creates `ipra_certified_continuation.pdf`. It uses an installed `pdflatex`;
it never downloads software. For the delivery environment's incomplete
generated TeX configuration, it can build the format and font map locally
inside `.build/` using the already installed TeX trees.

## Begin Lean checking

```bash
cd lean
lake update
lake build
lake env lean AxiomAudit.lean
```

The configuration pins Lean 4.32.0 and the baseline Mathlib commit. These
commands were not run successfully here and may reveal elaboration issues
to fix in the candidate source. Building this reference layer would still
leave the explicitly described object-iPRA port to do.

## Archive contents

- `paper/`: complete editable LaTeX source and bibliography.
- `lean/`: five reference/blueprint modules, umbrella import, axiom-audit
  commands, pinned Lake configuration, and implementation notes.
- `code/`: exact rational programs, verification driver, PDF build helper.
- `verification/`: computational evidence, build status, and PDF inspection.
- `provenance/`: inspected-source manifest and current repository audit.
- `CLAIMS.json`: claim-by-claim assumptions, proof location, and formal status.
- `SHA256SUMS.txt`: checksums of the delivered files.

No repository branch, commit, issue, or pull request was modified by this
research delivery.
