# Thue–Morse Frontier Deductions

*Boundary Corrections, Dyadic Completion and Mellin Renormalization, Rational
Resonances, Spline and Lattice Corrections, and Nonlinear Prouhet Geometry* —
a consolidated companion volume to
[`../Thue_Morse_Atlas_and_Frontiers/`](../Thue_Morse_Atlas_and_Frontiers/).
Assembled 2026-09-04/05.

## What this package is

One document replacing the six Thue–Morse research reports that arrived on
2026-09-04 (`Thue_Morse_Boundary_Corrections/`, `Thue_Morse_Dyadic_Completion/`,
`thue_morse_research_article/`, `Thue_Morse_Rational_Resonances/`,
`Thue_Morse_Research/`, `Thue_Morse_New_Directions/`, all deleted after the
merge; Git history retains them). The two dyadic-completion reports built the
same object and are merged into one part in one notation; the other four
overlapped only in the preliminaries, which a common first chapter now states
once with proofs.

- `Thue_Morse_Frontier_Deductions.tex` — 9,800-line book-class source: a
  preliminaries chapter, five parts (67 chapters), nine appendices. Loads
  `docs/fabius-notation.tex` by relative path.
- `Thue_Morse_Frontier_Deductions.pdf` — 199 pages A4, three `pdflatex`
  passes; the log passes `scripts/logcheck.py` and `scripts/audit_overfull.py`
  with zero overfull boxes.
- `figures/`, `tables/` — the five figures and the generated Poisson table
  the sources shipped, renamed by part.
- `verification/source1..6/` — the six verification programs, unchanged, with
  the outputs of their recorded runs (Part I: 19,037 exact rational checks;
  Part II: two independent high-precision programs at 60/80 digits;
  Part III: 408 exact cyclotomic-field checks plus 65-digit experiments;
  Part IV: 3,796 exact checks; Parts I/V: 2,800 exact assertions plus 80-digit
  saddle checks). Requirements files are beside the programs that need
  `mpmath`/`sympy`.

## Structure

| Part | Content | Source |
| --- | --- | --- |
| 1 | Common preliminaries: signs and block identities, finite product and `E(z)`, Prouhet cancellation, the Laplace product `P` and its flatness, the uniform sum `X` and its transform `Φ` (dilation, reflection, zeros, Fabius equation, lower bound), Bernoulli expansions, the centered up-function, Bell and partition polynomials, notation dictionary | editorial, from all six |
| I | Signed Stern boundary term, positive two-level correction, distributional first correction, analytic defect and binary partitions, Poisson bounds, dyadic energies, sharp Sobolev rates, amplitude family; boundary defects for correlations of every order | Boundary_Corrections; New_Directions (correlation chapter) |
| II | Completion `K=PΦ`, entire Mellin transform and periodic factor, Dirichlet continuation and real zeros, exact rescaling and coefficients, uniform expansion with explicit tube constant, zero strings, centering and signed remainders, coefficient asymptotics, Gaussian localization, lognormal twins, Hankel and orthogonal polynomials, flat twins, classification of completely monotone dyadic solutions, universal coefficients and beyond-all-orders ambiguity, boundary uniqueness of the gamma tower, other bases, Fourier profile, numerics | Dyadic_Completion (spine) merged with research_article |
| III | Rational profiles, cumulants, zeros, twisted moments and progressions, dyadic zero removal, coalescing-root Gaussian–Fabius hierarchy, cyclotomic aggregation, regularity classification | Rational_Resonances |
| IV | Derivative-copy geometry, coefficient calculus, global spline corrections, exact dyadic stabilization and Richardson reconstruction, lattice-to-spline conversion, local-limit expansion, dyadic stopping, energy moments and their twins, geometric extension | Research (New Deductions) |
| V | Covering-family identity, hafnians, matching-polynomial crossover, the flat product `Φ_q(z)`, its periodic amplitude as the Part II profile, Lambert-W saddle expansion, boundary layer and Woods–Robbins products | New_Directions |
| A–I | Per-part formula sheets, coefficient registers and ledgers; provenance, notation dictionary of the merge, verifier index | sources; editorial |

## Relation to the atlas

The atlas is under concurrent editing by other sessions, so the consolidation
is filed beside it rather than folded in. Folding is a follow-up; each part
names the atlas material it extends (the finite autocorrelation recurrences,
the strong spline-correction conjecture of the atlas's Part II, the automatic
Barnes hierarchy frontier, the Laplace-product and Mellin–Dirichlet chapters)
and the formalization route its source proposed. No Lean files were added.

## Build

```text
pdflatex -interaction=nonstopmode -halt-on-error Thue_Morse_Frontier_Deductions.tex
```

three times, from this directory. Run each verifier from inside its
`verification/sourceN/` directory as the part's verification section describes.
