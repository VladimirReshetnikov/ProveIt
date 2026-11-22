# Constructive Gauss–Bonnet in intuitionistic primitive recursive arithmetic

This package proves a quantitative Gauss–Bonnet theorem for explicitly
presented finite triangulated metric surfaces. Boundary, corners, disconnected
surfaces, and nonorientable surfaces are included. The presentation supplies
primitive recursive rational names, quantitative C2 jets, positive margins,
compatible edge charts, and finite tangent-fan order certificates.

The interpreted smooth conclusion is

    integral_M K dA + integral_boundary kg ds + sum_corner_turns = 2 pi chi.

Boundary curvature uses the inward unit conormal. A second theorem includes
seam curvature and interior cone defects for general triangle metrics.

## Start here

- `gauss_bonnet_ipra.pdf`: the complete report.
- `paper/gauss_bonnet_ipra.tex` and `paper/sections/`: all LaTeX sources.
- `lean/Assembly.lean`: ambient rational assembly candidate.
- `lean/IPRABridge.lean`: small object-level arithmetic bridge candidate.
- `lean/Blueprint.md`: definitions and completion obligations.
- `sources/proveit_source_audit.md`: exact inspected repository paths and SHAs.
- `VALIDATION.md`: precise status of the proof, candidate code, and executions.

## Mathematical contribution

For an upper triangular coframe

    theta1 = a dx + b dy, theta2 = c dy,
    P = (b_x - a_y)/c, Q = (c_x + b P)/a,

the curvature density is `rho = P_y - Q_x`. Three explicit arctangent
branches on the standard triangle make the turning calculation telescope
exactly. A finite rectangular grid proves the needed Green identity and
tracks every approximation error. Global assembly uses only

    3F = 2Ei + Eb,  Eb = Vb,  2 chi = 2Vi + Vb - F.

For arbitrary rational residual tables, the central exact identity is

    C + B + Theta - 2 p chi = R - I + S,

with all terms defined in the report. The parameter `p` can be any rational;
the analytic routines subsequently supply a certified approximation to pi.

## Logical and formalization status

The main human proof is a **fixed-PR-program theorem schema conditional on
its explicit arithmetic presentation hypotheses**. It does not quantify over
all abstract real manifolds or posit a universal primitive recursive
evaluator. An unconditional concrete iPRA instance additionally requires
iPRA proofs of its input contracts.

**The new Lean files have not been compiled.** No Lean, Lake, or Elan
executable was available in the authoring environment. The files have no
admitted proof declarations or new axioms, but this is not a kernel-check
receipt. The full analytic and mesh derivations remain the formalization
work described in the report. Python and symbolic tests do not replace them.

Inspected ProveIt commit:

    d36b35eed5bd01af4ade66bf539622495813ccc8

The inspected repository specifies Lean 4.32.0. Use its own dependencies
when integrating the candidate files; see `lean/README.md`.

## Reproduce the reference checks

Python 3.12.14, SymPy 1.14.0 and mpmath 1.3.0 were used for the recorded run.
The first two scripts use only the Python standard library.

```sh
python3 tools/finite_certificate.py > tools/finite_certificate_results.json
python3 tools/discrete_green.py > validation/discrete_green_results.json
python3 tools/smooth_examples.py --output examples/smooth_results.json
```

The tests cover:

- valid sphere, disk, annulus, torus, and projective-plane triangulations;
- invalid links, duplicate faces, and an invalid optional orientation certificate;
- exact arbitrary rational assembly tables and equilateral cone metrics;
- exact FTC and discrete Green telescopes, sharp error examples, rounding,
  deliberately reversed boundary orientation, and false cell contracts;
- a nonflat conformal triangle with exact rational integrals;
- 34 finite symbolic identities for a spherical octant, plus independent
  numerical quadrature diagnostics at 50 working decimal digits.

The reported floating-point zeros are agreement at the working precision,
not interval error certificates.

## Build the report

With Tectonic and a complete TeX bundle:

```sh
cd paper
mkdir -p build
tectonic --keep-logs --outdir build gauss_bonnet_ipra.tex
cp build/gauss_bonnet_ipra.pdf ../gauss_bonnet_ipra.pdf
```

Or with a functioning TeX Live installation:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build gauss_bonnet_ipra.tex
cp build/gauss_bonnet_ipra.pdf ../gauss_bonnet_ipra.pdf
```

`make report` uses PDFLaTeX via latexmk; `make checks` runs the reference checks.
The report uses no external images or bibliography processor.

Date: November 21, 2026 (America/Los_Angeles).
