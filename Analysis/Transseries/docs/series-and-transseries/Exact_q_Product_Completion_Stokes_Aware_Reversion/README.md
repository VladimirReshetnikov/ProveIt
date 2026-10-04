# Exact q-Product Completion and Stokes-Aware Transseries Reversion

Research article prepared for Vladimir Reshetnikov, 4 October 2026.

The package contains a 32-page article developing complex, sectorial transseries
reversion from exact q-product completion data. It includes conventional proofs,
all-orders recursions, a numerical verification program, and twelve research
questions.

## Files

- `article.pdf`: compiled article, with linked contents and references.
- `article.tex`: standalone editable source; the bibliography is embedded.
- `verify.py`: independent product/Borel comparisons, exact symbolic checks,
  and completed q-gamma critical-point and inverse-layer tests.
- `verification_results.json`: captured output at 150 decimal working digits.
- `requirements.txt`: the two Python dependencies and tested versions.
- `PROOF_REVIEW.md`: internal proof audit and boundaries of the claims.
- `SHA256SUMS.txt`: hashes of the other distributed files.

## Main results and reading route

Sections 3-4 derive an explicit meromorphic Borel kernel and the exact
Mellin-Borel completion of `log((exp(-a*t); exp(-t))_infinity)`. Both lateral
representations and their contour signs are stated. The proof specializes to
the nonsingular scalar identity stated as Conjecture 5 in Fantini-Rella,
arXiv:2506.08265v2 (1 April 2026), for `1 <= k < N`. The degenerate endpoint is
handled separately through the regularized eta transformation. This is a proof
of the specified identity, not an assertion of first-publication priority.

Section 5 classifies finite shift weights by reflection: antisymmetric weights
have exact linear-median reconstruction; symmetric weights have no perturbative
Stokes jump. It also bounds cancellation of initial exponential actions.

Sections 6-7 state the precise formal and analytic inverse hypotheses, transport
completion and Stokes data, and develop regular q-cusp inverses. In the
nondegenerate logarithmic target coordinate, the exponential action is 24.
An odd quotient cancels the linear core and produces a double-exponential
inverse Stokes scale. The general inverse-transport machinery is credited to
classical Lagrange inversion and the preceding ProveIt work.

Sections 8-9 compute the exact q-gamma completion, the exponentially displaced
critical point and critical value, and uniform inverse branches in the critical
layer. The forward scale `exp(-4*pi^2/t)` becomes `exp(-2*pi^2/t)` in this layer.
The completed quadratic normal form, rather than the regular perturbation
series, covers the actual branch point.

Sections 10-12 delimit root-of-unity applications, prove a conditional
finite-multiplicity action-selection principle, and give constructive all-orders
recursions. Section 13 reports tests. Section 14 contains twelve research
questions. The appendices record residue signs, proof checks, and provenance.

## Build the PDF

Use a TeX installation providing the packages listed at the top of `article.tex`,
including `newtxtext`, `newtxmath`, `tcolorbox`, `cleveref`, and `xurl`.
No local font or image files are required. From this directory, run:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Run another pass if LaTeX asks for it. BibTeX is not needed. The delivered PDF
was built successfully with pdfTeX/TeX Live; its final build had no undefined
references, overfull boxes, underfull boxes, or LaTeX warnings. All pages were
rendered and visually inspected in contact sheets, with detailed inspections of
the abstract, critical inverse formulas, numerical tables, and references.

## Reproduce the checks

Use Python 3.10 or later:

```text
python -m pip install -r requirements.txt
python verify.py --dps 150 --output verification_results.json
```

The program performs 19 exact finite symbolic assertions. The first numerical
group computes the original product and an accelerated principal-value Borel
sum independently. The second group uses the independently checked completion
to test critical-point and inverse-branch formulas. Domain validation and
iteration limits are included. All constants are computed at the active
precision; test inputs use decimal strings or exact rationals.

The captured run reports `all checks passed`. Working at 150 digits does not
mean that every approximation has a 150-digit accuracy guarantee: truncation
errors are reported explicitly. The numerical results are not interval
certificates or substitutes for the analytic proofs.

## Scope and provenance

The repository comparison is pinned to ProveIt commit
`b484725c893a7a9bde856151988996aef6965cb0`. It is a focused statement-level
comparison, not an audit of the entire repository. No repository files were
modified by this deliverable.

The article distinguishes its direct derivations from established Borel and
resurgent closure, Lagrange inversion, eta transformation, and analytic normal
form results. It does not assert a universal global inverse for every complex
transseries, nor a complete classification at arbitrary cyclotomic cusps.
The proofs have not been Lean-checked or independently refereed. An exhaustive
literature-priority claim is not made. See `PROOF_REVIEW.md` for further details.
