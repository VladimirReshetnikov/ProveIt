# Small Divisors at Surreal Scales

**Resonance flags, analytic lifting obstructions, and Hahn normal forms**  
Research draft dated September 21, 2026. Prepared with ChatGPT.

## Contents

- `article.pdf`: the compiled, 26-page article.
- `article.tex`: complete standalone LaTeX source with an internal bibliography.
- `code/verify.py`: exact finite verification program; Python 3.9+ and the standard library only.
- `verification.json`: the recorded successful verification run.
- `RESEARCH_NOTES.md`: source-review scope and provenance.
- `SHA256SUMS.txt`: file-integrity hashes for this package.

## Main results

Theorem 4.1 constructs a finite resonance flag for a surreal frequency vector
and one well-ordered support containing every reciprocal nonzero Fourier
divisor. There are at most d visible divisor-valuation levels in dimension d.

Theorem 5.2 gives a necessary and sufficient stratified subexponential
arithmetic condition for universal solvability in a Hahn algebra whose
coefficients are all holomorphic on one fixed open torus strip.

Theorem 6.1 constructs, for every N >= 1, an entire forcing whose first N+1
solution coefficients are analytic, although the next forced coefficient is
not even a distribution. Enlarging the Hahn value group cannot repair it.

Theorem 7.1 constructs a unique normalized infinitesimal conjugacy of a
perturbed nonresonant vector field to a constant vector field with a frequency
correction. Its existence proof uses coefficient stabilization certified by
positive support words, not sequential valuation convergence.

Theorem 8.1 proves necessity of the arithmetic condition for a universal
nonlinear theorem, even for arbitrarily high-valuation perturbations.
Proposition 8.3 shows that the strict perturbation-scale threshold is sharp
as a uniform sufficient bound. Theorem 9.2 gives a canonical invariant density.

## Mathematical scope and status

These are proposed original results with detailed mathematical proofs, not a
claim to have solved a named longstanding conjecture. The exact theorem
package was not located in the focused literature review; this does not
establish literature-wide priority. The article identifies its classical
Hahn-series and small-divisor inputs explicitly.

The proofs have not been refereed or formalized in Lean. The included code
checks only finite exact identities. In particular, it is not a machine proof
of the infinite-support and analytic statements.

The torus derivatives are external derivatives annihilating the Hahn scalar
field. They are not the Berarducci–Mantova derivation on surreal numbers.
The nonlinear theorem gives a coefficientwise Hahn-analytic normal form;
it does not assert convergence after replacing a Hahn monomial by a nonzero
real perturbation parameter, and it does not improve classical real KAM
convergence arithmetic.

## Build the article

From the extracted package directory, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, `latexmk -pdf article.tex` can manage the repeated passes.
A standard TeX Live or MiKTeX installation with the packages named in the
preamble is sufficient. No external bibliography, images, fonts, or source
files are required. The delivered PDF was compiled with pdfLaTeX and
visually reviewed. Its final compilation log had no warnings, undefined
references, or overfull/underfull box diagnostics.

## Reproduce the finite checks

From the same directory:

```sh
python code/verify.py --output verification.json
```

The recorded run verified:

- the slow-circle conjugacy through degree 10, including reality and the
  mean-zero normalization;
- the independent frequency identity nu^2 = 1-r^2 through degree 10;
- 117 exact coefficient recurrences for (1+t+t^omega)^(-1);
- 1,330 nonzero integer modes in the three-scale resonance example.

All arithmetic is rational Gaussian arithmetic, with no floating point.
The script raises an assertion error if an identity fails.
