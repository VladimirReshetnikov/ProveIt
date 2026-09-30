# Finite-Scale Geometry of Surreal Liftings

**Sharp dependence compression, exact polynomial degree bounds, and linear
realization of finite combinatorics**

Research manuscript prepared for Vladimir Reshetnikov, 30 September 2026.

## Contents

- `article.pdf`: the complete mathematical article.
- `article.tex`: standalone LaTeX source with embedded bibliography and a TikZ figure.
- `code/verify.py`: exact finite checks; Python 3.10+ standard library only.
- `data/certificates.json`: reproducible rational certificates and test results.
- `data/verification_report.txt`: the executed verification summary.
- `SOURCES.md`: source provenance and comparison boundaries.
- `PROOF_REVIEW.md`: review checklist and limitations.

## Central result

For n real base points affinely spanning dimension d, let V be their real
affine-dependence space, q = n-d-1, and L_h(c) = sum(c_i h_i).
Let m be the real dimension of the image of L_h.

After an affine height is removed, m <= q selected Conway coefficient
slices preserve the exact leading term of EVERY real dependence evaluation.
The complete sign type is an oriented partial flag of length m.

For m > 0 its exact minimum polynomial-germ degree is m-1. For finite
heights with a prescribed standard part, the exact minimum is m-r_0,
where r_0 is the rank (0 or 1) of the standard-part dependence functional.
Preserving only finite lifted determinant/slack signs and the shadow instead
requires degree at most one. The discrepancy between these two degrees can
be arbitrarily large. For integral bases, finite Graver certificates let
the same linear path preserve the entire toric initial ideal.

The article also gives a canonical refinement hierarchy, counterexamples,
corrections to an earlier convexity draft, a coefficient-oracle
undecidability result, and eight further research projects.

## Reproduce the exact checks

Run from this directory:

```sh
python3 code/verify.py
```

The program overwrites the two generated files in `data/` with reproducible
results. The executed suite has 53 examples: 7 named, 6 sharpness-family,
and 40 randomized cases, plus 60 extra dependence tests per example.
Do not run with Python's `-O` switch: the tests use assertions.

The representation is a COMPLETE finite rational coefficient list for a
Laurent polynomial in a positive infinitesimal. No float comparisons, network
access, general surreal arithmetic, or proof-assistant trust is involved.

## Build the PDF

A normal TeX Live installation with newpx, amsmath/amsthm, microtype, TikZ,
hyperref, xurl, and the other packages listed in the preamble suffices.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The bibliography is embedded in `article.tex`; BibTeX is not needed.

## Research and verification status

The general results have written proofs, not new Lean formalizations.
Finite exact tests supplement those proofs and do not establish universal
statements by themselves. The manuscript's proofs have been checked during
preparation but not independently refereed.

Normal-form linear algebra, real-closed-field transfer, symbolic perturbation,
regular subdivisions, and Graver control are classical ingredients. The
article proposes a sharp unified lifting package; it does not assert
literature-wide priority or a solution of all higher-rank tropical questions.
The September 2026 revision of the higher-rank GKZ-fan paper is explicitly
included in the comparison.

The fixed REAL BASE is essential for the low-degree construction. Polynomial
models preserve dependence signs as germs, not actual surreal exponent
values. A single real specialization cannot preserve every real dependence
sign when m >= 2. Full coefficient support is not assumed computably
extractable from arbitrary surreal names.
