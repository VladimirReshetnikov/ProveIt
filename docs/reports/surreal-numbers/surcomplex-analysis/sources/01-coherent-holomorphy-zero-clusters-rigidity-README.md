# Surcomplex Analysis
## Hahn-Coherent Holomorphy, Zero Clusters, and Global Rigidity

Prepared for Vladimir Reshetnikov, 21 September 2026.

## Contents

- `surcomplex_analysis.pdf`: complete article with proofs, examples, and linked references.
- `surcomplex_analysis.tex`: self-contained LaTeX source; bibliography is included.
- `verify.py`: standard-library Python script for exact finite algebraic checks.
- `verification.txt`: output from an executed run of the script.
- `Makefile`: PDF build, verification, and cleanup commands.

The PDF and TeX are the primary deliverables. No external figures, font files,
BibTeX database, or other downloaded assets are needed to rebuild the paper.

## Mathematical organization

The article distinguishes full-surreal differentiability from Hahn summability
and from coherence of ordinary holomorphic coefficient functions. It develops
Cauchy and residue calculus, a constructive Hahn-Weierstrass preparation,
exact infinitesimal zero counts, local open and inverse mapping theorems,
multivariable implicit functions, and an all-scale polynomial rigidity theorem.
A separate global construction discusses the canonical surcomplex exponential,
explicit noncanonical phase twists, local logarithms, and the value distribution
of Exp(1/z).

Infinite sums are set-supported Hahn sums, not full-surreal limits of finite
partial sums. Contours carrying the H superscript are integrated coefficientwise
along ordinary complex paths. The conditions on domains and allowed changes
of scale are part of the statements, not implicit transfer assumptions.

## Rebuild the PDF

A normal TeX Live or MiKTeX installation with pdfLaTeX and the packages named in
the source is sufficient. From this directory, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_analysis.tex
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_analysis.tex
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_analysis.tex
```

Three passes stabilize the contents, cross-references, and PDF bookmarks.
Alternatively, run `make` or `latexmk -pdf surcomplex_analysis.tex`.

The original build was performed with pdfLaTeX. All pages were rendered and
visually reviewed, and the final build has no undefined references or overfull
box warnings.

## Run the exact checks

Python 3.9 or newer, no additional packages:

```sh
python verify.py
```

The script checks:

1. The infinitesimal Lambert-type equation through degree 40.
2. Hahn-Weierstrass preparation for w^2 - t*exp(w), through t-degree 7
   and w-degree 10, with additional internal Taylor precision.
3. The two-scale root expansion through degree 2 in the deeper parameter.

Every check uses rational arithmetic. These finite calculations verify the
worked formulas; they are not a formal proof of the general analytic theorems.

## Attribution and scope

Surreal normal forms, real-closedness, Neumann's support lemma, Alling's analytic
foundations, and the Ehrlich-Kaplan canonical surcomplex exponential are
established inputs, cited in the article. The article supplies proofs of its
stated structural results and precisely distinguishes them from those inputs.
It does not claim exhaustive literature priority or proof-assistant verification.
