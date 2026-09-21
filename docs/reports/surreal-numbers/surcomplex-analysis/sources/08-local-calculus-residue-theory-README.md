# Surcomplex Analysis
## Local calculus, coherent Hahn functions, and residue theory

Prepared September 21, 2026.

## Files

- `surcomplex_analysis.pdf`: the compiled 33-page article.
- `surcomplex_analysis.tex`: complete, self-contained LaTeX source, including the bibliography.
- `verify_examples.py`: exact symbolic checks for selected examples.
- `verification.txt`: the recorded output of those checks.
- `README.md`: this guide.

## Main development

The article separates two mathematical structures:

1. Local Hahn analyticity over No[i]. Arbitrary formal power series have a
   realization at sufficiently small scales. The article proves calculus,
   Cauchy--Riemann, inverse and implicit function theorems, local ramification,
   formal residue identities, and local analytic ODE existence.
2. Coherent Hahn sections with ordinary holomorphic coefficient functions on
   one common domain and a common well-ordered support. Their canonical halo
   evaluation supports identity and maximum principles, Cauchy formulas,
   well-founded preparation and division, exact zero lifting, Rouche stability,
   moving-pole residue theorems, and an argument principle.

Affine charts carry the second theory to arbitrary surcomplex centers and
nonzero scales. Counterexamples explain why unrestricted global versions of
several familiar theorems fail without coherence or growth hypotheses.

The contour functional is defined coefficientwise over ordinary complex
contours. It is not claimed to be an ordinary Riemann integral along a
fine-continuous real-parameter path into the full surreal field.

## Building the PDF

A conventional TeX Live or MiKTeX installation with the packages named in the
preamble is sufficient. No external images, bibliography database, custom font
files, or shell-escape features are needed.

From this folder, run:

    latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_analysis.tex

Alternatively, run `pdflatex surcomplex_analysis.tex` at least twice, until
cross-references and the contents page stabilize.

## Running the checks

With Python 3.10+ and SymPy installed:

    python verify_examples.py

To regenerate the output file:

    python verify_examples.py > verification.txt

All six check groups passed in the supplied run, using exact symbolic
arithmetic. The script checks finite truncations and exact algebraic identities;
it does not certify the infinite-support proofs or formalize proper classes.

## Mathematical status

The article credits established surreal-analysis foundations, including
Conway, Gonshor, Alling, Berarducci--Mantova, and the Hahn--Neumann support
lemma. It develops and proves the stated coherent-framework results without
claiming that all formulations are previously unpublished. It is not an
exhaustive novelty search or a proof-assistant-certified development.

The assumptions of individual results matter. In particular, the finite halo
of an ordinary domain is not the whole surreal ball suggested by its ordinary
boundary, and a bound in the surreal ordering is not a coefficientwise bound.
