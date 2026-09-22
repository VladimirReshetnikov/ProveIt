# Expanding Polynomial Dynamics over Surreal and Surcomplex Fields
## Exact symbolic fibers and the cofinality obstruction

Research draft, 22 September 2026. Prepared for Vladimir Reshetnikov.

The article proves an exact infinite-itinerary fiber theorem for polynomials
`F = q^(-1) P` over real or complex Hahn fields of arbitrary valuation rank,
where `q` has positive valuation and `P` has degree-preserving, simple split
reduction. It specializes the results to actual surreal and surcomplex numbers.

The main formula is

    B_int(F) = disjoint union over words s of (x_s + I_kappa),
    I_kappa = {h : v(h) > n*kappa for every natural number n},
    kappa = v(q).

A support-controlled universal formal construction supplies the centers x_s.
The full native topology yields a Cantor shift exactly when kappa is cofinal.
Otherwise the fibers are open, iterates are uniformly equicontinuous on B_int,
and every compact forward-invariant subset of B_int is finite. The scale
quotient still gives the full shift.

Every preperiodicity polynomial splits with distinct roots in the original
Hahn field. Extending the exponent group can thicken all the fibers without
adding any preperiodic points. Additional theorems cover flat deformations,
an exact valuation-bounded orbit locus, and polynomial equicontinuity when
there is no order unit. The explicit example is F(x) = omega*(x^2 - 1).

## Files

- `article.pdf`: the 24-page article, including proofs and bibliography.
- `article.tex`: standalone LaTeX source with internal bibliography.
- `code/verify.py`: exact standard-library Python regression program.
- `data/verification.json`: recorded output of the supplied program.
- `RESEARCH_STATUS.md`: novelty scope, proof boundaries, and audit notes.
- `Makefile`: reproducible verification and PDF build commands.

## Status

This is an unrefereed research draft, not a certified solution of a named
published conjecture. The arbitrary-rank fiber/compactness and extension/
deformation package is proposed as new after a limited targeted literature
search. Historical priority is not established. The article expressly credits
classical Hahn support, formal implicit-function, and rank-one dynamics tools.

The new proofs are not Lean-checked, and the repository was not rebuilt or
modified. The finite verification program does not prove infinite support,
compactness, or proper-class statements.

## Reproduce the checks

Python 3.10 or later; no external packages and no network access needed:

```sh
python code/verify.py --output data/verification-rerun.json
```

Run without `-O`. The recorded run passed **38,139 exact checks**. Check counts
and rational outputs are deterministic; elapsed time and Python version vary.

## Build the PDF

A reasonably complete TeX Live or equivalent distribution is needed. Packages
include newpx text/math, amsmath/amsthm, microtype, TikZ, tcolorbox, hyperref,
cleveref, aliascnt, enumitem, tabularx, and listings. Font packages are standard TeX
dependencies; no font files are distributed in this archive.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or run `make all`. BibTeX is not required. `make clean` removes intermediate
TeX build files without deleting the article PDF or verification record.

The delivered PDF was rendered with Poppler and visually inspected. It is not
an accessible tagged PDF. No third-party books, research-paper PDFs, or
proof-assistant binaries are included.
