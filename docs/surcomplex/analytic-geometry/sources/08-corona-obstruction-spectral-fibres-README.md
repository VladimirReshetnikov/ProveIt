# A Corona Obstruction and Infinite-Dimensional Spectral Fibres in Surcomplex Analysis

Research article prepared for Vladimir Reshetnikov, 21 September 2026.

## Files

- `article.pdf`: the complete 26-page article, including full proofs and references.
- `article.tex`: self-contained LaTeX source; no separate bibliography file is needed.
- `verify.py`: exact finite consistency checks, using Python and SymPy.
- `verification_results.json`: output of the completed verification run.
- `PROOF_AUDIT.md`: dependencies, scope, and limits of the results and checks.
- `requirements.txt`: the SymPy version used for the recorded checks.
- `Makefile`: optional build and verification commands.
- `layout_audit.json`: page counts and text-boundary checks for the delivered PDF.

## Main setting

D is the ordinary complex unit disk. The ring is

    H_Gamma = O(D)((t^Gamma)),   K_Gamma = C((t^Gamma)).

Every ordinary holomorphic coefficient is defined on the same fixed disk,
and the global Hahn exponent support is well ordered. This is not a ring of
germs, a Tate algebra, or the full class of functions on No[i]. For the
surcomplex interpretation, t^gamma = omega^(-gamma). The normed results and
continuum prime chains use Gamma = R. Several algebraic statements hold for
arbitrary set-sized ordered abelian groups.

## Main conclusions

The article proves an exact Bezout criterion modulo a fixed ordinary simple
discrete divisor: nonzero values must have only finitely many distinct leading
valuations. Boundedness of those valuations is not enough.

An explicit pair has a uniform positive pointwise valuation-norm lower bound,
but generates a proper nonprincipal ideal. No larger Hahn value group repairs
the obstruction. The distance from 1 to the ideal is exactly 1, so approximate
Bezout identities with smaller residual norm also fail. This occurs in a
complete uniform non-Archimedean Banach algebra.

A single spectral fibre over one classical free maximal ideal is an integral
domain of infinite Krull dimension. It contains a continuum-sized chain of
prime ideals below an explicit coefficient-reduction maximal ideal. The chain
has a common norm closure. A concrete example also shows that coefficientwise
Hahn reduction need not equal scalar residue-field base change.

In contrast, localization at every actual finite surcomplex point above D is
a discrete valuation ring, with residue field K_Gamma and completion K_Gamma[[X]].
Real-symmetric versions give corresponding surreal-valued results.

## Status

This is a proof-based research draft, not a claim to solve a named published
conjecture. The proposed novelty lies in the precise combination of theorems,
not in the classical Hahn support lemma, ordinary interpolation, the existence
of free holomorphic ideals, or growth-rate constructions alone. A targeted
literature search found no matching complete statement, but does not certify
historical priority. The general proofs have not been independently refereed
or checked in a proof assistant.

The repository was inspected at the pinned commit

    aa846271b4dcae2c055b216126a87210292ec19b

of VladimirReshetnikov/Surreal. Section 11 identifies a fixed-domain structure
assertion contradicted by these results. It does not claim to refute the
repository's distinct germ-ring statements or finite-isolated-zero deformation
theorems. Related restricted interpolation results in the repository are credited.

## Rebuild the PDF

Use a TeX distribution with pdfLaTeX and the packages listed in `article.tex`,
including New PX text and mathematics. From this directory:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

Or run `make pdf`. No shell escape, network access, BibTeX, external images,
or separately supplied fonts are needed. Standard installed TeX font packages
are required; no font files are distributed in this archive.

The delivered PDF compiled with no LaTeX warnings or undefined references.
All 26 pages were rendered and inspected, and a text-boundary audit found no
text outside the specified safe page area.

## Reproduce the finite checks

Use Python 3.10 or later, without `-O`:

    python -m pip install -r requirements.txt
    python verify.py --output verification_results.json

The recorded run used Python 3.13.5 and SymPy 1.14.0. It passed:

- 1,000 exponent values and 999 successive differences;
- 256 cardinal-function identities at 16 centres, plus the derivative formula;
- 80 exact divided-difference polynomial identities;
- 72,000 rational-grid valuation inequality checks;
- 120 exact truncated positive-support inverse checks;
- 20 symbolic integer-rate separations and 600 finite witness bounds.

These are consistency checks for finite specializations. They do not compute
an arbitrary infinite Hahn series, construct a nonprincipal ultrafilter,
verify an infinite prime chain, prove the general theorems, or establish novelty.
