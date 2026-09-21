# Trigonometry on the Surcomplex Plane

**Canonical Angles, Infinite Triangles, Infinitesimal Contact, and Hahn-Analytic Oscillation**  
September 21, 2026

## Contents

- `surcomplex_trigonometry.pdf` — the 36-page compiled article, including proofs,
  worked examples, a dependency audit, a formula sheet, and references.
- `surcomplex_trigonometry.tex` — complete, self-contained LaTeX source.
  The bibliography is embedded; no external bibliography database is needed.
- `verify_examples.py` — 68 exact symbolic checks of selected finite algebraic
  identities and formal series coefficients.
- `verification_report.txt` — the successful check report produced for this edition.
- `requirements.txt` — the SymPy version used for the supplied verification run.
- `build.sh` and `build.ps1` — optional PDF build scripts for a Unix-like shell
  and PowerShell, respectively.

## Main development

The article constructs canonical sine and cosine on finite surreal angles using
Hahn summation. Every direction in the full surcomplex plane has such an angle,
including directions of vectors with infinite or infinitesimal coordinates.

It proves triangle laws at arbitrary scales; analyzes extremely thin triangles
and near-tangent circle intersections; constructs complex trigonometry on the
strip with finite real part and arbitrary surreal imaginary part; proves
finite-degree root counts, multiplicity-preserving cluster lifting, finite
Fourier identities, and a real-closed-field Fejer–Riesz factorization; develops
hyperbolic triangle laws; and classifies circular group-law extensions to all
surreal real arguments. The final sections separate coherent integrals from
ordinary polygon limits, and fine-local analyticity from common-domain Hahn
coherence.

## Build the PDF

Use a LaTeX distribution with pdfLaTeX and the standard packages listed in the
source preamble. There are no external graphics or custom font files.

    pdflatex -interaction=nonstopmode -halt-on-error surcomplex_trigonometry.tex
    pdflatex -interaction=nonstopmode -halt-on-error surcomplex_trigonometry.tex
    pdflatex -interaction=nonstopmode -halt-on-error surcomplex_trigonometry.tex

Alternatively run `bash build.sh` or `pwsh -File ./build.ps1`. The repeated passes
resolve cross-references, the table of contents, and PDF bookmarks.

## Run the exact checks

With Python 3.9 or later:

    python -m pip install -r requirements.txt
    python verify_examples.py --report verification_report.txt

The supplied report was produced with Python 3.13.5 and SymPy 1.14.0. Every check
uses exact symbolic arithmetic; no floating-point sampling is used. The script
exits with a nonzero status if a check fails.

## Scope and status

This is a mathematical research exposition, not a formally verified library.
The symbolic checks verify selected algebraic identities and series coefficients;
they do not implement the surreal class, verify transfinite recursions, or
machine-check the proofs. Positivity, branch selection, and Hahn-support
arguments are justified in the text. Independent mathematical review remains
appropriate for research use.

The article distinguishes established results and classical identities from
its developments and specializations. It makes no claim of literature priority.
It does not claim that a unique canonical value of circular sine at every
infinite real argument follows from the finite-angle theory.

The three supplied manuscripts are cited by title and filename, and their role
is explained in Section 1. Their several-variable division and residue theorems
are not assumed as black boxes for the triangle geometry. The original uploads
are not duplicated in this archive. Public references and links are in the
article's bibliography.
