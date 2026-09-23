# Omnific Integers and Omnific–Diophantine Geometry

**Retractions, rigidity, definability, and infinite families**\
Research article dated September 22, 2026, prepared for the Surreal project.

## Contents

- `omnific_integers.pdf` — the typeset article, with proofs, examples, bibliography, and source audit.
- `omnific_integers.tex` — complete, self-contained LaTeX source; bibliography is included in the source.
- `verification.py` — supplementary finite symbolic and integer checks.
- `verification_report.json` — actual output of the included verification script.
- `requirements.txt` — the tested SymPy version.
- `build.sh` and `build.ps1` — PDF build commands for a Unix-like shell and PowerShell, respectively.

## Main mathematical results

The article proves the constant-term retraction and equational transfer;
classifies finite quotients; solves integer-coefficient linear systems;
proves nonzero binary-form and number-field norm rigidity; classifies the
presence of infinite points on represented nonzero quadratic levels;
and constructs a single quartic equation defining the ordinary integers
inside the omnific integers, with five auxiliary variables independently
of tuple length.

It also treats global common monomial divisors, denominator clearing,
non-atomic factorization, an explicit pair without a gcd, failure of
Euclidean termination, infinite unimodular Pythagorean triples, and
primitive representatives of real projective directions.

## Build the article

A TeX distribution with `latexmk`, pdfLaTeX, Latin Modern, AMS packages,
`microtype`, `hyperref`, `cleveref`, `aliascnt`, `booktabs`, `enumitem`, and `fancyhdr`
is required. These are standard TeX Live / MiKTeX packages.

From this directory:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error omnific_integers.tex
```

Alternatively run `./build.sh` or `./build.ps1`. No bibliography processor,
external figures, nonstandard font files, or network access is required
once the TeX packages are installed. The scripts will write build
intermediates into this directory.

## Reproduce the finite checks

Python 3.9 or newer and SymPy are required:

```text
python -m pip install -r requirements.txt
python verification.py --output verification_report.json
```

The actual Python and SymPy versions used for the supplied report appear
in `verification_report.json`. The checks cover scalar identities,
20 quadratic-isometry matrix cases, Pell indices 0 through 30, and
256 square-gap / quartic-guard witnesses.

**These checks are not proof-assistant verification of the article.**
They do not implement arbitrary surreal normal forms and do not establish
the general statements by finite sampling. The manuscript contains the
mathematical proofs; the classical three-square theorem, normal-form
foundations, and MRDP theorem are explicitly cited imports.

## Scope and provenance

Repository snapshot inspected:
`VladimirReshetnikov/Surreal`, commit
`2cb9c0200af749fbbd27796c97d017e7f16fbf33`.

This was a focused read of the tree, READMEs, documentation index, and
trigonometry source-audit material through the GitHub connector, not a
repository checkout or build. The article separates fixed Hahn-workspace
results from theorems using the full surreal class. It makes no claim of
independent peer review, complete historical novelty, or Lean verification.

A current refinement-conjecture announcement is recorded only as a dated,
qualified announcement; none of the mathematical results here depends on it.
