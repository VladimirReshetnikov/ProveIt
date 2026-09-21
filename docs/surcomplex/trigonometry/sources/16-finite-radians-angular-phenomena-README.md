# Trigonometry on the Surcomplex Plane

**Finite Radians, Arbitrary-Scale Geometry, and Infinitesimal Angular Phenomena**  
September 21, 2026

## Contents

- `surcomplex_trigonometry.pdf` — the 33-page article, including contents, proofs,
  examples, notation, and bibliography.
- `surcomplex_trigonometry.tex` — self-contained LaTeX source; references are inline
  in a `thebibliography` environment, so no separate bibliography database is needed.
- `verify_examples.py` — reproducible exact symbolic checks.
- `verification_report.txt` — results from the included script: 67 checks passed.
- `requirements.txt` — the tested SymPy version for the checks.
- `source_provenance.txt` — identities and SHA-256 hashes of the three supplied sources.

## Mathematical scope

The article starts from the supplied manuscripts and established surreal/Hahn-field
foundations. Its main distinction is between directions, finite radian arguments,
and optional phases at infinite real arguments. Every surcomplex direction has a
finite radian representative; the phase group is the group of finite surreals modulo
ordinary integral multiples of 2 pi. It also splits as the ordinary circle times the
additive group of real surreal infinitesimals.

The article proves triangle, circle, and concurrence identities at arbitrary surreal
scales, then develops angular valuation identities, a uniform flattening formula,
Fejer–Riesz factorization, finite Fourier inversion, and angular root-collision and
conditioning results. A degree-two example is positive at every ordinary angle but
negative at an infinitesimal angle. The canonical complex sine on arguments with
finite real part and arbitrary surreal imaginary part is surjective onto the whole
surcomplex field. A character classification describes global phase choices and
shows that every homomorphic full-real-class extension has infinite periods.

The coupled-root example uses the finite algebra of the entire zero set in the
infinitesimal monad; its dimension four is a total multiplicity, not a claim that
each individual simple root has a four-dimensional local algebra.

Classical identities and real-closed-field extensions are not presented as original
discoveries. No exhaustive novelty certification, named open-conjecture resolution,
or proof-assistant verification is claimed. The source manuscripts are explicitly
identified as unpublished supplied documents, not as published literature.

## Build the PDF

With a LaTeX installation containing the usual AMS, Latin Modern, microtype,
hyperref, cleveref, booktabs, longtable, and fancyhdr packages:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_trigonometry.tex
```

Alternatively run `pdflatex surcomplex_trigonometry.tex` repeatedly until the
cross-reference and table-width warnings disappear (normally three runs).

## Reproduce the symbolic checks

The recorded run used Python 3.13.5 and SymPy 1.14.0.

```text
python -m pip install -r requirements.txt
python verify_examples.py
```

The script overwrites `verification_report.txt` next to itself, or accepts an
alternative output path:

```text
python verify_examples.py --output another_report.txt
```

These checks verify finite polynomial/rational identities and finite formal-series
coefficients. They do not implement arbitrary surreal numbers, prove strong
summability, or formalize the general theorems. Those proofs are in the article.

## PDF review

The final source compiles without LaTeX warnings or overfull/underfull boxes.
All PDF pages were rendered and visually reviewed; extracted text was also checked
for unresolved references and text outside the page boundaries. These layout checks
are separate from mathematical verification.
