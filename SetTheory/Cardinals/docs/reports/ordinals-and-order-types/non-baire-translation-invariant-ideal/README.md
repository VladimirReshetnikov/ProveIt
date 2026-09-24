# A non-Baire translation-invariant ideal with a perfect translation-almost-disjoint family

Research note prepared September 20, 2026.

## Result and status

The article presents a complete proposed affirmative construction for Question 1
of Rafał Filipów and Jacek Tryba, *Densities for sets of natural numbers vanishing
on a given family*, Journal of Number Theory 211 (2020), 371–382;
preprint arXiv:2309.00982, page 7.

For every free ultrafilter U on omega, the construction gives a proper,
translation-invariant ideal I_U without the Baire property and a perfect
continuum-sized family of I_U-positive sets. Intersections of distinct members
remain finite after every fixed integer translation. The article also proves
positive-restriction non-Baire behavior, tallness, exact ultrafilter traces,
continuum many quotient atoms, a rich maxitive abstract upper density with exact
null ideal I_U, and a countable permutation-action extension.

This is an unrefereed research note. It has not been independently certified or
formalized in a proof assistant. The targeted literature search did not locate a
prior resolution of the selected question; it is not a definitive priority
search. The article distinguishes the proposed construction from classical
category criteria and established density-construction techniques.

## Read

Open `article.pdf` (18 pages). The complete editable source is `article.tex`.
The bibliography is embedded in the TeX file; no separate .bib file is required.

## Reproduce the finite checks

Requirements: Python 3.10 or later, standard library only.
The recorded run used CPython 3.13.5.

```sh
python3 verify.py
```

A successful run prints `EXACT FINITE VERIFICATION: PASS` and regenerates:

- `verification_results.json`
- `verification_report.txt`
- `tree_levels.csv`
- `shift_collisions.csv`
- `fusion_certificates.json`

For a separate output directory:

```sh
python3 verify.py --output-dir new-results
```

The original random selection is read from `random_selection.json`, adjacent to
the script. The area draw selected zero-based index 22, Set theory, from 24 areas.
The seed and complete pool are preserved. No reroll was made.

The recorded run passed 13,012,145 exact checks. All 8,191 labels through level 12
are generated; shifts up to absolute value 512 are scanned for node collisions.
All 256 depth-eight branch prefixes are compared for every nonzero shift from
-31 to 31. Eight 24-stage fusion constructions are also checked.

**Limits:** These checks do not construct or query a free ultrafilter, decide
membership in I_U, establish the Baire-property claim, verify the complete group
action theorem, or replace the infinite mathematical proofs. Finite ultrafilters
are principal and are not a substitute for the free ultrafilter in the argument.
The program uses explicit runtime checks, not removable Python `assert`
statements.

## Build the PDF

Requirements: a LaTeX installation with pdfLaTeX and the standard packages listed
in the preamble, including amsmath, amsthm, mathtools, lmodern, microtype, geometry,
booktabs, enumitem, fancyhdr, hyperref, and bookmark.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The Makefile provides `make pdf`, `make verify`, and `make clean`.
The last target removes LaTeX intermediates, not the PDF or verification data.
No internet connection is needed to run the checks or compile the article.

## Other files

`literature_search.md` records the scope and limitations of the source review.
No checksum manifest is included: re-running the checks or rebuilding the
PDF changes file hashes.
No copies of third-party papers, font files, or LaTeX build intermediates are
included in the archive.
