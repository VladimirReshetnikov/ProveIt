# Turing Degrees: A Unified Research Report

Unified edition: 18 September 2026.

This package integrates the three reports supplied in Turing.zip. It includes
39 consolidated research topics, three separately marked bounded programmes,
the complete proposed tower-padding arguments, diagnostic lemmas, a shared
formalization audit, one bibliography, and an input-to-output crosswalk.

## Files

- turing_degrees_unified.tex: self-contained editable LaTeX source.
- turing_degrees_unified.pdf: compiled report.
- source_crosswalk.csv: all 60 original numbered entries plus three programmes.
- build.sh: reproducible PDF build command.
- checks/: the two inherited Python check programs and freshly generated results.
- validation.txt: document checks and the scope of verification.

## Build

Use a standard TeX Live installation with pdfLaTeX, latexmk, Latin Modern,
AMS packages, geometry, booktabs, longtable, tabularx, microtype, enumitem,
xcolor, fancyhdr, listings, xurl, titlesec, hyperref and bookmark.

Run `./build.sh`, or run:

    latexmk -pdf -interaction=nonstopmode -halt-on-error turing_degrees_unified.tex

No external bibliography processor or image assets are required.
No font binaries are distributed.

## Run the finite checks

Requires Python 3.10 or later, standard library only:

    python3 checks/check_padding.py
    python3 checks/finite_checks.py

The tests check only finite combinatorial identities and examples. They do
not prove the infinite tower claims, settle published questions, certify
novelty, or constitute Lean verification. The report is explicit about the
weak-tower convention issue and the absence of an independently reviewed
or Lean-checked proof. Original software audits are inherited source
inspections; no Lean build was performed for this synthesis.

The three original PDFs and unrelated source-package metadata are not
duplicated here. Their provenance and entry mappings are in the report.
