# Building the report

`report.pdf` is the supplied compiled report. Its complete editable source
is `report.tex`; it has no external image or bibliography-file dependencies.

From this directory, a TeX Live installation with pdfLaTeX can build it:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error report.tex`
three times so that the table of contents and cross-references stabilize.
The source uses conventional packages: geometry, lmodern, microtype,
amsmath/amssymb/amsthm/mathtools, booktabs/longtable/array, xcolor, enumitem,
listings, seqsplit, fancyhdr, hyperref, and bookmark.

The report contains ordinary mathematical proofs and computational evidence.
Its compilation is a document-build check, not a proof-assistant check.
