# Building the article

The self-contained source is `report.tex`; the delivered `report.pdf` was
compiled from it with pdfLaTeX through `latexmk`.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The preamble uses standard TeX Live packages. All bibliography entries are
embedded and link to the reviewed commit. There are no external images,
BibTeX databases, or generated tables required by the build.

The article states the accepted component scope separately from the remaining
endpoint integration. Replay commands and exact source pins are in the archive
root and the Lean/Rocq component READMEs.
