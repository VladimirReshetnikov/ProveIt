# Build the research article

The main file is `compressed_component_certificates.tex`. Build from this
directory with:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error compressed_component_certificates.tex
```

Without `latexmk`, use pdfLaTeX, BibTeX, then two further pdfLaTeX passes:

```bash
pdflatex -interaction=nonstopmode -halt-on-error compressed_component_certificates.tex
bibtex compressed_component_certificates
pdflatex -interaction=nonstopmode -halt-on-error compressed_component_certificates.tex
pdflatex -interaction=nonstopmode -halt-on-error compressed_component_certificates.tex
```

The PDF and complete source tree are included. Keep `sections/`, `tables/`,
`figures/`, and `references.bib` beside the main source when integrating the
article into another repository directory. All figures are available as
vector PDF and PNG; the manuscript uses the vector versions.

The enclosing archive's `reproduce.py` can rebuild a separate copy under
`rerun/article/`. Its figure command defaults to the recorded data, keeping
the tables consistent with the numerical discussion. New benchmark data can
be selected explicitly; updating tables does not rewrite prose automatically.

The article distinguishes proved local scheduling results, the classical
weighted AHT foundation, the five-coordinate geometric implementation, and
the remaining obligations for a general quasi-polynomial recognizer. It is a
research continuation prepared against ProveIt commit
`274909dd8724e411ece14e47ac4addea717aeca6`.
