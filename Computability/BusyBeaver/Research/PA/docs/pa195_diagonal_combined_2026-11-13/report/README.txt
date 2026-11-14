Building the report
===================

The supplied PDF is the complete compiled report. All of its source files
are included in this directory. From this directory, use an ordinary
TeX Live or MiKTeX installation:

  pdflatex -interaction=nonstopmode -halt-on-error pa195_diagonal_combined.tex
  pdflatex -interaction=nonstopmode -halt-on-error pa195_diagonal_combined.tex

Alternatively, latexmk -pdf pa195_diagonal_combined.tex manages the passes.
No BibTeX run is needed; the bibliography is included in the main source.
The report uses standard packages including lmodern, geometry, amsmath,
amssymb, amsthm, mathtools, booktabs, longtable, array, tabularx, microtype,
xcolor, xurl, enumitem, fancyhdr, needspace, etoolbox, and hyperref.

Appendix A's transition entries are generated from ../machine/machine.tm.
The compiled PDF was rendered and visually checked, and the 390 printed
transition entries were checked against the supplied literal table.
The LaTeX source distinguishes a mathematical proof of PA provability,
existing imported formal proofs, and the executable symbolic certificates.
