# Rebuild the report

From this directory, with a standard TeX Live installation:

    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    pdflatex -interaction=nonstopmode -halt-on-error main.tex

The included PDF is compiled from this exact main.tex and its included section/table fragments. Packages are standard: lmodern, microtype, geometry, AMS mathematics, mathtools, booktabs, longtable, array, tabularx, multicol, xcolor, xurl, hyperref, fancyhdr and enumitem.

`generate_tables.py` regenerates the transition table and both comparison appendices directly from the delivered machine and CSV files. `research_summary.tex` summarizes the separately recorded finite search scope.

The inherited logical source fragments are preserved as references; they are not all intended as standalone compilable documents. `proof/pa194h6_preservation.tex` is included in main.tex.
