# K222 research report

`report.pdf` is the 10-page article, including the complete canonical transition table.
The editable source is `report.tex`; `metadata.tex` and `transition_table.tex` are required inputs.

Build with standard TeX Live:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

`sh build.sh` performs those steps with optional compatibility settings for the research container. The standard packages used are geometry, fontenc, lmodern, amsmath, amssymb, amsthm, booktabs, array, longtable, hyperref and xurl.

Regenerate the table from the delivered machine when needed:

    python3 generate_table.py ../machine/k222.tm

The report states the completed original final-machine checks. Clean-extraction release replay is separately recorded in the package verification receipts. The report does not claim a new Rocq or Lean kernel endpoint.
