# Base-10 display of the 26/122/8 candidate

The [PDF](equation.pdf) and [TeX source](equation.tex) show the
[26-variable, 122-operation, degree-eight candidate](../adaptive-aq26-two-quotients122/)
as one equation in positive integers. Each witness has a distinct readable
name; the numbered `G` names are operation abbreviations, not variables. The
four fixed integers use the existing base-10 recipe, copied byte for byte
from the maintained main `equation.tex`. This is a separate presentation and
does not replace the main equation.

The candidate has a mathematical zero-map argument to the earlier AQ26 graph,
but **its new expression and that transfer have not been elaborated in Lean**.
The earlier graph's historical endpoint and its provenance limitations are
explained in the candidate README. This display does not independently prove
an iPRA endpoint for the new equation.

To reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/adaptive-aq26-two-quotients122-decimal-display/generate.py --write
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=research/adaptive-aq26-two-quotients122-decimal-display research/adaptive-aq26-two-quotients122-decimal-display/equation.tex
python3 -I -S -B research/adaptive-aq26-two-quotients122-decimal-display/verify_display.py
```

The generator pins the graph and existing constant recipe. The independent
row-wise extraction script checks all 122 graph rows in both TeX and extracted
PDF text, all 26 input names, exact inheritance of the decimal fixed-constant
section, every decimal seed line in the PDF, two-page layout, and absence of
TeX overfull boxes. Its deterministic output is retained in
[render-result.json](render-result.json). These checks are source/display
checks, not Lean elaboration or a formal proof of PDF rendering semantics.
