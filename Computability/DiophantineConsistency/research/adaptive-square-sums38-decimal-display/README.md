# Base-10 display of the 38-variable quartic candidate

This separate [TeX file](equation.tex) and [two-page PDF](equation.pdf) present the independently reviewed [38-positive-variable, 160-operation, degree-4 candidate](../adaptive-square-sums38-two-quadratic-products/README.md). They do not modify the maintained `equation.tex` or `equation.pdf`. The 38 input names use distinct descriptive `arg` prefixes, avoiding clashes with the bound indices in the constant recipe, and the `G001` through `G160` symbols are explicitly identified as intermediate polynomial abbreviations. The four fixed integers use the same current-2011 base-10 recipe and decimal seed as the maintained page; the fixed-constant section is copied byte for byte from the pinned source page.

The [independent graph review](../../reviews/adaptive-square-sums38-independent/README.md) checks the external positive zero maps to the 40-variable parent, exact quartic degree and operation count. The parent has a historical author-side standard-iPRA endpoint with its documented provider qualifications. **The new 38-variable expression and maps have not been proved in Lean**, and neither external text extraction nor a PDF hash establishes formal semantics of document bytes. The formula is a candidate and does not prove ZFC consistency.

`generate.py` derives the TeX gate assignments from the pinned 160-row DAG, assigns 38 readable input names and sequential `G` abbreviations, and copies the existing base-10 constant section. `verify_display.py` independently checks all 160 TeX rows against the DAG and all 160 corresponding equations in extracted PDF text, checks that the 38 declared names are distinct, verifies the inherited constant section and each decimal seed line, and records two PDF pages with no overfull boxes. The local LaTeX run reports normal small-font size substitutions for the compact fixed-constant formulas. These checks are a source/text comparison, not a verified TeX interpreter or Lean binding.

From this directory:

```sh
python3 -I -S -B generate.py | cmp - result.json
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error equation.tex
python3 -I -S -B verify_display.py | cmp - render-result.json
```

`generate.py` without arguments is read-only; `generate.py --write` deterministically replaces the TeX and source receipt in this candidate directory only. The PDF and TeX may be reproduced with the listed tools; different toolchain versions can produce different PDF bytes or text extraction.
