# Base-10 display of the 37-variable quartic candidate

This separate [TeX file](equation.tex) and [two-page PDF](equation.pdf) present the [37-positive-variable, 158-operation, degree-4 candidate](../adaptive-square-sums37-difference-quartic/README.md). They do not modify the maintained `equation.tex` or `equation.pdf`. The 37 input names use distinct descriptive `arg...` prefixes, avoiding collisions with fixed-recipe indices; `G001` through `G158` are intermediate polynomial abbreviations. The four fixed integers use the same current-2011 base-10 recipe and decimal seed as the maintained page, copied byte for byte from its pinned source.

The 37-variable construction uses an external zero map to the 38-variable candidate, including a positivity argument for the new square-difference witness. The older 40-variable parent has a historical author-side standard-iPRA endpoint with documented provider qualifications. **The new 37-variable expression and maps have not been proved in Lean**, and neither external text extraction nor a PDF hash establishes formal semantics of document bytes. The formula is a candidate and does not prove ZFC consistency.

`generate.py` derives the TeX assignments from the pinned 158-row graph and copies the fixed-constant section. `verify_display.py` checks all 158 TeX rows against that graph and all 158 corresponding equations in extracted PDF text, checks distinct input names, verifies the inherited constant section and each decimal seed line, and records two PDF pages with no overfull boxes. The local LaTeX run reports small-font size substitutions for the compact fixed-constant formulas. These checks are source/text comparisons, not a verified TeX interpreter or Lean binding.

From this directory:

```sh
python3 -I -S -B generate.py | cmp - result.json
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error equation.tex
python3 -I -S -B verify_display.py | cmp - render-result.json
```

`generate.py` without arguments is read-only; `generate.py --write` deterministically replaces the TeX and source receipt in this candidate directory only. Different LaTeX or PDF-tool versions can produce different PDF bytes or extraction.
