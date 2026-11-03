# Standalone decimal display for the 91-operation candidate

[`equation.tex`](equation.tex) and [`equation.pdf`](equation.pdf) state the
12-variable, 91-operation positive-coordinate graph as one Diophantine zero
equation. The only unknowns are the distinct positive integers
`a,b,c,d,e,f,g,h,i,j,k,ℓ`. In the graph's original order these correspond to
`J,F,alpha,t,T,w,s,r,eta,zeta,n,gamma`. The `r01` through `r91` names are
explicit evaluator abbreviations, not additional unknowns. The page specifies
ordinary integer arithmetic, including integer subtraction and potentially
negative intermediate values. The fixed coefficients and all 943 selector
blocks are expressed with decimal numerals.

The four-page display is self-contained: page 2 defines the four fixed
integers, and pages 2–4 contain the complete decimal selector list. It uses
the same fixed coefficient and selector recipes as the separately reviewed
[94-operation v2 display](../ordinary12-ipra-bridge/compact44-free-j-display-v2/README.md).
Relative to the 92-graph, the sixth positive witness is `w`, with the former
`X=q*w`; the seventh remains `s`, with the original `Y=q³*s`.
The [independent 91-graph audit](../../reviews/ordinary12-xq91-independent/README.md)
checks the 91 live operations and gives external evidence of exact degree
172. The separate positive-coordinate shifts used in model statements are
not included in the displayed operation count.

[`generate.py`](generate.py) is adapted from the checked 92 display generator
and pins the 91 graph, selector/slot source files, and all four compressed
coefficient payloads. It computes each fixed integer and checks its complete
little-endian representation against the retained payload. Two fresh builds,
[`build01`](build01) and [`build02`](build02), exited 0, produced byte-identical
TeX and PDF, and match the canonical files. Their result files and full LaTeX
logs are retained; neither reports an overfull box, and both report one
underfull box in the evaluator paragraph. The PDF has four letter-size pages.
At 100 dpi, the first two pages were visually inspected and showed no apparent
clipping or overlap; the small evaluator and selector text benefits from zoom.

[`check_display.py`](check_display.py) compares all 91 extracted PDF rows
against the pinned graph and checks the printed TeX formulas and 41 slots,
the 943 decimal selectors in TeX and PDF, all four complete coefficient
payloads, the integer-subtraction notice, and repeated builds. The separate
[`independent_check.py`](independent_check.py), adapted from the earlier
independent 92-display checker, independently parses the 91 PDF rows,
verifies every selector block and PDF-extracted slot, recomputes the complete
four fixed coefficients against hash-pinned supplement payloads, and checks
PDF word bounds. Its fixed-coefficient and selector text on pages 2–4 exactly
matches the independently reviewed v2 94-operation PDF. Text equality and
word bounds are not general TeX or PDF-rendering semantics. Poppler emits an
XML-invalid control character for a math delimiter; the bounding-box parser
removes such controls before checking page bounds. The minimum extracted word
margin is 28.028 points. These are author-run checks, not a new independent
peer replay of this 91 display.

Both separate checkers exited 0 with empty stderr and unchanged captured
inputs in [`observations/checks01`](observations/checks01/). The canonical
file hashes are:

- TeX: `88ccf8f71a4e9adf341912cd5e550cafca51e60245ef8fce76c3b4223607241b`
- PDF: `ff67d52fcc8d2809772896c21c68b5f204e1c4fe577f975650b3a3931ba90133`

The 91-expression has a separately checked Lean all-model machine-run
comparison; see the [independent halt-model review](../../reviews/ordinary12-xq91-halt-independent/README.md).
Correspondence between these PDF/TeX files, JSON and external coefficient
payloads remains externally checked, not a Lean file/PDF semantics theorem.
The coherent internal iPRA equivalence remains open. No global minimality is
claimed. The maintained root `equation.tex` and `equation.pdf` were not
modified by this display workflow.

From this directory, use a fresh direct child for a repeat build and run the
read-only external checks:

```sh
python3 -I -S -B generate.py --output "$PWD/build03"
python3 -I -S -B check_display.py
python3 -I -S -B independent_check.py
```
