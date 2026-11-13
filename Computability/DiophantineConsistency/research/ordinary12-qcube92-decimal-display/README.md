# Standalone decimal display for the 92-operation candidate

[`equation.tex`](equation.tex) and [`equation.pdf`](equation.pdf) state the
12-variable, 92-operation positive-coordinate graph as one Diophantine
zero equation. The only unknowns are the distinct positive integers
`a,b,c,d,e,f,g,h,i,j,k,ℓ`. In the graph's original order these correspond to
`J,F,alpha,t,T,X,s,r,eta,zeta,n,gamma`. The names `r01` through `r92` are
explicit evaluator abbreviations, not additional unknowns. The displayed
instructions specify ordinary integer arithmetic, including integer
subtraction and possibly negative intermediate values. Fixed coefficients and
the 943 selector blocks are written with decimal numerals.

The four-page display is self-contained: page 2 defines all four fixed
integers, and pages 2–4 contain the complete decimal selector list. It uses
the same fixed coefficient and selector recipes as the separately reviewed
[94-operation v2 display](../ordinary12-ipra-bridge/compact44-free-j-display-v2/README.md).
The seventh positive witness is `s`; relative to that parent graph's `Y`, the
new graph uses `Y=q³*s` and a factored first residual. The independent
[92-graph audit](../../reviews/ordinary12-qcube92-independent/README.md)
checks the 92 live operations and gives external evidence of exact degree 164.
The separate positive-coordinate shifts used in model statements are not
included in this operation count.

[`generate.py`](generate.py) is adapted from the v2 generator and pins the
92-graph, selector/slot source files and all four compressed coefficient
payloads. It computes the displayed fixed integers and checks their complete
little-endian representations against the retained payloads. Two fresh builds,
[`build01`](build01) and [`build02`](build02), produced byte-identical TeX
and PDF and match the canonical files. Their recorded LaTeX output reports
no overfull boxes. Both PDFs have four letter-size pages; page 1 and the
formula page were visually inspected.

[`check_display.py`](check_display.py) compares all 92 PDF-extracted
operations against the pinned graph, verifies the printed TeX formulas and
41 slots, the 943 decimal selectors in TeX and PDF, the full values of all
four coefficient payloads, the integer-arithmetic notice and repeated
builds. A separate [`independent_check.py`](independent_check.py) parses all
92 PDF rows independently, verifies every 14-digit selector block and the
PDF-extracted 41 slots, recomputes all four complete fixed coefficients
against the hash-pinned supplement payloads, and checks PDF word bounds.
The extracted text of its fixed-coefficient and selector pages 2–4 exactly
matches the independently reviewed v2 94-operation PDF. Text equality and
word bounds are not general TeX or PDF-rendering semantics. Poppler emits an
XML-invalid control character for a math delimiter; the bounding-box parser
removes such controls before checking page bounds. The minimum extracted word
margin is 28.028 points.

Both separate checkers exited zero with empty stderr and unchanged inputs in
[`observations/checks01`](observations/checks01/). The retained canonical
file hashes are:

- TeX: `eacbe2fd9a52fe599fae4a51afb58ae588d21e3bec7eefc48c86bae33d3c8bfd`
- PDF: `9b7803603e0f9237c90f30f6b14d4957ad0849b9f1765099e981403849d0dc07`

The 92-expression has a separately checked Lean all-model machine-run
comparison; see the [independent halt-model review](../../reviews/ordinary12-qcube92-halt-independent/README.md).
The correspondence between these PDF/TeX files, JSON and external coefficient
payloads is still checked externally, not by a Lean file/PDF semantics
theorem. The coherent internal iPRA equivalence remains open. These documents
do not claim global minimality.

From this directory, use a fresh direct child for a repeat build and run the
read-only external checks:

```sh
python3 -I -S -B generate.py --output "$PWD/build03"
python3 -I -S -B check_display.py
python3 -I -S -B independent_check.py
```
