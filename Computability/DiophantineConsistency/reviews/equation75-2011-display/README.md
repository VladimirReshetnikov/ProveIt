# Display of the 2011-port 75-operation equation

[`equation75-2011.tex`](../../equation75-2011.tex) and its one-page
[`equation75-2011.pdf`](../../equation75-2011.pdf) display the
13-positive-variable `ModelThirteenSquares.value75` polynomial at the full
current 2011 port tuple. The fixed action seed is decimal and the thirteen
unknowns have distinct names. The existing `equation.tex` and PDF remain the
separate 14-variable display.

[`check_display.py`](check_display.py) parses all 24 displayed polynomial
abbreviations and compares them with the symbolic 75-row DAG by exact sparse
integer polynomial arithmetic at named cuts. It checks the 13 positive unknown
names, the square-sum output wiring and byte equality of the fixed-constant
block with the existing 2011 display. Its three mutation controls alter the
gap, the mixed signed carrier and the boxed output. The auxiliary `t=b*i*c²`
is checked and retained inline because it is not a separate graph row. The
75-operation count refers to the shared positive-coordinate DAG, not the
expanded polynomial or unshared positive-shift syntax.

The [independent graph/iPRA audit](../thirteen75-model-binding-independent-audit/README.md)
checks the symbolic row binding and paired native, standard, reference and
translated-consistency client. The [separate exact-degree audit](../thirteen75-degree2011-independent-audit/README.md)
checks degree 96 for the full 2011 tuple. The displayed constant block
inherits the [2011 fixed-constant audit](../equation14-historical-literal-binding/README.md),
including its manually transcribed decoder/ranking recipe boundary. This
external display check is not Lean semantics for TeX or PDF, and the parent
proof's package-transitive/dynamic and Foundation wrapper-exit limitations
remain. The present display packet awaits independent review.

`python3 -I -S check_display.py` actually exited 0 with all 24 definitions,
graph output wiring, constant block and three mutation controls checked;
`python3 -I -S -O check_display.py` exited 1 before checking. A fresh
`pdflatex -interaction=nonstopmode -halt-on-error` build produced a
byte-identical one-page letter-size PDF. The build reported font-size
substitution warnings but no typesetting error.

The TeX SHA-256 is
`18855bda8468b5a3d61b1ff8c07b52f1660262aaa8ecf387f127af56511e26fa`;
the PDF SHA-256 is
`07acffa02ec7e2068b2cbd04e16cc0089d4fa30af045e86a9130f95ac444abda`.
