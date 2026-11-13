# Display of the 2011-port 13-variable equation

[`equation69-2011.tex`](../../equation69-2011.tex) and the generated
[`equation69-2011.pdf`](../../equation69-2011.pdf) display the 13-positive-
variable `ThirteenCarrier.value69` polynomial at the complete current 2011
port tuple. They are separate from the maintained 14-variable `equation.tex`.
All thirteen unknowns have distinct names. The fixed action seed is printed
in decimal, as in the existing 2011 display.

[`check_display.py`](check_display.py) parses the 24 displayed polynomial
abbreviations and compares them with the symbolic 69-row DAG using exact
sparse integer polynomial arithmetic at named cuts. The auxiliary `t` is
checked as `b*i*c²` and kept inline because it is not a separate row of the
69-operation DAG. The checker separately verifies the output factor wiring,
the thirteen distinct positive unknown names, and byte equality of the fixed
constant block with the existing 2011 display. It rejects changes to the gap,
the signed carrier and the boxed equation. Its graph has the original
phase-split metadata, but the checked 69 arithmetic rows are symbolic in all
four ports; the displayed constant block selects the different current 2011
tuple. The 69-operation count is for that shared positive-coordinate DAG,
not a count of a fully expanded polynomial or of the unshared positive-shift
syntax. The 2011-port exact degree is checked separately in the
[independent degree audit](../thirteen69-degree2011-independent-audit/README.md).

The corresponding [DAG-specific iPRA endpoint](../thirteen-model-dag-ipra-independent-audit/README.md)
has a paired and independently reviewed replay. It states derivability for the
positive-shifted literal and the selected Foundation consistency encoding,
including its Gödel–Gentzen-translated consistency comparison. This display
check is external: it is not a Lean parser for TeX or a formal PDF semantics.
The unchanged constant block inherits the existing [2011 display audit](../equation14-historical-literal-binding/README.md),
including its manually transcribed decoder/ranking recipe boundary and the
recorded provider/dynamic ancestry limitations. The current display check has
not yet been independently reviewed.

## Observed checks

* `python3 -I -S check_display.py` exited 0, checking all 24 definitions,
  output wiring, constant-block equality and three mutation controls. It uses
  the `Poly`, `Parser` and `tokenize` definitions extracted from the existing
  86-display checker without running that checker's other top-level code.
* `python3 -I -S -O check_display.py` exited 1 before checking.
* `pdflatex -interaction=nonstopmode -halt-on-error` produced a one-page
  letter-size PDF. A second build in a fresh output directory was byte-identical.
  The build logged font-size substitution warnings, as does the compact
  fixed-decoder display; no typesetting error was reported.

The checked TeX SHA-256 is
`731f2d6e763d74588702d8354633079900bc0d78fe4f65428e827fbae7905382`;
the PDF SHA-256 is
`83c4ebf9c7afc24405088fb4d0cd49d80507673e20367286cf17be34df8002e0`.
