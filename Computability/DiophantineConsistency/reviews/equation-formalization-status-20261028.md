# Canonical equation page: formalization status correction

The canonical page's former footer said that native calibration and internal
formalization remained open in Lean. That statement was stale. This change
updates only the footer; it does not change the equation, the positive domain,
the fixed constants, the decimal decoder, any printed digit, or the unknown
names. It makes no new claim of a consistency decision or global minimum.

The corresponding maintained polynomial has a closed external equivalence
`CurrentPositiveZero2011.no_positive_zero_iff_conZFC`. The repository also
formalizes an HA derivation as `HACurrentEquation2011.ha_current_iff_consistency`;
`ArithmeticCurrentEquation2011.sat_unsolvabilitySentence_nat` relates the
standard interpretation of its no-zero sentence to the maintained positive
polynomial, and `ObjectCurrentEquation2011.polynomial_expression` binds its
expression to that polynomial. The [HA plan](../HA_PROVABILITY_PLAN.md)
records the later IΣ₁ strengthening. This presentation update does not replay
any Lean endpoint, and its footer does not claim that Lean parses the PDF.
The [independent page review](padding-staircase-carrier65-2011-page-peer.md)
previously checked the printed source, constants, 715 decimal digits and
rendered page against the accepted construction. That review and the candidate
manifests bind the **earlier** presentation, including its former footer.

| Canonical artifact | Earlier SHA-256 | Current SHA-256 |
| --- | --- | --- |
| `equation.tex` | `a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e` | `94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635` |
| `equation.pdf` | `417c2fa109cacf99d0e83af35d06cbdc8fed1179054d7245e07f3e51ebfff978` | `23a52933980352f83a19c21a0d6f349594be5f85edc85a462e25ffc83c7fd5d6` |

The source prefix up to the old/new footer markers and the final document
ending are byte-identical. A fresh `pdftotext -raw` comparison also found the
entire extracted prefix before those markers byte-identical. Extracting the
12 decimal chunks from each PDF gives the same 715 digits as
`research/reverse-discovery-decimal-seed/DECIMAL_INTEGER.txt`. The source
retains the same 14 distinct unsubscripted unknown names and explicitly labels
the printed integer base 10.

The current PDF was built with
`pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory=/tmp/equation-status-20261028 Computability/DiophantineConsistency/equation.tex`.
A second build in a separate directory was byte-identical. `pdfinfo` reports
one Letter page; `pdftotext -bbox` reports all 928 word boxes inside the page
(extents x=27.36–584.642163, y=29.026091–601.387654 points). A 150-dpi
render was visually inspected: the full two-column content and footer fit
without clipping. TeX emitted the same four font-size substitution warnings
recorded in the original candidate build; it emitted no overfull or underfull
box warning. Current sizes are 5,359 TeX bytes and 153,879 PDF bytes; the
`pdftotext -layout` nonwhite count is 2,871.
