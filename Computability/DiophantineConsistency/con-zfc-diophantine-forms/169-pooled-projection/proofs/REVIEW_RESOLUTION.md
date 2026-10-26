# Resolution of the manuscript review

The separate report review is preserved in REPORT_REVIEW.md. Its findings
were incorporated before the final PDF build:

- The ambient affine Pell-coordinate map is now stated as U=X-Z. The equation
  Z=AY identifies it with X-AY only on the common zero set.
- The sparse-format degree limits now explicitly refer to individual
  monomial index lists.
- Integer-domain language is restricted to the delivered equations'
  independent unknowns; syntax variables are explicitly natural.
- The strict-range CRT argument identifies each full prime power of B.
- The prime-power range lemma explicitly assumes positive k and e.
- The uncentered internal comparison was removed; only delivered equation
  metrics are used in the main comparison.

The reconstructed 27 JSON files agree byte for byte with the supplied files.
The first packaging-only rebuild attempt serialized two affine intermediate
files compactly even though their frozen byte format was indented JSON.
Selecting the original serialization for those two files fixed that mismatch;
no mathematical coefficient or certificate was changed.

Source-import authentication also removed one transport-added trailing newline
from the comparison copy of source 158, restoring its exact Git blob identity.
All 28 retained repository inputs now pass both Git blob and SHA-256 checks.

A late source comparison and dependency-boundary review led to three further
wording corrections, all incorporated in the final sources:

- The detailed composition proof now also uses the affine map U=X-Z and
  identifies U=X-AY only through the retained gate equation.
- The verification section attributes the new unbounded steps to this
  article and review while retaining the named inherited arithmetic theorems.
- The earlier complete display and P225 comparison are explicitly tied
  to the construction snapshot. A later check at commit
  fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb records the source 160–165
  support/height tradeoffs without asserting a new repository-wide optimum.

These changes do not alter any polynomial or transformation certificate.
