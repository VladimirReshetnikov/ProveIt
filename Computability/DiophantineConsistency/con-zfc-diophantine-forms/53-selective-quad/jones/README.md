# Thirteen-integer Jones equation with a seeded guard stack

Canonical result: `generated/signed_seeded.json` has exactly 13 unrestricted
integer variables, 759 live binary operations (520 multiplication, 215
addition, 24 subtraction), and exact total degree 57,866,184.
Its lack of integer zeros is equivalent to Con(ZFC), using the explicitly
identified inherited compiler theorem and Jones ratio interface. This is an
ordinary mathematical proof, not a new kernel-checked theorem or a consistency
proof. It is not a variable-count record or a global minimality claim.

Read `section.tex` or the standalone `report.pdf` for the complete equation,
universal carry proof, square-threshold calibration, signed-domain recovery,
cofinal odd base construction, and exact-degree argument.

Main new combinations:
- Selective quadratic coefficient isolation, rather than full B2/B4 uniqueness.
- Sparse target padding with an explicit borrow-invariant test.
- A two-block central-binomial code whose block scale 2b makes its threshold
  a polynomial square with the quadratic radix B = 2^2134940 b^2.
- Seed the three sign guards with the already required a0 square condition,
  so only two radicals, rather than three, remain in the final norm.

The seeded norm handles every zero and sign branch. In particular, a0 is
explicitly included in the nonzero multiplier. Its residue is NOT assumed
1 modulo 4. The proof uses a rational square identity, not an unproved
separation assumption.

## Rebuild and audit

From this directory:

    python build_jones.py
    python check_jones.py
    python -O check_jones.py
    pdflatex report.tex
    pdflatex report.tex

The Python code requires only the standard library. The neighboring
`weights/code_v1.json` must be included for the canonical-tuple consistency
check. `CHECK_RESULTS.json` records finite implementation audits, not an
unbounded solution search. The independent signed finalizer audit is supplied
by the aggregate package under `root_checks/`.

## Fixed data and provenance

`FIXED_BINDING.json` identifies the complete four-port tuple and two additional
power-of-two constants. Coefficients are finite recipes, not unknowns.
`SOURCE_PINS.json` records byte-authenticated source files at commit
124c07c0b77a9e20e84676514d8b1ff78536ea3f. The original package31 source uses
positive coordinates shifted by n_i+1; package45's additional transport shift
is not used. See `licenses/` and the inherited proofs for attribution.

## Comparison baseline

`generated/signed.json` is the same carry/Jones construction with the known
unseeded three-root finalizer: 13 integers, 770 operations, degree71,382,096.
Its independent degree certificate is `generated/signed_degree.json`.
The seeded improvement saves 11 operations and 18.93% degree relative to that
baseline. The separate nine-positive-variable construction is a sibling
package, not an alternative interpretation of this integer polynomial.

All named intermediates are polynomial abbreviations. Fixed powers are
expanded in the emitted circuit; no variable exponents, roots, divisions,
quantified coefficients, hidden witnesses, or conditional coefficient choices
occur in the final polynomial.
