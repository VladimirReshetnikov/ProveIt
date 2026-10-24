# Shared binomial certificates and short carriers for Con(ZFC)

Prepared for Vladimir Reshetnikov and ProveIt, 24 October 2026.
Comparison pin: `45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`, including all
eight then-current archives in `docs/incoming`.

## Results

The report is `report.pdf`; its complete editable source is
`report/report.tex` with the adjacent TeX sections.

| Construction | Domain | Variables | Exact degree | Live binary operations |
|---|---|---:|---:|---:|
| Coprime product in a Pell coefficient | unrestricted integers | 11 | 966 | 111 |
| Same, with smaller index modulus | unrestricted integers | 11 | 882 | 112 |
| Short carrier, direct three-root norm | unrestricted integers | 11 | 488 | 121 |
| Short carrier, centered norm | unrestricted integers | 11 | 464 | 125 |
| Centered norm with smaller index modulus | unrestricted integers | 11 | 440 | 126 |
| Direct shared-binomial quartic | nonnegative integers | 319 | 4 | not optimized |

The 319-variable polynomial is **exactly** the sum of the squares of the
254 quadratic residuals in `direct/equation319/natural/equation.json`.
It has 10,283 collected monomials and coefficient height 86,842,335. Every
coefficient is in the matching `expanded_polynomial.json`, and complete
readable residual/polynomial listings are also supplied. This improves the
latest 349-variable incoming baseline in variables, residuals, terms, and
height. Its six full power certificates replace the baseline's nineteen.

The optional `direct/equation320` companion has 320 natural variables,
255 residuals, 13,828 terms, and height 15,248,812. It is a height tradeoff,
not the selected fewest-variable direct result.

The eleven-variable circuits are complete integer polynomials, with
all six fixed source34 coefficients supplied and reconstructed. Intermediate
register names are polynomial abbreviations, never additional unknowns.
The 464/125 and 966/111 points improve both operations and degree over their
respective incoming 688/126 and 1632/114 baselines. The 440/126 point reduces
the same 688/126 baseline's degree to 440 at unchanged arithmetic cost.

## Mathematical contribution and attribution

The direct architecture uses the same binomial `B=binom(F^2+t,t)` for
the squared-radius factorial fixed point and the reciprocal CRT product.
An independently certified radix validates that binomial before either
intended meaning is assumed. Common Pell residues replace eleven full
numerator-power certificates. The squared-radius factorial lemma itself
is prior work in package 105; the modular-residue mechanism is prior work
in package 108. The full integration and measured equations are new to
the audited baseline. The direct route does not read or simulate K215
or instantiate Jones's universal polynomial.

The small-variable constructions combine powered divisibility and
supported-modulus interpolation with selective coprime fusion, a shorter
index modulus, and saturation of a strong Pell coefficient. Pairwise
coprimality and congruences modulo four recover the missing signs in the
single product equation. Every formerly exceptional zero-coordinate case
is covered in the ordinary proofs.

## Logical claim and limits

With the explicitly retained ordinary native/calculus-to-refutation
calibration, the report proves that each fixed equation has a solution
in its stated domain exactly when ZFC has a finite syntactic refutation.
The no-solution sentence is therefore equivalent in ZFC to Con(ZFC).

This is an ordinary mathematical proof formalizable in ZFC, with exact
finite artifact checks. It is not a proof of consistency, a global
simplicity minimum, a historical priority claim, or a newly completed
Lean/Rocq endpoint. The archive retains all calibration boundaries rather
than presenting finite tests as a proof of unbounded arithmetic.

## Reproduce offline

The polynomial builders and audits need only Python 3's standard library.
No network is used. From this directory:

    python3 -B verify_all.py

The wrapper validates the release manifest, copies the package into a
temporary directory, rebuilds and checks all components, runs normal and
optimized checks, and removes the temporary working copy. It does not
modify the delivered artifacts. It can write its result to an explicit
path with `--report PATH`.

The component READMEs document smaller commands for individual equations.
The inherited coefficient recipe runs normally by design; all new checks
are also exercised with Python `-O`.

To rebuild the PDF with TeX Live:

    cd report
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Run another pass if cross-reference warnings remain. Polynomial and
certificate reproduction is byte-exact; PDF bytes can vary with TeX
versions and metadata.

## Review and provenance

`reviews/` contains separate mathematical audits of the three reductions.
Independent review means a separately tasked research-agent audit in this
workflow, not an external human endorsement. The literal graph and
coefficient checks are independently implemented as documented by each
component. `PROVENANCE.json` records the repository pin and incoming
archive hashes. `MANIFEST_SHA256.json` authenticates the release files.

All inherited licenses, notices, and historical source identities are
retained. No external repository was modified to prepare this archive.
