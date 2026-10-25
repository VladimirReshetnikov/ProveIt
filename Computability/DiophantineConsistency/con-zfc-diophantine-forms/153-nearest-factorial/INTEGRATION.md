# Integration into ProveIt

This is a standalone research submission prepared on 25 October 2026. Its
comparison snapshot is `3ecd6a6cf53d47519228328567f45fb7ee9781d9` in
`VladimirReshetnikov/ProveIt`. It does not modify a remote branch, open an
issue or pull request, or overwrite an existing research package.

## Suggested intake

The delivered ZIP can be placed in `docs/incoming` using its descriptive
filename. After review, its single top-level directory can be copied beside
the existing contributions under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms`.
The repository maintainer should assign any numbered package name according
to the current intake sequence. This submission does not reserve or invent
a new package number, and no earlier package should be replaced.

Preserve the relative paths within the package. The component verifiers,
coefficient bindings, frozen transformation certificates, and report builder
use those paths. The release can be verified offline before choosing its
permanent repository location.

## Mathematical content to review

The principal contribution is the signed nearest-factorial reduction in the
direct C222 arithmetic certificate. Review the new proof in the article and
`direct/proofs/NEAREST_FACTORIAL_PROOF.md`, including the q=1, F=0, and
negative-B exclusions and the construction of all twelve entries in the
common norm bound. The exact final choices are:

- `direct/equations/P242/equation.json`: 242 unrestricted integers, 178
  quadratic residuals, degree four, 17,026 collected terms, height 38,432.
- `direct/equations/P243/equation.json`: 243 unrestricted integers, 179
  quadratic residuals, degree four, 6,877 collected terms, height 11,856.

The former saves one further coordinate; the latter is the more balanced
support/height choice. Both improve dimension and height against the
252-variable common-remainder parent, but both have a larger expansion.
The credited common-remainder, odd-square, coordinate-shear, and affine-row
techniques are predecessors. The new result is their composition with the
signed nearest-factorial proof, not a claim to have invented each ingredient.

The `signed/` component provides distinct degree/operation tradeoffs at
14, 13, and 11 unrestricted integer variables. Keep their stated operation
costs and their large fixed-coefficient bindings with the equations. Their
semantic proof and native ancestry differ from the direct C222 branch.

The `compact/` component is a shorter evaluator of the same existing
10-positive-variable, degree-382 polynomial. It should be catalogued as an
80-to-79 operation reduction, not as a new polynomial or a result over all
integers.

## Reproduction and acceptance boundary

Run from the extracted package root:

```sh
python3 -B verify.py
python3 -B verify.py --rebuild
python3 -B -O verify.py --rebuild
python3 -B build_report.py
```

The first three commands validate finite artifacts and deterministic
reconstructions. The last rebuilds `report/report.pdf` from the editable
source and authoritative equation data. Arithmetic checks use Python's
standard library; the PDF build additionally requires pdfLaTeX.

Successful finite replay establishes the supplied polynomial identities,
source bindings, inverse certificates, coefficients, and metrics. It does
not replace review of the unbounded arithmetic proof or its inherited
logical calibration. In particular, this package is not a newly checked
end-to-end proof-assistant endpoint and does not prove Con(ZFC).

Any repository status page should retain this distinction. It can record a
complete ordinary ZFC-formalizable construction with exact finite artifacts
without claiming that the full C222-to-polynomial bridge has been newly
formalized. The retained formal interfaces and scoped internalization review
are source evidence for that boundary.

## Attribution and preservation

Keep `NOTICE.md`, the component provenance and source-binding ledgers, and
all retained licenses and notices with redistributed copies. In particular,
the direct and native branches have different source closures. Do not mix
coefficient tuples from different scalar constructions. `RESULTS.json`
identifies the authoritative paths and domains of the final endpoints.

The generated metric and residual inputs under `report/` derive from the
literal equations. Changes to an equation require corresponding proof,
certificate, coefficient-expansion, result-inventory, and appendix updates.
Do not edit generated counts merely to match a proposed claim.

Research questions for follow-up include reducing the support cost of the
fourth affine projection, simplifying the remaining two gap certificates
without circular sign recovery, applying the nearest-factorial mechanism in
a new direct compiler, and formalizing the complete arithmetic/calibration
chain end to end. They are open directions, not assumptions in the supplied
results.
