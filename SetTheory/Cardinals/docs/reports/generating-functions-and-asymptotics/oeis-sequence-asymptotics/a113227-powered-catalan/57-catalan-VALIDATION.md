# Validation record

Date: 1 October 2026.

## Mathematical and numerical checks

The independent mathematical verification record identifies the exact reviewed TeX source. The report's proof supplies the asymptotic claims; the computations below are diagnostics.

- Exact symbolic reciprocal-product and Stirling expansions reproduce the displayed residue coefficients
- Independent Gaussian-moment extraction reproduces c_1 and c_2 and supplies c_3 and c_4
- Exact integer recurrence evaluated through n=2500, with leading and first/second correction comparisons
- 110-digit spectral computation with 65 nodes reproduces total mass to the printed 50 digits and moments through n=30
- Inverse approximations H_0, H_1, H_2 checked against exact targets through n=500
- Numerical scripts include explicit diagnostic assertions on spectral mass and moment errors

## PDF checks

- All 14 final pages rendered and visually inspected
- A second independent visual pass inspected the full report and the final changed pages
- No clipped equations, overlaps, missing mathematical glyphs, or overflow found
- Final TeX build reports no overfull boxes, underfull boxes, or unresolved-reference warnings
- The Bessel square-root typesetting and the EGF cutoff argument were corrected during review before finalization

Reviewed TeX SHA-256:
2feb8e8de0603df2b8c47ef892caccf7d5bacfb542559f706039ce787eb7382a

Rendered PDF SHA-256:
f3f0c49f9b06b773120250b33eda2092b342c79f04cd526df0ad8800f3084454

The release file manifest records hashes for the report, code, outputs, and verification records. Numerical diagnostics are not certified intervals. The exact inverse requires an explicit asymptotic-remainder bound in addition to a Newton residual for a certified finite-target enclosure.

## Clean replay

A fresh-directory replay completed all symbolic calculations, all numerical tests, and the PDF rebuild. Every file listed in the release manifest was byte-identical before and after replay, including the PDF and generated numerical outputs. The replay used the dependency versions recorded in environment.txt. This establishes reproducibility on the tested toolchain; it is separate from the mathematical proof and from interval certification.
