# Thirteen-integer CRT and coprime-guard construction

The recommended compact polynomial is `generated/signed_coprime_compact_split_crt.json`: exactly 13 unrestricted integer variables, exact degree 11,543,632, and 518 live binary operations (326 multiplication, 169 addition, 23 subtraction). The fully explained scaled split baseline is `generated/signed_coprime_split_crt.json`, with degree 11,546,112 and 520 operations.

Its lack of integer zeros is equivalent in ZFC to Con(ZFC), relative to the explicitly inherited fixed compiler theorem and Jones ratio interface. This is an ordinary mathematical proof, not a consistency proof, a newly kernel-checked theorem, or a global minimality claim. No 12-variable construction is claimed.

## What's new

- Degree-separated sparse kernels use only same-degree support isolation: 89 records, 22,544 verified interactions, maximum source convolution degree 2161. One off-target monomial makes the packed source positive for every signed integer input.
- The last Pell sign guard uses the other square candidate as a coprime spectator: B3=1+4 d3 C2 a1 z3^2.
- This ensures the two final radicands are unequal on every relevant signed branch. Therefore the final two-root norm needs no separating weight.
- An explicit unconditional source-positivity argument closes the a1=0 branch without increasing the nonzero multiplier.
- Combining this with the inherited exact CRT reparameterization H=C+F(B1+jC) removes F from the quintic merger denominator.

Together, the new source and finalizer reduce degree by 80.05% from 57,866,184 and operation count by 31.75% from 759. At the identical old selective source, the finalizer alone reduces degree to 28,847,344 with 754 operations. The spectator-only variant is also included (degree 46,680,720; 758 operations), as are the two unchanged old comparisons. All retain the same coherent original four-port tuple.

Read `section.tex` or `report.pdf` for the complete equation and universal proof. All named registers are polynomial abbreviations, not hidden unknowns. All fixed powers are expanded in the circuit. The source remains the original package-31 positive system, decoded through p_i=n_i+1, with its coherent four-port tuple. It is not silently replaced with the tuple from the CRT source packet.

## Rebuild

    python build_jones.py
    python check_jones.py
    python -O check_jones.py
    python check_source_minimum_independent.py
    python -O check_source_minimum_independent.py
    pdflatex report.tex
    pdflatex report.tex

Python needs only its standard library. `CHECK_RESULTS.json` records literal finite-field replays, exact degree certificates, source hash checks, all 22 formal target identities, 22,544 source interactions, 590,976 signed spectator stack cases, five explicit Pell constructions, all integer source-positivity samples, and CRT identities. These finite checks corroborate, but do not replace, the universal proof.

`SOURCE_PINS.json` and `FIXED_BINDING.json` identify the original compiler and complete materialized coefficients. `CRT_PROVENANCE.json` identifies the later imported CRT argument. Licenses and notices are retained. `INDEPENDENT_SOURCE_REVIEW.md` and its receipts record an additional independent AI-assisted review of the signed source minimum and both calibrations, not external peer review. `ARTIFACT_HASHES.json` covers the complete intended artifact tree, excluding transient TeX, Python, and rendered-image files and the manifest itself.

The recommended compact calibration is proved in the final subsection of `section.tex` and `report.pdf`, and documented separately in `COMPACT_CALIBRATION_PROOF.md` and emitted as `generated/signed_coprime_compact_split_crt.json` (13 integers; degree 11,543,632; 518 operations). Its signed source register is used only squared; the positive Jones parameter is its absolute value in the proof, never an absolute-value gate in the polynomial.
