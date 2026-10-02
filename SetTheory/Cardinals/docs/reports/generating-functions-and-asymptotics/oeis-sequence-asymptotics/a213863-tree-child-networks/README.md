# Fixed combining degree tree child networks

Start with `d-combining-asymptotics.pdf`. Its editable source is `d-combining-asymptotics.tex`.

## Scope

For each fixed integer d>=2: a positive amplitude, all finite Airy orders and asymptotic inversion for the word diagonal and maximal-reticulation networks. For total networks at d>=3: the leading equivalent only. No unbounded-d uniformity, convergent infinite expansion, verified d>=3 OEIS accession, or certified numerical amplitude is claimed.

## Contents

- `expanded-proof.md`: expanded derivation notes, with both independent-audit precision repairs
- `reproducibility/mathematical-audit.html`: readable independent mathematical audit
- `reproducibility/mathematical-audit.md`: audit source
- `reproducibility/verify_reduction.py`: exact comparison of source and shifted arrays
- `reproducibility/independent_checks.py`: independent source-array normalization and boundary tests
- `reproducibility/derive_coefficients.py`: exact polynomial-Airy construction
- `reproducibility/numerical_diagnostic.py`: ordinary floating diagnostics, not certified enclosures
- JSON and log files: clean replay results

## Replay

With Python 3 and the packages in requirements.txt:

    bash reproducibility/replay.sh

Build the PDF with a standard pdfLaTeX installation:

    bash build_pdf.sh

The build script puts temporary TeX files under .build. No files outside this directory are needed for the proof or scripts. The binary research report is only a historical comparison; its mathematical argument is not imported as an unproved generalization.

Verify the archive file contents:

    sha256sum -c SHA256SUMS

The included audit is independent research review, not external peer review, publication or formal proof-assistant verification. No frozen binary deliverable was changed and no external publication occurred.
