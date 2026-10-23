# Nine-variable parity-calibrated consistency equation

Primary outputs:

- `generated/calibrated_natural.json`: nine nonnegative inputs, exact degree 7,344,328, 744 binary operations.
- `generated/calibrated_positive.json`: nine positive inputs, same degree, 738 binary operations.
- The corresponding `_certificate.json` files are exactly equal polynomials with cancellation-resolved expressions; `_degree.json` records exact degrees and diagonal leaders.
- `PROOF.md` is the full mathematical proof, including alternatives and dependency boundaries.
- `section.tex` can be included in a larger paper. `report.tex` and the visually checked five-page `report.pdf` are standalone.

All gate inputs are fixed integers or one of the nine variables. The circuit schema is a topologically ordered list of `literal`, `fixed`, `variable`, `add`, `sub` and `mul` nodes. A binary gate reads `left` and `right`; `output` is the output node. Fixed recipes, fixed power-of-two exponents, variable domain, and operation counts are embedded in each JSON. The named nodes are abbreviations, not extra unknowns.

The complete fixed tuple is authenticated by `COEFFICIENT_BINDING.json`. All four gzip payloads decode as little-endian unsigned integers. Recipe ports are beta, K0=K, MC, MF=MF_source. MF is already shifted. Never mix one port from a different compiler tuple or apply another MF shift.

Reproduce without a network or third-party Python packages:

    python3 build_nine.py
    python3 verify_nine.py

Both commands also pass under `python3 -O`. `STANDALONE_REPLAY.json` records a fresh isolated-directory replay of this entire folder with no sibling dependencies. `generated/VALIDATION.json` contains the finite audit results. With a normal TeX Live installation, run `pdflatex report.tex` twice.

Other fully bound comparison outputs are included:

- `three_*`: conservative three-block carry, degree 12,023,320; positive form 734 operations. This remains a degree/operation tradeoff point.
- `two_*`: uncalibrated square-base two-block carry, degree 14,687,132; positive form 740 operations. This is dominated and is included only to document why parity calibration matters.

The main new idea is L=2b B^5741 rather than L=B^5741: the extra b in the block length makes the exact popcount threshold a polynomial square while retaining a linear unrestricted natural base parameter. With B=2^2134940 b^2, the ratio threshold root is N=2^16012040 B^2966. L and N must not be confused.

This is a classical reduction formalizable in ZFC, using the explicitly stated inherited compiler and Jones ratio theorems. It does not prove Con(ZFC), claim a global minimum, claim an unrestricted-integer nine-variable result, or claim a fresh end-to-end kernel-checked theorem. The finite audits do not decide consistency.
