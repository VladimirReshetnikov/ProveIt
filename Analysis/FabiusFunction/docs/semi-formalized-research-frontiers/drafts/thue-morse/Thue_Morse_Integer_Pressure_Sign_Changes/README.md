# Infinite Taylor Sign Changes in Integer Thue–Morse Pressure

The PDF proves that, for every integer m >= 2, both even degree classes modulo four contain infinitely many positive and infinitely many negative Taylor coefficients. The positive and negative coefficient subsequences have the same exponential scale, with the separate filtered radii distinguished. The proof is analytic and does not depend on a finite scan.

The finite table gives the exact first negative degree after cancellation for m=2,...,20. It does not establish a large-m scaling law.

## Contents
- infinite_pressure_sign_changes.pdf and .tex: complete seven-page report
- build.sh: ordinary pdflatex build (three passes)
- checks/first_negative_exact.cpp: exact GMP Fourier recurrence, full logarithm, all-order residual checks
- checks/m002.json,...,m020.json: exact eigenvalue and pressure coefficients through degree 10m
- checks/verify_table.py: independent rational pressure conversion and complete first-negative scan
- checks/verify_charpoly.py: independent symbolic characteristic-polynomial calculation for m=2,...,6
- checks/reproduce.py: compile and replay all 19 Fourier cases without overwriting delivered data
- checks/*validation*.json and independent_charpoly_checks.json: executed arithmetic receipts
- SOURCES.md and source_pin.json: version and attribution
- VALIDATION.md and compiler.log: validation record
- SHA256SUMS: file provenance

## Reproduction
The analytic theorem is proved in the manuscript. For the finite table use Python 3, a C++17 compiler, and GMP development libraries:
    python checks/reproduce.py
    python checks/verify_table.py

The independent characteristic-polynomial check additionally uses SymPy:
    python checks/verify_charpoly.py

To build the PDF, use a LaTeX installation providing the packages listed in the preamble:
    sh build.sh

The reported source mathematics is not externally refereed or formally verified. No dominant complex singularity location or sign density is asserted in this report.

