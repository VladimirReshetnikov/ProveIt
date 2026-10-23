# Positive degree-901 carrier

New twelve-positive-unknown presentations:

| Carrier | Equation degree / operations | System degree / operations | Shifted system operations |
|---|---:|---:|---:|
| Full | 901 / 112 | 892 / 107 | 106 |
| Short | 905 / 110 | 896 / 105 | 104 |

The full carrier improves the pinned degree-1022 / 124-operation form in both metrics. The key new result is a modular obstruction that permits the inner radical multiplier to be exactly one, coupled with an outer weight derived from the identity `(I sqrt(G))^2-(c sqrt(D))^2=I^2-c^2`.

- `PROOF.md`: full mathematical proof, including all positivity and nonzero-denominator obligations, exact leading forms, and inherited interface boundary.
- `section.tex`, `report.tex`, `report.pdf`: concise two-page TeX/PDF presentation for incorporation into the parent report.
- `build_positive.py`: standard-library division-free circuit emitter and ledger auditor.
- `check_positive.py`: independent formal radical algebra, full finite-field polynomial rays, actual fixed-tuple rays, and transport-coordinate checks; requires NumPy.
- `BUILD_RECEIPT.json`, `CHECK_RESULTS.json`: exact metrics and reproducible diagnostics.
- `COEFFICIENT_BINDING.json`: selected whole source31 Wang943 121-by-8801 tuple, already-shifted MF, all four raw and gzip hashes, and explicit path basis.
- `SOURCE_PINS.json`, `SELECTED_TUPLE_SOURCE_PINS.json`: immutable fetched proof sources and selected tuple source pins.
- `upstream/`: historical source proofs and inert code consulted, not executed by the new implementation. Source30 coefficient recipes here are historical only; they are not the selected tuple.

Replay from the full release, retaining its sibling `sun/sources/data` directory:

    python positive/build_positive.py
    python positive/check_positive.py
    python -O positive/check_positive.py

The two programs verify the actual coefficient payload hashes. They never import received upstream programs. Shared payload paths are intentional and declared in the binding; there are no machine-specific paths in the arithmetic programs. The `.tex` sources compile with ordinary pdfLaTeX and standard AMS packages. `section.tex` is suitable for direct inclusion in the parent document.

Scope: ordinary mathematics formalizable in ZFC, not an end-to-end proof-assistant certificate or a proof of Con(ZFC). The inherited compiler/calibration theorem remains a stated dependency. Nine-variable Jones and ten-integer-variable Sun families solve different metric tradeoffs and are not displaced.
