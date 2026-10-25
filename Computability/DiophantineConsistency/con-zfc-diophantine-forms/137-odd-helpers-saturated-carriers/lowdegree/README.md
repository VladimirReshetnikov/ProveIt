# Two new integer consistency-polynomial tradeoffs

This directory contains two complete fixed division-free equations:

- `equation.json`: 14 unrestricted integer variables, exact degree 88, 119 live arithmetic operations (67 multiplications, 27 additions, 25 subtractions).
- `thirteen/equation.json`: 13 unrestricted integer variables, exact degree 156, 127 live operations (75 multiplications, 27 additions, 25 subtractions).

Both have explicit maps on every zero to and from the identical pinned 15-variable free-scale degree-44 source. Their zero nonexistence is therefore equivalent to syntactic Con(ZFC) under the retained ordinary source34 compiler/calibration theorem. These are reductions, not proofs of consistency, global minima, or new end-to-end formal-kernel certificates.

Read `PROOF.md` and `thirteen/PROOF.md` for full ordinary proofs, exact source maps, canonical completeness, actual nonzero leading coefficients, and dependency boundaries. Each directory includes `section.tex`, `standalone.tex`, and an intentionally included three-page `standalone.pdf`; all six pages were visually inspected. The containing report may re-use the source sections with only label/tag changes documented by its assembler.

## Replay

From this directory, with Python 3 and SymPy installed:

    python build.py
    python review/audit.py
    python -O review/audit.py
    cd thirteen
    python build.py
    python review/audit.py
    python -O review/audit.py

Each build writes its literal equation/specification, and each audit writes `review/CHECK.json`. Normal and optimized stdout receipts are retained. The audits do not import the builders; they independently check all named expressions, exact coefficient attainment, fixed payload bytes, source pins, liveness, operation counts, identities, and gate-mutation rejection. Finite checks do not replace the unbounded proofs.

The six coefficient payloads in `coefficients/` are shared by both constructions and occupy 615883 uncompressed bytes. The `thirteen/` equation explicitly binds to `../coefficients/BINDING.json`; keep that relative directory structure. `source/` contains the pinned immediate source and inherited interfaces, and the containing archive retains the full upstream closure.

## Packaging whitelist

`MANIFEST.json` enumerates the frozen files for this entire branch, including `thirteen/` and both checked PDFs. Do not include `__pycache__/`, TeX `.aux/.log/.out` files, or temporary rendered PNGs. The standalone TeX sources use standard article/AMS/geometry/hyperref packages. `review/PDF_QA.json` in each branch records the visual review; `review/PDF_BUILD.txt` records compilation.
