# Centering the final radical

This self-contained equation component contains four ordinary polynomial circuits in ten unrestricted integers, their actual fixed coefficient payloads, an algebraic correctness proof, and independent authored checks. It composes the new short guard (see ../source/short_guard) with integral polynomial square completion.

| Circuit | Binary operations | Exact degree |
|---|---:|---:|
| integer10_polar.json | 471 | 1245324 |
| integer10_center0.json | 485 | 1179788 |
| integer10_center1.json | 496 | 1114252 |
| integer10_center2.json | 545 | 1080888 |

The lower-degree equations are cost/degree tradeoffs. They are not claimed globally minimal. The short-guard replacement preserves existential solvability by its separate soundness/completeness proof. Each centered equation then follows by a bijective translation of the last integer variable. The inherited ordinary mathematical consistency calibration is recorded in BASELINE_PROOF.md; no new Lean/Rocq certificate is claimed.

Rebuild and check with Python3 and SymPy:

    python build.py polar
    python build.py center0
    python build.py center1
    python build.py center2
    python check.py
    python -O check.py

build.py uses only vendored inert data and the authored circuit helper. check.py imports neither builder nor helper and independently evaluates the complete native prefix, verifies universal polynomial identities, integral coefficients in halfA, actual fixed numerals, topology, backward liveness, operation counts and attained exact degrees. The source/library licenses are preserved. PDF-ready text is section.tex, with full details in PROOF.md.
