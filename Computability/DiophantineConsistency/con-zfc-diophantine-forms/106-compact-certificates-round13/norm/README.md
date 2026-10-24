# Four shorter ten integer norm graphs

All unknowns are unrestricted integers. The full fixed polynomial graphs, actual fixed coefficient payloads, exact correctness proof, and independent verifier are included.

| Variant | Binary operations | Exact degree |
| --- | ---: | ---: |
| polar | 467 | 1245324 |
| linear | 470 | 1179788 |
| cubic | 473 | 1114252 |
| sixterm | 507 | 1080888 |

These compute exactly the same polynomials as the corresponding latest pinned short-guard parents, with four or five fewer operations. They are not new variable-count or degree records. PROOF.md also proves that degree1080888 is the minimum among all final-coordinate polynomial translations with this prefix fixed, using the positive-square leading part of the cross term.

Reproduce with Python3 and SymPy:

    python build.py
    python check.py
    python -O check.py

No downloaded upstream code is executed. The new verifier imports neither producer nor graph helper. Actual integer leaves are bound by FIXED_COEFFICIENTS.json. Source/compiler and Pell calibration remain the named inherited ordinary mathematical dependencies; this package does not add a kernel certificate or decide consistency.
