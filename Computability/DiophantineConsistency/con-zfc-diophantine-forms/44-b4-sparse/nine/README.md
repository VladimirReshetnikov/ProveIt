# Nine-variable sparse Jones equation

Final result: exact degree 23,321,536,264; 1,383 operations over nine nonnegative integers, or 1,378 over nine strictly positive integers. These are fixed-coefficient polynomial equations whose lack of solutions is provably equivalent in ZFC to Con(ZFC), under the explicitly imported ordinary compiler and Jones arithmetic theorems. They do not cover nine unrestricted integers.

- `NINE_B4_PROOF.md`: full new universal majorant/finalizer proof and precise semantic dependencies.
- `section.tex`: report-ready mathematical section.
- `build_nine_b4.py`: deterministic circuit generator, using only the Python standard library.
- `verify_nine_b4.py`: exact finite certificates and independent literal modular verification.
- `generated/`: natural/positive circuits, exactly equal telescoping certificate circuits, degree certificates, coefficient aliases, and executed `VALIDATION.json`.
- `SOURCE_PINS.json` and `NOTICE.md`: pinned sources and attribution.

From the package root, run:

    python3 nine/build_nine_b4.py
    python3 nine/verify_nine_b4.py

The shared 31-witness compiler data live in `sun/sources/data/`, the certified weight list in `root_checks/`, and the full common sparse-carry proof in `signed_audit/`. Preserve those sibling folders. JSON degrees and exponents are integers; use integer-preserving parsers.

The selected radix is b=2+epsilon and B=a b^4 with a=2^4269877. Do not substitute earlier b^5 formulas. Finite checks validate the artifacts, not unbounded solvability or consistency. No end-to-end proof-assistant certificate or minimum-size claim is made.
