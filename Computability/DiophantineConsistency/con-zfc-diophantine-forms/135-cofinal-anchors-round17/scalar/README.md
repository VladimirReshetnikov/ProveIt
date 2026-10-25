# Linear cofactor saturation

Four recommended ordinary integer polynomials use exactly eleven unrestricted integer unknowns:

- free_cofactor11_sharp.json: degree 328, 130 binary arithmetic operations.
- free_cofactor11_simple.json: degree 340, 129 operations.
- free_cofactor11_none.json: degree 352, 125 operations.
- weak_cofactor11_none.json: degree 398, 121 operations.

The two other weak-scale files are dominated controls, not additional frontier claims. A binary addition, subtraction or multiplication costs one, including fixed scalar multiplication and squaring; integer/variable leaves and reuse are free. All eleven variables and all six fixed numerical coefficients are live.

PROOF.md gives the complete ordinary arithmetic equivalence and the exact inherited native/compiler/refutation boundary. The new idea is linear cofactor saturation B=r A Dm, combined with a coprime product and an exact centered two-root norm. The complete authentic source34 numerals, reconstruction recipe, ordinary dependencies, provenance and original licenses are included. No minimum or proof-assistant claim is made.

Replay with Python 3 and its standard library:

    python replay.py

The replay authenticates the release files, builds and checks a fresh isolated copy in normal and optimized Python, and compares the actual output bytes. For individual steps use python build.py, python check.py and python -O check.py. The producer is not imported by the independent checker. CHECK.json and CHECK_OPTIMIZED.json contain the all-gate degree and actual nonzero-leading-coefficient certificates, local exact polynomial bindings, coefficient authentication, complete finite recipe replay, norm identities and rejected formula mutations. Finite tests are not substitutes for the unbounded proof.
