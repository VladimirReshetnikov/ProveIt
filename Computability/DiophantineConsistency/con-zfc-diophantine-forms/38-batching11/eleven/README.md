# Eleven positive unknowns by index absorption

A single polynomial has exact degree **1154** in **11 strictly positive integer unknowns**, evaluated with **123** binary arithmetic operations. The two-equation versions have residual degrees **2,1152** and use **119 operations**, or **118** with the proved transport-coordinate shift. The full formulas and proof are in `ELEVEN_POSITIVE_PROOF.md`.

The former supplied index quotient h is encoded through the existing norm carrier; a short-range Pell-index argument reconstructs its full divisibility. It is not set to a constant or ignored. The unchanged K215/blank-compiler theorem and signed-quotient interface remain identified dependencies. This is an ordinary mathematical proof formalizable in ZFC, not a new end-to-end proof-assistant certificate or a consistency proof.

## Reproduce

From this directory, with Python 3.10 or later and no third-party packages:

    python3 build_eleven.py
    python3 check_eleven.py

The checker reads all four sibling compiler payloads and verifies their hashes before testing the norm at their actual fixed residues. Generated JSON files enumerate every gate and every supplied variable. `generated/CHECK_RESULTS.json` records the finite diagnostics; these do not replace the unbounded proof.

The current coherent binding is `../compiler/COEFFICIENT_BINDING.json`; MF is the shifted high mask and K0 aliases its K payload. Never substitute only part of a tuple.

## Comparison

This removes one supplied variable and one equation from the repository's direct twelve-positive Pell-norm family. It does not beat the separate Jones nine-variable or cited Sun ten-integer bounds, the twelve-positive degree 1022 record, or the historical 67-operation single-equation record. Exact source pins and predecessor notices accompany the proof.

## Optional lower-degree companion

`build_eleven_translated.py` and `check_eleven_translated.py` reproduce a separate **degree 1140 / 129-operation** polynomial in the same eleven positive variables. Its shifted two-equation system has degrees 2,1138 and 124 operations. `OPTIONAL_TRANSLATION_PROOF.md` proves the positive carrier translation and its exact degree. The main 123-operation circuit is unchanged.

    python3 build_eleven_translated.py
    python3 check_eleven_translated.py
