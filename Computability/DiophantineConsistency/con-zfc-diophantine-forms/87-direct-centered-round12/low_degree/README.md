# Low-degree unrestricted-integer consistency equations

Read PROOF.md. Literal single polynomials are the sums of squared residuals in integer*.json. All fixed numeral payloads are included in coefficients/ and bound by BINDING.json. Full ordered variable lists and restoration maps are in each packet.

Reproduce from this directory:

    python3 build.py
    python3 check.py
    python3 -O check.py

The builder requires SymPy; the independent replay uses only Python's standard library. No upstream code is imported or executed. New endpoint proofs are mathematical, not newly compiled Lean/Rocq certificates. The retained inherited proofs identify the complete native/Pell compiler dependencies.
