# Eleven unrestricted integers by parity and centered interpolation

This component supplies an ordinary fixed integer polynomial in 11 unrestricted integer variables, exact degree 2240, evaluated by 206 live binary additions, subtractions, and multiplications. Two shorter evaluators trade degree for operations: 2272/204 and 2912/200.

The new construction combines the centered sign budget with the incoming full-residue Pell interpolation. An early rational projection recovers the main root and congruence; four odd radicands can then be combined using fixed parity weights instead of variable magnitude bounds. Two integral coordinate shears lower the degree.

Read PROOF.md for the universal reduction, DEGREE_PROOF.md for exact degree and a nonzero actual-coefficient certificate, and the three `budget_intersective11_degree*.json` files for complete literal circuits. All coefficients are the same six authenticated source-34/source-71 integers as the sibling guard component, including its already-shifted MF. No coefficient is selected by a halting or consistency search.

Composing the new arithmetic reduction with the named inherited ordinary compiler and refutation calibration yields, as ordinary mathematics formalizable in ZFC, equivalence between absence of an integer zero and syntactic Con(ZFC). This does not prove either consistency or inconsistency, and does not claim a newly completed proof-assistant or encoded object-ZFC derivation. No global minimum or historical-priority claim is made.

Reproduce from this directory with:

    python build.py
    python check.py
    python -O check.py

The sibling guard directory is an explicit bundle dependency. Its six complete numeral payloads, finite reconstruction recipe, source notices, and shared arithmetic tools are retained. The checker reconstructs the entire tuple, checks every live gate and input, checks exact front-register cuts and all 20,349 norm coefficients, verifies the exact specialized leading term, and runs separately labelled modular transcription diagnostics including zero strong/guard coordinates.
