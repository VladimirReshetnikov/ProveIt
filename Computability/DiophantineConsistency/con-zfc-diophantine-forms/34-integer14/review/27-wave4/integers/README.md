> Release binding: all new generated artifacts in this directory use the complete mixed-radix Wang943 tuple, B=2^(5^9), selected by COEFFICIENT_BINDING.json. Historical source tuples mentioned below document predecessors or valid alternatives, not the selected numerical instance. The sibling coefficients/COEFFICIENT_PROOF.md proves the full adapter and simultaneous canonical restrictions.

# Integer-domain synthesis

Read INTEGER24_PROOF.md for the primary result: a 163-operation polynomial in 24 unrestricted integer variables, degree 2432. Its three-comparison presentation costs 158 operations and has maximum residual degree 2416.

INTEGER24_SPLIT2_PROOF.md gives a lower-degree tradeoff: 164 operations, degree 2256, still 24 integers. It changes the first-root separating coefficient from HL to 2HBnd and costs one additional binary multiplication. The corresponding three-comparison system costs 159 operations and has maximum degree 2240.

INTEGER24_RATIO_WEIGHT_PROOF.md gives a further tradeoff: 168 operations, degree 1936, still 24 integers. Its three-comparison system costs 163 operations and has maximum degree 1920. This uses a sign-safe bound relative to the main square root rather than an absolute bound.

LOW_DEGREE_PROOF.md gives 51-integer quartic, 42-integer sextic and 36-integer octic sum-of-squares equations, improving the previous 54/45/39 lifts. All respective residuals are explicit in the JSON files.

Run with Python 3 standard library only:

    python build_integer24.py
    python build_low_degree.py

Proofs use the coherent package 23 T5263 coefficient quartet at the pinned repository commit. It is specified by finite integer recipes, not supplied as four existential variables. SOURCE attribution, whole-tuple restrictions and current verification scope are in PROVENANCE.json and the proof notes. A smaller authentic compiler quartet can replace it only as a whole and after verifying the listed parity/population hypotheses.

Operation convention: every binary +,-,* costs one, including multiplication by numerals. Comparisons are free. The _system_comparison variant compares N00 with GN11 and saves the otherwise unnecessary final subtraction. _system computes the norm N and compares it to zero. _system_residual explicitly computes all three zero residuals. _product and _sos are single-polynomial presentations.

This is an ordinary mathematical reduction using the source Pell and compiler results, not a new end-to-end proof-assistant certificate, a claim of global optimality, or a proof of Con(ZFC).
