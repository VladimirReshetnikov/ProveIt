# Whole-product center: ten positive variables, degree208,116 operations

The complete equation is in equation.json, a literal DAG using only binary
addition, subtraction and multiplication with fixed integer coefficients.
All ten independent variables are strictly positive integers. The exact four
coefficient payloads are in coefficients/, with hashes and little-endian
decoding specified in the equation's binding record.

The new center approximates the whole product E*V, not E alone, and is an
ordinary integer polynomial. ALGEBRA.md gives its short division-free formula,
the exact complete-output identity, and the exact degree calculation.

    python3 -B check.py --receipt /tmp/whole-product-check.json
    python3 -B -O check.py --receipt /tmp/whole-product-optimized.json
    python3 -B review_graph.py

The first two independently check the actual source without importing its
producer. The third uses another polynomial implementation. Source graph
mutations are rejected by algebraic checks even when their operation-count
metadata is refreshed. These checks are not searches for a zero and do not
replace the separately supplied unbounded mathematical proof.

In a working copy, `python3 -B build.py` reconstructs equation.json exactly.
`exact_center.py` supplies further symbolic comparison data for the lower-order
and scale16 alternatives; those experiments are not additional main claims.
The earlier 120-operation comparison evaluator is not part of this submission.

The arithmetic/native boundary is the whole directly indexed BFS943/radix67
tuple retained by parent85.json. Do not substitute arbitrary coefficient ports
that merely satisfy elementary inequalities. The companion article establishes
the new center's validity and composes it with that inherited calibration.
No consistency claim, global simplicity minimum, or new end-to-end formal
kernel certificate is asserted by this finite artifact checker.

This work is AI-assisted. Source attribution is in the parent component and
its retained licenses and source ledger. The main new mathematical mechanism
is the ten-positive-variable quotient center combined with the proved
square-transport budget, followed by a measured division-free evaluator.
Whole-expression centers were already present in the eleven-integer branch
of source packages 153, 154 and 165; no priority for that general idea is claimed.
