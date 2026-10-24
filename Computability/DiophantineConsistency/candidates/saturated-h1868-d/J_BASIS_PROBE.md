# Affine J basis: no shorter evaluator found

A further finite probe replaced A by (J+5)/4 in the263-term D-reduced
table, using the already computed J=4A-5. All143 A-free terms and120
A-linear terms were substituted exactly with rational arithmetic. The
result still has263 nonzero terms and common coefficient denominator4.
Thus4P has an integer J,C,D,i,Z representation.

Exhausting all120 coordinate Horner orders with the existing exact DAG
builder gives a minimum raw count954, at order Z,i,D,C,J. This ties the
current D-reduced evaluator before its shared norm rewrite. A valid new
whole equation would additionally need its radical scale multiplied by4
to match4P; that change was not materialized because the probe found no
operation advantage. It would define a different polynomial and require
the generic scaled-majorant existence argument, rather than an identity
to the current parent.

This is a finite cost probe, not a new calibrated equation, a lower bound
over other factorizations, or a polynomial-equivalence certificate. The
checked953-operation circuit remains the working lower-degree candidate.
