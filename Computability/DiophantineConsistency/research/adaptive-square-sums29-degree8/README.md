# Candidate: 29 variables, degree eight, 135 circuit operations

This graph is a candidate: its Lean model transport and native consistency
endpoint have matched guarded historical replays with independent artifact
audits. The proof snapshot and provider qualifications below remain important.
It removes `fSquareVariable` from the verified 30-variable graph, substituting
the defining product `f*f` and deleting the resulting zero constraint. The
model witness construction uses positivity of the product of two positive
model elements. See the [proof and replay status](../adaptive-aq29-proof/README.md),
including the failed initial run and later fresh project-source pair.

`generate.py` pins the parent graph and constructs the 29-variable, 135-operation live DAG. `verify_substitution.py` checks all 21 parent residuals by exact integer polynomial arithmetic, including that the omitted residual vanishes. `verify_degree.py` checks exact degree eight after the positive shift, with a port-independent leading monomial. These finite computations do not themselves establish zero-set equivalence in nonstandard models or an iPRA theorem. The graph hash is `894ff6fa3205629c03de826d8984f4959c2be317bf61c46d0f393f770d113a20`; no minimum is claimed.
