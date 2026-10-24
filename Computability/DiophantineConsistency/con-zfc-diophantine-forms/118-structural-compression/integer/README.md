# Symmetric four-root norm evaluators

This packet reduces three existing unrestricted-integer Con(ZFC) evaluators
without changing their polynomials. The preferred compact variants are:

- 13 variables, exact degree 536: **135 to 126 operations**.
- 12 variables, exact degree 1200: **145 to 138 operations**.
- 12 variables, exact degree 1456: **141 to 137 operations**.

COMPACT_NORM_ADDENDUM.md credits and proves the retained 28-operation norm
schedule and its new common-scale adapters. The preferred literal endpoints
are compact_trace13.json, compact_scalar12_rational.json, and
compact_scalar12_integral.json. PROOF.md supplies the complete thirteen-
variable specification and an independent fully symmetric 29-operation
identity. Its symmetric_trace13.json and symmetric_scalar12 variants remain
as alternatives costing one additional operation each.

Every integer coefficient is fixed. The complete six-port tuple is included
under coefficients/, with the original binding and source license retained.
The ordinary consistency calibration is inherited from the identically
equal pinned parent polynomials; no new Lean or object-ZFC certificate,
global optimum, or consistency assertion is claimed.

Run `python3 verify_symmetric_norms.py` from this directory. It needs only
the Python standard library and proves complete tail equality by sparse
polynomial arithmetic, rather than by numerical sampling. The builders
reproduce the three literal DAGs. SOURCE_PINS.json and VERIFICATION.json
record provenance and exact verification.
