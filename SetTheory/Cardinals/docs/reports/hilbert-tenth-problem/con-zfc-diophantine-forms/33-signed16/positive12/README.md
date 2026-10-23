# Twelve-positive-variable evaluator improvement

`positive12_product108.json` evaluates exactly package 30's degree-1081,
twelve-positive-variable polynomial in **108 binary operations** instead of 111.
The companion unshifted system uses 104 operations instead of 107; the positive
transport-coordinate shift gives a 103-operation system. Every numeral
multiplication and square is charged.

All intermediate register names abbreviate polynomials; they are not variables.
The complete fixed Wang943 tuple remains unchanged and is bound in
`COEFFICIENT_BINDING.json`. The compressed payloads live in the parent
package's `upstream/compiler` directory.

- `PROOF.md`: complete definitions, exact identities, counts, domain-preserving
  shift, degree argument, and explicit inherited semantic proof boundary.
- `build_and_verify.py`: new standard-library-only builder and independent
  arithmetic verifier; run it from any directory.
- `VERIFICATION.json`: successful arithmetic and payload checks.
- `SOURCE_PINS.json`: immutable source commit and hashes of reference files.
- `upstream/`: unmodified previous 111-operation polynomial and original proof.

This reduces evaluation cost, preserving the fixed polynomial. It is not a
new formalization or a global optimality claim. The inherited compiler and
K215 endpoint give the theorem that absence of a positive solution is provably
equivalent in ZFC to Con(ZFC).
