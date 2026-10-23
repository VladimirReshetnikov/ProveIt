# Nine-variable multi-target quadratic construction

This directory defines a single polynomial whose lack of zeros over nine
strictly positive integers is equivalent to Con(ZFC), with the equivalence
provable in ZFC under the explicitly identified arithmetic/compiler results.
A separate affine translation gives the nonnegative-integer version.

| Domain | Live binary operations | Exact total degree |
|---|---:|---:|
| Strictly positive integers | 788 | 129875980 |
| Nonnegative integers | 791 | 129875980 |

The common diagonal leading coefficient is 2^2050. Operations count every
live addition, subtraction and multiplication, including scalar products
and repeated-squaring expansions of fixed powers. Fixed integer coefficients
are leaves, not free variables. No global minimality is claimed.

## Contents

- `MULTITARGET_NINE_PROOF.md`: mathematical proof and exact degree calculation.
- `MULTITARGET_INSTANCE.json`: parent/target provenance, complete four-port
  tuple, coefficient recipes, signed payload encoding and SHA-256 hashes.
- `generated/multitarget_nine_positive.json` and
  `generated/multitarget_nine_natural.json`: exact straight-line polynomial DAGs.
- `generated/*degree_certificate.json`: equal polynomial DAGs with the main
  cancellation resolved for leading-degree verification; these have a larger
  operation count and are not the advertised primary forms.
- `generated/fixed/*.bin.gz`: all 17 live fixed coefficients as explicit bytes.
- `generated/VERIFICATION.json`: finite-check results, not a kernel certificate.
- `circuit.py`, `build_multitarget_nine.py`,
  `materialize_fixed_coefficients.py`, `verify_multitarget_nine.py`:
  newly authored builder and reproducible checks.

## Reproduction

Run from the release root with Python 3 and SymPy available:

```
python nine/build_multitarget_nine.py
python nine/materialize_fixed_coefficients.py
python nine/verify_multitarget_nine.py
```

The verifier itself requires only Python's standard library. Preserve the
release's relative paths: construction reads `quartic/QUADRATIC_TARGETS.json`,
materialization reads the four port payloads in `sun/upstream/signed10/data/`
and binds the parent at
`review/sources/31-sun10/quartic31/quartic31_system60.json`.
The independent target verifier is `quartic/verify_quadratic_targets.py`.
No downloaded upstream program is executed by these commands.

The finite audits verify transcription, algebraic identities and concrete
payloads. They do not prove consistency, search unboundedly for a solution,
or replace the unbounded mathematical equivalence argument.
