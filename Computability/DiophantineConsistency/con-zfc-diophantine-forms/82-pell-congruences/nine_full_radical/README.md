# Full-radical polynomial majorant for Con(ZFC)

**New explicit companion equation:** nine strictly positive integer unknowns,
exact degree **1,158,228**, **726** live binary arithmetic operations.

The equation is `laurent9_positive.json`. `PROOF.md` gives the complete new
majorant theorem, its application, exact degree, logical scope, and fixed
coefficient binding. Compared with package71's 1,379,730 / 478-operation form,
this is a **16.0540% degree reduction at higher arithmetic cost**.

The new mathematical step approximates the complete Pell radical sqrt(DFI),
clears a variable denominator by C^7, and certifies positivity by complete
integer polynomial expansions. It does not add any existential variables.

## Verify

Python 3.10+ with the standard library is sufficient:

```sh
python3 verify.py
```

The independent verifier checks the complete majorant and defect expansions,
all 41,853 positive cone coefficients, the 110-term compact identity, the
literal DAG's new components and source preservation, the exact degree and
leading coefficient, coefficient byte hashes, byte-exact reconstruction of
all four fixed coefficients in a temporary directory, and the operation count. It is
also valid with `python3 -O verify.py`. This finite audit does not decide
consistency and is not a new proof-assistant formalization of the inherited
native compiler.

## Regenerate

```sh
python3 laurent_symbolic.py
python3 check_laurent_cone.py
python3 build_correction.py
python3 build.py
python3 verify.py
```

The first two scripts display exploratory coefficient statistics while
regenerating the literal tables. The final independent verifier is the release
gate. The fixed coefficient generator, literal transition/tile inputs, and
compressed integer payloads are included under `upstream/31-sun10/coefficients`.

The repository comparison and imports are pinned to
`cf4a5218a5a4e4358d3f5314151b6b05d4aa384e`. The inherited files retain their own
earlier mathematical calibration pins and notices.
