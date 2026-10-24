# Nine-positive-variable composition

**One explicit polynomial: 9 positive variables, degree 1,379,730, 478 live
binary arithmetic operations.** A nonnegative version has 485 operations.

Read `PROOF.md` for the definition and complete composition/degree argument.
The authoritative polynomial is `generated/composed9_positive.json`.
All registers are abbreviations. Exact fixed coefficient values are supplied
under `coefficients/payloads/`, together with the finite generator.

Run, with Python 3.10+ and its standard library:

```
python3 coefficients/build_coefficients.py
python3 build_composed.py
python3 check_composed.py
python3 -O check_composed.py
```

The native generator reconstructs the complete original31 tuple; do not
substitute individual compact-tuple ports. `MF_source` is already shifted.
`VERIFICATION.json` records the exact finite checks. No consistency search
or new proof-assistant certificate is claimed.

The construction composes source 65, majorant 63 and power rewrite 62 from
ProveIt snapshot `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`.
The three unchanged upstream proof texts preserve their original paths and
context. The current paths and formulas in `PROOF.md` are authoritative for
this new composition. `PROVENANCE.json` identifies all reused files.

This is a new combined polynomial and quantitative improvement, not a new
native compiler, new variable bound, or global simplicity minimum.
