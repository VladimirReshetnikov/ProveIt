# Integer low-degree consistency equations

This self-contained component delivers five fixed integer polynomials:

| File | Domain | Variables | Degree | Residuals | Binary gates |
|---|---|---:|---:|---:|---:|
| `sextic31.json` | all integers | 31 | 6 | 18 | 144 |
| `octic26.json` | all integers | 26 | 8 | 14 | 131 |
| `degree10_24.json` | all integers | 24 | 10 | 12 | 135 |
| `degree12_23.json` | all integers | 23 | 12 | 11 | 122 |
| `degree14_22.json` | all integers | 22 | 14 | 10 | 123 |

The single equation in every case is the sum of the squares of the listed
residuals. The fixed six-numeral tuple is fully materialized in `coefficients/`.
The corresponding `_circuit.json` files are compact division-free binary
arithmetic evaluators. `degree12_25.json` is a retained, dominated intermediate
used to document the exact elimination chain, not a recommended endpoint.

`PROOF.md` displays the complete 23-variable equation and proves the new
composition. It states the inherited compiler, Pell, and ZFC-calibration
dependencies. This is an ordinary mathematical construction with exact finite
algebra checks, not a new end-to-end proof-assistant certificate.

Run with Python 3 and the standard library only:

    python3 build.py
    python3 circuits.py
    python3 verify.py

All checks remain active under `python3 -O`. There is no refutation search and
no attempt to prove consistency by bounded testing. Proof-only witness
choices do not add functions to the delivered polynomials.

Source snapshot: ProveIt `2605669a532342f153b13eb6b4a0af4b54f5fa37`.
The construction combines source75's signed bootstrap, source71's calibrated
determinant guard, and source68's simultaneous-positivity lemma. It adds the
explicit composition, the 31/26/23-variable elimination chain, a nonzero-scale
main-norm replacement and root shear giving 24 variables at degree ten, and
an auxiliary strong-norm row operation giving 22 variables at degree fourteen.
It does not claim the inherited mechanisms were first discovered here.

