# Four-root elimination: 12 integers / degree 512 / 132 operations

The complete new literal polynomial is `integer12_degree512.json`.
`PROOF.md` gives the full formula, signed-radical separation, rational Pell
integrality, total maps in both directions to the inherited15-variable kernel,
exact leading form and an attained coefficient on the authentic numeral slice.

This is a **method result and within-twelve tradeoff**, not a new global
frontier: versus12/500/139 it saves7 operations at12 additional degrees;
versus12/1084/123 it removes572 degrees at9 extra operations. The existing
11/398/121 point dominates it across variable counts.
The ordinary native/refutation calibration is inherited, not newly formalized.

Run in this directory, Python3 standard library only:

```
python3 -B build.py --check
python3 -B check.py
python3 -B -O check.py
python3 -B reconstruct_coefficients.py
python3 -B -O reconstruct_coefficients.py
```

All commands pass. The exact norm has495 terms. All132 live binary-gate
corruptions are rejected. All six complete numerals (615883 raw bytes) are
reconstructed. No Diophantine zero search, blank-machine execution, network,
or external CAS is used by these commands. The inherited files preserve their
original requirements but need not be executed to reproduce this new packet.

See `CLOSURE_MAP.md`, `SOURCE_PINS.json`, `INHERITED_PINS.json`, the independent
review in `review/`, and report-ready `report_section.tex`.
