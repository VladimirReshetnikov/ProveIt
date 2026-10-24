# Scaled-root compression for Diophantine consistency

Main result: an explicit polynomial in **17 unrestricted integers**, exact
degree **112**, with five squared residuals. Its integer solvability is
equivalent to the cited parent consistency equation. The complete new
ordinary arithmetic proof is in `PROOF.md`.

The new mechanism merges the first and auxiliary Pell roots. Scaling one
root by the existing integer I makes equality of the two radicands
impossible modulo I^2. Rational-square integrality and an elementary Pell
descent then recover genuine integer witnesses. The companion equation in
18 integers has degree 80. A secondary 17-integer degree-110 equation
uses 140 operations, compared with 124 for the degree-112 equation.
Four transport projections improve the
variable/degree pairs to 21/16, 20/20, 19/32, and 18/88.

## Reproduce

```sh
python3 -m pip install -r requirements.txt
python3 build.py
python3 circuit.py
python3 verify.py
python3 -O verify.py
python3 independent_review.py
```

`forms/` contains the full inlined polynomial packets, ordered coordinate
lists, fixed-port references, degree certificates, and compact displays.
`coefficients/` contains the actual six fixed integer numerals as compressed
minimal unsigned little-endian bytes. `SOURCE_PINS.json` authenticates the
exact incoming archive and copied parent packets. `certificates/` records
finite checks. No explanatory register is an additional quantified
unknown. All powers in a packet have fixed nonnegative integer exponents.

The inherited native tableau/compiler and ZFC-refutation calibration
remain mathematical dependencies. No new end-to-end Lean/Rocq certificate,
global minimum, or priority over all mathematical literature is claimed.

Do not distribute `.runtime/`, `__pycache__/`, or temporary logs; they are
local build dependencies, not part of the mathematical deliverable.
