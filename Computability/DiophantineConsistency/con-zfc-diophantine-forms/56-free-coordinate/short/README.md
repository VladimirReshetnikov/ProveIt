# New short-circuit tradeoffs

The principal new candidates use fifteen strictly positive unknowns:

| Circuit | Operations | Exact degree | Fixed tuple |
|---|---:|---:|---|
| `generated/ordinary_gap_minima73_squared_modulus_degree54.json` | 73 | 54 | Complete package31 |
| `generated/gap_minima74_squared_modulus_degree46.json` | 74 | 46 | Complete package31 |

Every addition, subtraction and multiplication, including multiplication by
a fixed coefficient, is charged. There are no arithmetic tests or variable
exponents hidden in these schedules.

Read `PROOF.md` for the explicit equations, complete new arithmetic proof,
exact degree certificates, and inherited semantic dependencies. The two new
principal points combine the incoming minimum-norm and squared-modulus
reductions, with a further regrouping of the main norm that saves one gate.
They are new bounded tradeoffs, not a claim of globally simplest equations.

Run `python3 build_and_audit.py` or `python3 -O build_and_audit.py`.
The verifier writes deterministic JSON schedules and `generated/AUDIT.json`.
Original source bytes and their provenance are in `upstream/` and
`SOURCES.json`; materialized whole coefficient tuples, builders, source
proofs and original licenses are in `coefficients31/`. Both new polynomials
bind to that one complete tuple. The copied squared-modulus proof was
originally stated for the normalized package-36 circuit; our proof explains
its use on canonical package-31 ordinary witnesses.

No new proof-assistant compilation or checked object-ZFC derivation is
claimed. The Con(ZFC) equivalence imports the inherited mathematical
compiler and K215 calibration; the finite audits certify literal arithmetic
and metrics only.

New synthesis text and verifier are AI-assisted mathematical work, released
under MIT-0. Inherited files retain their original notices and licenses.
