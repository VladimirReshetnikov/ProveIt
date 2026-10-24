# Residue-oriented consistency equations

The recommended main equation is the sum of squares of the 25 quadratic
residuals in `quartic40_direct.json`, over **40 unrestricted integers**. Two exact
projections give a sextic in **34 integers** and an octic in **29 integers**.
Their lack of integer zeros is equivalent to Con(ZFC), by the ordinary
mathematical proof in `PROOF.md` and its explicitly inherited dependencies.

The new idea replaces a square positivity witness by the affine restriction
X_old=3X3-1, implying X=2 mod 3. A sign-uniform
Pell argument first recovers X=+/-2^R with R odd; the congruence selects
the positive value. The dedicated witness in X=2u^2 can then be deleted.
For the low-degree projections, a separate 40-variable form uses
J_old=3J3+1 and w_scale_old=3w3+1 to impose the same residue while
retaining the monic X definition.

| Equation | Integer unknowns | Residuals | Exact degree | Inspected incumbent |
|---|---:|---:|---:|---:|
| `quartic40_direct.json` | 40 | 25 quadratic | 4 | 41 unknowns |
| `quartic40.json` (projection parent) | 40 | 25 quadratic | 4 | 41 unknowns |
| `sextic34.json` | 34 | 19 cubic | 6 | 35 unknowns |
| `octic29.json` | 29 | 14 quartic | 8 | 30 unknowns |

All four fixed integers are supplied and rebuilt from the retained literal
tile list. Every residual is an integer polynomial, with no variable
exponents or unresolved program parameter. The same coherent source34
native tuple is used throughout. MF is already shifted; do not shift it again.

Run, from this directory:

    python3 build_verify.py
    python3 -O build_verify.py

Python's standard library suffices. These commands regenerate the packets
and expanded polynomial lists, verify all retained source hashes and exact
coefficient bytes, and check all elimination identities, dimensions,
degrees, and nonzero leading coefficients. The proof and independent
mathematical review are separate from these finite checks.

The source pin is `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`. New results
are compared to that snapshot. No global minimality, low-variable record
over all degrees, new machine proof, new proof-assistant certificate,
proof of consistency, or improvement on every complexity measure is claimed.
Expanded expressions become larger after the affine substitutions.
The direct quartic has 393 symbolic monomials (parent: 388); the projection
parent has 614. The sextic and octic have 614 and 1238, respectively.

`upstream/` holds unchanged proof/data sources and licenses. `SOURCE_PINS.json`
records their original repository paths, Git blob identities, and SHA256
hashes. These documents can retain historical relative links; the current
packet's literal coefficient binding is authoritative.
