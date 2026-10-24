# Pointwise main-root/modulus guard reduction

This separate candidate retains the complete original 667-coordinate,
585-row body and exactly 79 of the frozen 967 equation's 100 guards.
The 15 main-root guards and six noninitial modulus guards are consequences
of the unchanged rows. The ordinary proof and complete ordered row/call
ledger are frozen in research/main-root-and-modulus-signs.

Every equation is the sum of the squares of the complete quadratic
residual list in its equation.json, over unrestricted integer variables.
Each expanded_polynomial.json is the full collected integer polynomial.

| Variant | Integer variables | Quadratic rows | Quartic terms | Coefficient height |
|---|---:|---:|---:|---:|
| unprojected | 904 | 664 | 4752 | 63905862 |
| support4 | 645 | 405 | 5580 | 63905891 |
| support8 | 619 | 379 | 8597 | 2445790974704 |
| support16 | 617 | 377 | 8692 | 2445790974704 |
| support32 | 616 | 376 | 10028 | 2445790974704 |

These are complete materialized equations of exact degree 4, with whole
coefficient and inverse certificates. They are separate from the older
679/689 families, which remain unchanged. The 616-variable endpoint
deletes 63 witnesses and 21 rows from the matched 679-variable profile;
its source-variable values are not changed by the guard reduction.

The signed projections must first be reversed over the integers,
including all guard coordinates. All 592 raw affine wires are then
restored over the integers. Only after the ordered sign argument gives
the 21 omitted values nonnegative do 63 fresh Legendre witnesses produce
a literal zero of the frozen 967 equation. Its previous ordinary
calibration is invoked at that point. This is an existence equivalence;
it asserts neither pointwise naturalness of every coordinate nor a new
Lean/internal-ZFC theorem.

PROOF.md explains the maps. domain_certificate.json binds the exact 79
guard roles. BRIDGE967.json gives all copied and fresh literal witness
positions. The optimizer is authenticated and used only by build.py;
check.py never imports it. The independent checker verifies every full
residual, collected coefficient and signed inverse, replays the entire
ordered sign ledger, and reruns both frozen source/domain checkers.

```sh
python -B Computability/DiophantineConsistency/candidates/projected-radius-main-root-signs/build.py --check
python -B Computability/DiophantineConsistency/candidates/projected-radius-main-root-signs/check.py
python -B -O Computability/DiophantineConsistency/candidates/projected-radius-main-root-signs/build.py --check
python -B -O Computability/DiophantineConsistency/candidates/projected-radius-main-root-signs/check.py
```

VERIFY.json and VERIFY_OPTIMIZED.json record the independent runs.
BUILD_VERIFY.json and BUILD_VERIFY_OPTIMIZED.json record deterministic
whole-artifact regeneration. MANIFEST.json seals the complete packet.
