# Projected low-digit quartics with candidate-output factorial radii

| Method | Natural variables | Quadratic rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| both radii, support64 | **399** | 317 | 4 | 8,286 | 83,843,274 |
| H-only, support64 | 403 | 320 | 4 | **8,229** | 83,843,593 |
| both radii, support16 | 402 | 320 | 4 | 6,882 | 211,184,624 |
| both radii, support4 | 453 | 371 | 4 | 5,059 | 63,906,450 |
| both raw export | 667 | 585 | 4 | 3,632 | 63,905,862 |
| H-only raw export | 678 | 595 | 4 | 3,695 | 63,905,958 |

This new sibling composes the independently accepted 407 source/radix
engine with the exact radius `rho=f*n²`. For both factorials the radix
is `B*(V_H+V_t+1)`, leaving **21 powers / 16 exponent atoms / 15 seed
index tests / 1 derived pair**. The H-only tradeoff has 22/17/15/2.
`PROOF.md` includes both unbounded soundness/completeness arguments,
the initially zero t-factorial candidate, the stronger low-digit bound
for the smaller H-numerator and the full witness order.

Each directory contains every quadratic residual and every collected
quartic coefficient. The old 407 archive and all frozen local parents
remain unchanged. Inspected source code is loaded from its authenticated
incoming ZIP into a temporary directory; no whole component is copied.
Only the ordinary arithmetic compiler/checker paths run, with no Lean,
historical native/H10 emitter, machine search or network access.

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_projected_factorial_radius.py --check
python3 -O -B Computability/DiophantineConsistency/tools/build_projected_factorial_radius.py --check
python3 -B Computability/DiophantineConsistency/candidates/projected-factorial-radius/check.py
python3 -O -B Computability/DiophantineConsistency/candidates/projected-factorial-radius/check.py
```

The independent checker imports no producer or optimizer. It checks all
actual local factorial, shared-power/index, digit/range, radix, aggregate
and canonical-index interfaces; all raw affine/square exports; every
natural restoration; and every complete SOS coefficient. Its controls
explicitly include zero second-factorial candidates and the new strict
squared-numerator bound. The prior ordinary C222/refutation calibration
is unchanged; new Lean/internal-ZFC formalization and global optimality
are not claimed.
