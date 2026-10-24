# New integer quartics from the 667-natural projected-radius source

| Unrestricted integers | Rows | Degree | Terms | Height |
|---:|---:|---:|---:|---:|
| **862** | 458 | 4 | 11,245 | 2,445,790,974,704 |
| 863 | 459 | 4 | **9,909** | 2,445,790,974,704 |
| 865 | 461 | 4 | 9,814 | 2,445,790,974,704 |
| **891** | 487 | 4 | **6,797** | **63,905,891** |

Every coefficient is literal in the four complete equations/expanded
polynomials. A fresh actual-row certificate proves 506 source coordinates
nonnegative from 161 guarded seeds, before any semantic macro is used.
The common guarded parent and full domain-conversion/sign proof are stored
once. Each signed monic certificate substitutes into every row, including
all guards, and removes no unconstrained coordinate. Reverse integer
restoration precedes the original sign chain. `PROOF.md` gives both
unbounded directions. No minimum-seed or global optimality claim is made.

The natural and incoming parents remain frozen. To reproduce from the
repository root using only the standard library:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_projected_radius_integers.py --check
python3 -O -B Computability/DiophantineConsistency/tools/build_projected_radius_integers.py --check
python3 -B Computability/DiophantineConsistency/candidates/projected-radius-integers/check.py
python3 -O -B Computability/DiophantineConsistency/candidates/projected-radius-integers/check.py
```

`PARENT_PINS.json`, `guarded.json`, `domain_conversion.json` and every
projection certificate are required, alongside the frozen natural parent
and the pinned 407 incoming ZIP. The independent checker imports no
producer or optimizer. It verifies the actual sign rows, all guards,
every substitution and every quartic coefficient, plus signed restoration
diagnostics and deliberately corrupted certificates.

The ordinary C222/refutation argument is inherited from the natural
source. There is no new Lean/internal-ZFC theorem, consistency proof,
zero-existence decision or native-port calibration claim.
