# Retained-wire, low-height integer quartics

Five complete equations over unrestricted integers, all of exact degree
four and all ordinarily equivalent in zero existence to the unchanged
667-natural-coordinate factorial-radius source:

| Directory | Integer variables | Rows | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|
| `integer1742` | 1,742 | 1,338 | 6,200 | 427 |
| `integer1095` | 1,095 | 691 | 5,044 | 4,750 |
| `integer950` | 950 | 546 | 6,808 | 737,653 |
| `integer886` | 886 | 482 | 10,158 | 737,653 |
| `integer872` | 872 | 468 | 10,122 | 938,261 |

Retaining every raw arithmetic wire gives 1,259 natural coordinates,
1,177 rows and height 427. A fresh actual-row sign certificate derives
1,098 signs from 161 guarded seeds. Subsequent signed monic projections
substitute every guard and restore the full integer parent before using
that sign certificate. There are no unconstrained-coordinate deletions.
See `PROOF.md` for both directions and the scope of inherited semantics.

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_retained_radius_integers.py --check
python3 -O -B Computability/DiophantineConsistency/tools/build_retained_radius_integers.py --check
python3 -B Computability/DiophantineConsistency/candidates/retained-radius-integers/check.py
python3 -O -B Computability/DiophantineConsistency/candidates/retained-radius-integers/check.py
```

The independent checker imports no producer or optimizer. It checks all
coefficients, all actual rows and all inverse certificates, plus signed
assignment and corruption controls. The immutable 407 ZIP supplies the
pinned reviewed arithmetic checkers. Original natural and integer
parents remain unchanged. No Lean or internal-ZFC formalization is
claimed here.
