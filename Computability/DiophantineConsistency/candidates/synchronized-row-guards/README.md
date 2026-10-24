# Synchronized integer quartics with certified row signs

The main equation has **1,224 unrestricted integer variables** and degree
four. Only 234 original coordinates receive three-square guards; actual
polynomial rows certify every remaining coordinate's nonnegativity.
[PROOF.md](PROOF.md) establishes both directions without using the
parent's arithmetic semantics to justify a sign.

| Directory | Integers | Degree | Terms | Height |
|---|---:|---:|---:|---:|
| `integer1224/` | **1,224** | **4** | 23,590 | 83,900,628 |
| `integer1231/` | 1,231 | 4 | 14,148 | 211,184,624 |
| `integer1298/` | 1,298 | 4 | 10,628 | 63,909,160 |
| `integer1597/` | 1,597 | 4 | **8,232** | **63,908,265** |

Each directory contains the full quadratic system, expanded polynomial,
unchanged authenticated natural parent and ordered sign certificate.
No `kind` annotation is used as a sign premise. The natural parents
retain their independently reviewed ordinary C222/refutation meaning.

Reproduce from the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_synchronized_row_guards.py --check
python3 -B Computability/DiophantineConsistency/candidates/synchronized-row-guards/check.py
python3 -O -B Computability/DiophantineConsistency/tools/build_synchronized_row_guards.py --check
python3 -O -B Computability/DiophantineConsistency/candidates/synchronized-row-guards/check.py
```

All four commands pass. The incoming archive and earlier candidates are
unchanged. This is ordinary arithmetic research; Lean remains paused,
and no new internal object-ZFC derivation is claimed.
