# Actual 72 zeros with common X,Y,c have common k

`FreeMainActualFirstOrdinateUnique.same_k` proves in every IΣ₁ model that two
actual positive 72-graph zeros at the same arbitrary natural ports have equal
`k=v₁₀+v₁₁` if their X,Y,c values agree. It extracts each zero's first
Pell index, then applies the checked generic first-ordinate uniqueness theorem
to the common scale interval. No fixed compact masks or `3|q` assumption are
needed. This result does not assert either zero exists, a 76Y consequence, or
the existential reverse implication.

Attempt01 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and expected `[propext, Classical.choice, Quot.sound]` axioms. The
source's unchecked-draft header predates the check. Direct guarded providers
are first-ordinate uniqueness, actual first-index extraction, and conditional
rank definitions. Transitive/dynamic ancestry and sampled monitoring are
inherited; this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainActualFirstOrdinateUnique.lean` | `9b2e4519f7417e01905b286be8853781d9060d580e010ffc35653c206ab93c3d` |
| `check01.py` | `ea85ebd06152d1404d6550a5a7b0736237358c7e9a5577ba66c2e840969abd3a` |
| `observations/attempt01/compile.log` | `d93b5e5f876951f2e1ed006ef52d363308dbb1ca80df0a966cdbef670b9b7444` |
| `observations/attempt01/result.json` | `0ea8d22fdecd9cbe19f7b5ee1fad89292efa88273f4be860b97bb0541bb6220e` |
| `/tmp/p64-qcube72-actual-first-ordinate-unique-priority-check01/FreeMainActualFirstOrdinateUnique.olean` | `c37a0740ec76365e3e1aa2d848dad873ff3a3a434f7a25f1fa0a974ecc4f88bc` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority.
