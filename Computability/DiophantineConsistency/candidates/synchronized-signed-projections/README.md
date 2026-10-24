# Signed projections of synchronized integer quartics

The fewest-variable point here is an explicit equation in **1,190 unrestricted
integers**, of exact degree **four**, with **600** quadratic residuals,
**26,411** collected monomials and coefficient height **83,900,628**.
Its integer zero set is in polynomial bijection with that of the frozen
1,224-integer synchronized companion. In particular it has a zero exactly
when the reviewed 522-natural parent does.

This is ordinary mathematical research and exact Python algebra. Lean
formalization remains paused. It does not prove consistency, no-zero
existence, or an internal object-ZFC equivalence.

Each directory gives the **complete** equation, expanded polynomial and
ordered elimination/restoration certificate. All coordinates are integers.
The equation means precisely the sum of the squares of its listed residuals.
No new fixed tuple or machine encoding is introduced.

| Directory | Parent integers | Integers | Rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|---:|
| from1224-support4 | 1,224 | **1,190** | **600** | 4 | 26,411 | 83,900,628 |
| from1231-support4 | 1,231 | 1,196 | 606 | 4 | 15,737 | 211,184,624 |
| from1231-support8 | 1,231 | 1,195 | 605 | 4 | 15,901 | 211,184,624 |
| from1298-support4 | 1,298 | 1,265 | 675 | 4 | **11,399** | **63,909,160** |
| from1298-support8 | 1,298 | 1,215 | 625 | 4 | 14,034 | 3,828,333,528 |
| from1298-support8-quadratic | 1,298 | 1,217 | 627 | 4 | 13,803 | 3,815,149,650 |
| from1298-support16-quadratic | 1,298 | 1,196 | 606 | 4 | 22,277 | 83,898,602 |

These seven points retain distinct tradeoffs from 18 measured configurations:
support caps 4, 8 and 16, with affine-first or quadratic-first priority, on
three frozen parents. They are not a global optimum claim. The unchanged
parents also retain useful term/height choices. For example the 1,224-parent
has fewer terms (23,590) than the 1,190-point. `PROBES.json` records all 18
configurations, including identical outcomes and a dominated point.

Signed restoration coefficients are essential: respectively 12, 12, 26,
12, 46, 21 and 23 eliminated coordinates use a polynomial with a negative
coefficient. Their validity follows from the integer domain and exact
monic equations, not from nonnegative circuit metadata.

`PROOF.md` gives the unbounded zero-set argument. `PROVENANCE.json` pins
the complete arrival archives, authentic signed optimizer/replayer and
the complete copied parent packets. Each parent includes its unchanged
natural prefix and actual-row nonnegativity certificate. The source
optimizer is from the batched arrival, SHA256
`ff0d3f638d91a905f676f6fe3e40e134979a14880ed34cadf0741604386e8e55`;
the natural systems are unchanged members of the synchronized arrival,
SHA256 `ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf`.

Regenerate or check from the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_synchronized_signed_projections.py --check
python -B Computability/DiophantineConsistency/candidates/synchronized-signed-projections/check.py
python -B -O Computability/DiophantineConsistency/tools/build_synchronized_signed_projections.py --check
python -B -O Computability/DiophantineConsistency/candidates/synchronized-signed-projections/check.py
```

The independent checker imports no optimizer, generator or arithmetic
compiler. It replays every polynomial substitution, including every
guard, validates reverse restoration on signed off-source controls,
checks each restored actual-row sign inference, expands every complete
quartic and rejects corrupted restorations and rehashed missing rows.
All checks use explicit conditions, not Python assertions. The bounded
controls supplement the unbounded algebraic argument; they do not replace it.

Ordinary refutation calibration is inherited unchanged from the accepted
synchronized parent review. No new semantic claim is inferred from the
finite coefficient checks, and the encoded internal-ZFC proof obligation
remains separate.
