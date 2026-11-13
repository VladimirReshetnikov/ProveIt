# Independent review: root74 ordered lexical provider plan

The [candidate provider plan](../../research/ordinary14-root74-ordered-provider-plan/README.md) accurately describes its bounded, point-in-time evidence. The candidate sequence is topologically ordered for the checked source headers and the selected frontier; it is not a verified Lean build sequence. Its `check.py` reproduced `plan.json` in this environment.

The independent receipt pins the plan, reads and hashes each of the 162 actual stage sources, and extracts their initial contiguous single-line import commands directly. All source headers have that simple form, and each matches its plan row as a multiset. Every recorded import is either an earlier candidate stage or a selected frontier object. Traversing those same lexical imports backward from `Root74Endpoint` reaches all 162 stages. The receipt also hashes all 35 current observed `.olean` files and verifies their recorded resolved paths; the project frontier resolves to 24 files under the selected P72 root and seven under the linked base, as documented. These are comparisons to the observation, not producer authentication.

The review does **not** run Lean, resolve the actual `LEAN_PATH`, establish that object bytes match their producers, examine transitive object imports, validate companions or toolchain compatibility, check output collisions, reserve resources, or demonstrate the endpoint or its axioms. The parser intentionally accepts only the observed simple header form and is not a general Lean parser. The exact receipt depends on temporary retained roots and may cease to reproduce if their contents change. The plan's remaining prerequisites and refusal to claim a build-ready provider closure are appropriate.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-root74-ordered-provider-plan-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-root74-ordered-provider-plan-independent/result.json
```
