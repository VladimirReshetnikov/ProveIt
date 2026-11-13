# Actual 72 zeros with 3-divisible q have Y²∤h

`FreeMainActualDivisibleQObstruction.actual_zero` proves in any IΣ₁ model:
for arbitrary natural ports, an actual positive zero of the 72 graph with
`3|q` satisfies `¬(Y²|v₁₃)`, where `q=p₀v₀+1` and `Y=q³v₇`.
`fixed_zero` states the same consequence at the fixed compact44 beta and
masks, with arbitrary natural K. The proof extracts the main Pell root and
free carrier from that same zero and applies the checked generic 3-divisible-q
obstruction.

The hypothesis `3|q` is explicit. Neither theorem proves an actual zero with
that property exists, rules out other zeros, or establishes a failure of
existential reverse implication. No old-carrier witness exclusion is claimed
in this packet.

Attempt01 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and both expected `[propext, Classical.choice, Quot.sound]` axiom
reports. The source's unchecked-draft header predates this check. Its direct
guarded providers are the fixed-compact carrier package, generic 3-divisible-q
obstruction and graph main-root object. Transitive/dynamic ancestry and sampled
monitoring are inherited; this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainActualDivisibleQObstruction.lean` | `6e186ef99bc68076c9e9bc1e3c57c9999bf15f754dbf8731e2e60a4c7e8297ce` |
| `check01.py` | `33add9b4ccecf3a2b97daa4c5bfbad5c28b3e75d04fe5fc6b2fa5ef307566a0d` |
| `observations/attempt01/compile.log` | `c67b56a266f91712d4d50f1ba6d3c7a36d3f452ef39d695d6036447f28259837` |
| `observations/attempt01/result.json` | `828af6073480d5bf4f2b0a4611629a0c2cd9138c36a5b5a4dcd243e80717658c` |
| `/tmp/p64-qcube72-actual-divisible-q-obstruction-priority-check01/FreeMainActualDivisibleQObstruction.olean` | `bf804a8acde053c241f8a45faa73386ce7148d48c69fe78c7fb6f75c9a421bfe` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority.
