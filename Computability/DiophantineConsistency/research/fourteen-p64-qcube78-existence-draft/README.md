# Positive-zero equivalence for the 78-operation graph

`same_zero_iff` proves that, for each natural port tuple and each **positive**
14-tuple in an indicated IΣ₁ model, the generated 78 and 79 graphs vanish
at that same tuple together. `positive_zero_iff` lifts this to equivalence of
positive-zero existence. This is stronger than merely constructing a witness
with different coordinates.

The outputs differ by twice the 79 first residual. For a 79 zero the checked
residual split forces that first residual to zero. For a 78 zero the separately
checked `P64QCube78GraphSplit.first_eq_one` forces its shifted first residual
to one, so the 79 first residual is zero by the checked ring binding.

This concerns the generated Lean graph expressions. It does not by itself
provide an iPRA endpoint, external graph/payload/PDF binding, or full provider
ancestry audit.

On 2026-11-04 Lean exited 0 and all three axiom reports were exactly
`[propext, Classical.choice, Quot.sound]`, without warnings or `sorryAx`.
A subsequent [bounded guarded replay](lean-replay.json) exited 0 with the same
reports and byte-identical output. It recorded the full [Lean output](lean-replay.log),
command and before/after hashes of the source, executable and three direct
import objects. The [runner](check_lean.py) refuses to overwrite outputs;
a repeat requires fresh paths in a copy of the runner.

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube78Existence.lean` | `a5e64c5dfeed7752d80546d6ff3b61cff314767d64682c173f935734e22b3af7` |
| `/tmp/P64QCube78Existence.olean` | `8371368a8feb9de7e729501224455ab26848c1509b88c93aadd757b38e0bd669` |
| `check_lean.py` | `3fb10bced4a9ffce1d5cf4bdccbcea90a00659552535ac6e94ffa493bee4bb9f` |
| `lean-replay.json` | `21a13c2db0894d4768df4c224fd42d9c11510ac8cce99362e1337e57ed053d39` |
| `lean-replay.log` | `d3bd76eb4475485f3066e170775dd657b80f9b2426e0c91cec46f9d55d74f616` |

The checks use temporary prebuilt providers; package-transitive,
dynamic-loading, full project-source and search-path ancestry remain inherited
rather than authenticated by these direct guards.
