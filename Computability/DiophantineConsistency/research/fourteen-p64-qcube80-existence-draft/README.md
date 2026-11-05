# Positive-zero equivalence for the 80-operation graph

`positive_zero_iff` proves that the generated 80- and 81-operation graphs
have positive 14-tuple zeros for exactly the same natural port tuples in
each indicated model of IΣ₁. In the 81→80 direction it sets the 80 coordinate
`r0` to `rho+s`. For the reverse direction the separately checked
`P64QCube80Gap.graph_remainder` proves `s<r0` for any actual positive 80 zero;
the proof extracts a positive `rho` with `r0=rho+s` and applies the checked
ring-level graph-output binding.

This theorem concerns the generated Lean graph expressions. It is not by
itself the iPRA derivability endpoint, an external graph/payload/PDF binding,
or an audit of the captured providers' full ancestry. The intermediate
`positive_zero_iff_conditional` exposes the remainder hypothesis; the final
`positive_zero_iff` discharges it using the checked zero-specific theorem.

On 2026-11-04, Lean exited 0 and all eight axiom reports were exactly
`[propext, Classical.choice, Quot.sound]`, without warnings or `sorryAx`.
A subsequent [bounded guarded replay](lean-replay.json) exited 0 with the same
reports and byte-identical output. It recorded the full [Lean output](lean-replay.log),
command and before/after hashes of the source, executable and three direct
import objects. The [runner](check_lean.py) refuses to overwrite its outputs;
a repeat requires fresh paths in a copy of the runner.

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube80Existence.lean` | `f417cb3f09e4e9235e5e9cd85f083d14f8fd0e89b1b554dfbaaedc672cfdda10` |
| `/tmp/P64QCube80Existence.olean` | `7e8f2976371bc6a7fc206b1ef7882126bbdccad642a99b2738dd9782c1c938fd` |
| `check_lean.py` | `d165e18e1611a65f6b5bde72a79423fbd3dd648595e1d9cbbdc814160c7971c9` |
| `lean-replay.json` | `7715996d4699bd24f1ea8e22c6c5130ae846c90348c808d122534c32ca879c4e` |
| `lean-replay.log` | `758d850042e0a3ad9d30ba32daf6b8129bb4d833751201ee8ab690277969e57b` |

The successful checks use temporary prebuilt providers; package-transitive,
dynamic-loading, full project-source and search-path ancestry remain inherited
rather than authenticated by these direct guards.
