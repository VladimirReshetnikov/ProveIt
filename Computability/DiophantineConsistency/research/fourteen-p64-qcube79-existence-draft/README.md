# Positive-zero equivalence for the 79-operation graph

`positive_zero_iff` proves that the generated 79- and 80-operation graphs
have positive 14-tuple zeros for exactly the same natural port tuples in
each indicated model of IΣ₁. In the 80→79 direction it replaces `r0` by
`t=ell+r0`. For the reverse direction the separately checked
`P64QCube79Gap.graph_root_gt` proves `ell<t` for any actual positive 79 zero;
the proof extracts a positive `r0` with `t=ell+r0` and applies the checked
ring-level graph-output binding.

This theorem concerns the generated Lean graph expressions. It is not by
itself an iPRA derivability endpoint, an external graph/payload/PDF binding,
or an audit of the captured providers' full ancestry. The intermediate
`positive_zero_iff_conditional` exposes the root-gap hypothesis; the final
`positive_zero_iff` discharges it using the checked zero-specific theorem.

On 2026-11-04, Lean exited 0 and all five axiom reports were exactly
`[propext, Classical.choice, Quot.sound]`, without warnings or `sorryAx`.
A subsequent [bounded guarded replay](lean-replay.json) exited 0 with the same
reports and byte-identical output. It recorded the full [Lean output](lean-replay.log),
command and before/after hashes of the source, executable and two direct
import objects. The [runner](check_lean.py) refuses to overwrite its outputs;
a repeat requires fresh paths in a copy of the runner.

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube79Existence.lean` | `95a8f112ccd9f3f1f735b131b48f0a6f7366119b313c6e65b057671b81c9e593` |
| `/tmp/P64QCube79Existence.olean` | `bd6c23e7857eb62216def8e113082c1ef8e7b6ec695f044e5cd2b2c17a29872f` |
| `check_lean.py` | `702f5ab8384fd161d4044c07c7735e18f940a20dbf7d838f3c642bf3191b4d10` |
| `lean-replay.json` | `5ec7589e3605abbb0a9dd2b454a11dbbc850a6aa15f4e2c072f1ced3fad0b257` |
| `lean-replay.log` | `0acbfee66954063184c662c861a075bb47a4e71fbd7e878e7a4de5758eefdbef` |

The successful checks use temporary prebuilt providers; package-transitive,
dynamic-loading, full project-source and search-path ancestry remain inherited
rather than authenticated by these direct guards.
