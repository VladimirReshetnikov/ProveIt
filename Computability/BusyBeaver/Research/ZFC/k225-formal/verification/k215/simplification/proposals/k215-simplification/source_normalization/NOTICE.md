# Source provenance and attribution

Baseline repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `b6c7087477e51c017003bd729e712c8969733223`.

The preserved files under `upstream/` come from these exact paths:

| Packaged file | Repository path |
|---|---|
| `sites215.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json` |
| `dagperm_nodes.json` | `Computability/BusyBeaver/Research/ZFC/k225-formal/lean215/dagperm_nodes.json` |
| `gen_cert.py` | `Computability/BusyBeaver/Research/ZFC/k225-formal/gen_cert.py` |
| `KSource215Data.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean` |

The kernel receipt records each input's SHA-256 digest and the eight imported
formal dependencies. The DAG's Git blob is
`ad1775396daf0d351492a8d95c3af1d95bc33ea1`; the original generator's Git blob is
`4dd02091c09af52f067c83c9b183cef1b2c48bf4`.

The underlying path semantics, source programs, numerical calculus,
enumerator, compiler, and original correctness proofs remain contributions
of their original authors. This packet adds a normalized certificate relation,
its soundness proof and concrete instance, shared reflected trees, and
partitioned finite checks. The new proof code reuses the inherited semantics;
it does not claim authorship of the underlying machine or calibration.

The original K215 notice and inherited license texts are retained in
`upstream/licenses/`. New material may be incorporated under ProveIt's
existing MIT No Attribution License; inherited material retains its terms.
