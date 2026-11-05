# 79-operation first-root graph: iPRA endpoint client

`P64QCube79Endpoint.lean` composes the checked all-model 79↔80 positive-zero
equivalence with the existing 80 positive bridge. The generic adapters then
prove native, standard and equality-only iPRA derivability statements for the
79 graph's positive-shifted no-zero formula and the selected mapped Foundation
refutation negation. These are proof-existence statements in the specified
encoded theories, not assertions that ZFC is consistent.

The candidate has 14 positive variables and 79 live operations; its exact
degree is externally computed as 68. The endpoint concerns the Lean graph at
symbolic compact44 ports. Finite graph and degree checks, coefficient payload,
external displays, and formal filesystem/gzip/JSON/PDF identification are
separate from this client. It does not establish global minimality.

## Observed guarded client check

On 2026-11-04, the runner exited 0. Lean 4.32.0 reported
`[propext, Classical.choice, Quot.sound]` for `positiveBridge` and all three
endpoints, with no warnings or `sorryAx`. The exact command, elapsed time,
search path and direct input guards are in
[`observations/attempt01/result.json`](observations/attempt01/result.json);
the complete output is [`compile.log`](observations/attempt01/compile.log).
The runner guarded source, Lean binary, 79 graph, 79↔80 existence object and
80 endpoint object before and after compilation, refused an existing output
directory and an occupied Lean slot, and applied a 300-second bound.

To repeat with the captured providers available, choose a fresh output
directory in a copy of the runner and run from the repository root:

```sh
python3 -I -S -B -u Computability/DiophantineConsistency/research/p64-qcube79-ipra-draft/run.py
```

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube79Endpoint.lean` | `982c587f1eb8e801de36efa1ef33b1a1b4dec235c203dd028571574951b24fb0` |
| `P64QCube79Endpoint.olean` | `0fd32770fa41c913b9f2a1754b0d1c5a98adedcd2c9b1bda270e8718eb74a119` |
| `P64QCube79Existence.olean` | `bd6c23e7857eb62216def8e113082c1ef8e7b6ec695f044e5cd2b2c17a29872f` |
| `P64QCube80Endpoint.olean` | `2486d2b671dce6751c656830dde439bda0c0de3dcbca2a82842c8dd1331f3c6c` |
| `run.py` | `45e09cdfa9373a8b4be4b5ca5e7d1825c52d061014ef71b068fcebdd3ed05050` |

This is a single guarded client check against temporary prebuilt providers,
not a paired end-to-end replay. Full transitive project, package,
dynamic-library and search-path ancestry was not independently rebuilt or
audited in this check.
