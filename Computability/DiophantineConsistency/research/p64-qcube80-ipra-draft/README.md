# 80-operation q³ quotient: iPRA endpoint client

`P64QCube80Endpoint.lean` composes the checked all-model 80↔81 positive-zero
equivalence with the existing 81 positive bridge. It then applies the
repository's generic adapters to prove native, standard, and equality-only
iPRA derivability statements for the 80 graph's positive-shifted no-zero
formula and the selected mapped Foundation refutation negation. These are
proof-existence statements in the specified encoded theories, not assertions
that ZFC is consistent.

The candidate has 14 positive variables and 80 live operations; its exact
degree is externally computed as 68. The endpoint concerns the Lean graph
with symbolic compact44 ports. The finite graph and degree checks, coefficient
payload, external displays, and formal filesystem/gzip/PDF identification
are separate from this client. It does not prove global minimality.

## Observed guarded client check

On 2026-11-04, the runner exited 0. Lean 4.32.0 reported
`[propext, Classical.choice, Quot.sound]` for `positiveBridge` and all three
endpoints, with no warnings or `sorryAx`. The exact command, elapsed time,
search path and direct input guards are in
[`observations/attempt01/result.json`](observations/attempt01/result.json);
the full output is [`compile.log`](observations/attempt01/compile.log). The
runner checked source, Lean binary, 80 graph, 80↔81 existence object, and
81 endpoint object hashes before and after compilation, refused an existing
output directory and an occupied Lean slot, and applied a 300-second bound.

To repeat while the captured providers remain available, choose a fresh
output directory in a copy of the runner and run from the repository root:

```sh
python3 -I -S -B -u Computability/DiophantineConsistency/research/p64-qcube80-ipra-draft/run.py
```

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube80Endpoint.lean` | `2fdbc40162acab85cef045cbe15c91ef188c6b58793a51945831fe2ab00c8338` |
| `P64QCube80Endpoint.olean` | `2486d2b671dce6751c656830dde439bda0c0de3dcbca2a82842c8dd1331f3c6c` |
| `P64QCube80Existence.olean` | `7e8f2976371bc6a7fc206b1ef7882126bbdccad642a99b2738dd9782c1c938fd` |
| `P64QCubeEndpoint.olean` | `893103d30af30a2da273e6f9509a18933c5adce8c9de391cc414c6e98aac6763` |
| `run.py` | `d95cf45f52e8ea14345da0450eb62be5203315581e0db15462bc13f3affe8b63` |

This is a single guarded client check against temporary prebuilt providers,
not a paired end-to-end replay. Full transitive project, package,
dynamic-library and search-path ancestry was not independently rebuilt or
audited in this check.
