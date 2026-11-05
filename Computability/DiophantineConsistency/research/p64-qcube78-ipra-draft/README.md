# 78-operation shifted first residual: iPRA endpoint client

`P64QCube78Endpoint.lean` composes the checked all-model 78↔79 positive-zero
equivalence with the existing 79 positive bridge. The generic adapters prove
native, standard and equality-only iPRA derivability statements for the 78
graph's positive-shifted no-zero formula and the selected mapped Foundation
refutation negation. These are proof-existence statements in the specified
encoded theories, not assertions that ZFC is consistent.

The candidate has 14 positive variables and 78 live operations; its exact
degree is externally computed as 68. The endpoint concerns the Lean graph at
symbolic compact44 ports. Finite graph and degree checks, coefficient payload,
external displays, and formal filesystem/gzip/JSON/PDF identification are
separate from this client. It does not establish global minimality.

## Observed guarded client check

On 2026-11-04, the runner exited 0. Lean 4.32.0 reported
`[propext, Classical.choice, Quot.sound]` for `positiveBridge` and all three
endpoints, with no warnings or `sorryAx`. The command, elapsed time, search
path and direct input guards are in
[`observations/attempt01/result.json`](observations/attempt01/result.json);
the full output is [`compile.log`](observations/attempt01/compile.log). The
runner guarded source, Lean binary, 78 graph, 78↔79 existence object and 79
endpoint object before and after compilation, refused an existing output
directory and an occupied Lean slot, and applied a 300-second bound.

To repeat with captured providers available, choose a fresh output directory
in a copy of the runner and run from the repository root:

```sh
python3 -I -S -B -u Computability/DiophantineConsistency/research/p64-qcube78-ipra-draft/run.py
```

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube78Endpoint.lean` | `f472f972edf2f8ec8d6e2cc343c36735475229ae22e7b0c37a34328022bd6a64` |
| `P64QCube78Endpoint.olean` | `a2e7bb5d0303e42afeb0f59331ca740f8397a3c681aa815d7559f15e7fb82eea` |
| `P64QCube78Existence.olean` | `8371368a8feb9de7e729501224455ab26848c1509b88c93aadd757b38e0bd669` |
| `P64QCube79Endpoint.olean` | `0fd32770fa41c913b9f2a1754b0d1c5a98adedcd2c9b1bda270e8718eb74a119` |
| `run.py` | `ce6196c90e21f1b104c0e60f7bd516f673cd8a9740b96932545269d88398a0b6` |

This is a single guarded client check against temporary prebuilt providers,
not a paired end-to-end replay. Full transitive project, package,
dynamic-library and search-path ancestry was not independently rebuilt or
audited in this check.
