# 77-operation unit-product graph: iPRA endpoint client

`P64QCube77Endpoint.lean` composes the checked all-model 77↔78 positive-zero
equivalence with the existing 78 positive bridge. The generic adapters prove
native, standard and equality-only iPRA derivability statements for the 77
graph's positive-shifted no-zero formula and the selected mapped Foundation
refutation negation. These are proof-existence statements in the specified
encoded theories, not assertions that ZFC is consistent.

The candidate has 14 positive variables and 77 live operations; its exact
degree is externally computed as 90. The endpoint concerns the Lean graph at
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
runner guarded source, Lean binary, 77 graph, 77↔78 existence object and 78
endpoint object before and after compilation, refused an existing output
directory and an occupied Lean slot, and applied a 300-second bound.

To repeat with captured providers available, choose a fresh output directory
in a copy of the runner and run from the repository root:

```sh
python3 -I -S -B -u Computability/DiophantineConsistency/research/p64-qcube77-ipra-draft/run.py
```

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube77Endpoint.lean` | `921fbdf5f333959f6a7abf43cf7853df0512683c26de342f025bc4c700ea9154` |
| `P64QCube77Endpoint.olean` | `d283e42f2b3225ca20143cd3e4db79290de8a4796bd939e684fa2dce37768c7f` |
| `P64QCube77Existence.olean` | `0cd0fa8b52a8cad49bad9db49507f16acb0171ee56dad0e21783515facf15a72` |
| `P64QCube78Endpoint.olean` | `a2e7bb5d0303e42afeb0f59331ca740f8397a3c681aa815d7559f15e7fb82eea` |
| `run.py` | `0eac274ea4b5d77ec4f0bc0f025a4fffb31b1874635a37d44e83c66d79f57639` |

This is a single guarded client check against temporary prebuilt providers,
not a paired end-to-end replay. Full transitive project, package,
dynamic-library and search-path ancestry was not independently rebuilt or
audited in this check.
