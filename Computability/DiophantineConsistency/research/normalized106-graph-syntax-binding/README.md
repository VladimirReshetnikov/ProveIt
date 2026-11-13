# 67/106 JSON graph to historical Lean syntax

This standalone, read-only checker compares the 67-row graph in
`../fourteen-normalized-product106/polynomial.json` with the exact
stage-078 `ModelCarrierSyntax.lean` source used by the independently
replayed stage-079 model/iPRA provider. It parses the `expressionAt106`
Lean expression, checks the 14 witness indices and four port slots,
constructs shared exact symbolic expression trees, and compares 19
intermediate cuts plus the complete output modulo only associativity and
commutativity of addition and multiplication. Powers 2 and 3 are expanded
as repeated multiplication. No distribution or sampled evaluation is
used for the equality. A changed-witness negative control is rejected.

The checker verifies all 67 graph rows are live, all 14 witnesses and four
fixed ports are live, and the counts are 38 multiplications, 16 additions
and 13 subtractions. It checks the compressed and decompressed port bytes
against the JSON metadata. The graph and source are SHA-256 pinned. This is
an external source/graph correspondence check, not a new Lean proof, a PDF
render check, or a standalone proof that those numerical bytes equal
`CurrentWindowCarry2011.ports`. The coefficient package's separate
`fourteen-normalized-product106` audit provides its current2011 binding
and exact degree-106 certificate; this checker does not redo that degree
proof.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/normalized106-graph-syntax-binding/check.py
```

The saved run exited 0 directly with stdout redirected to `result.json`;
no Lean process was invoked. The stage-078 captured syntax source hash is
`8d40486fd9adf151e905977c01cbc1a2aa7142fbd02c5e4293906c6865e5a43a`.
Its captured output object SHA-256 is
`9eaaefb9b4121df6d9c8f6f1c5feef1cc837fc38f51a831a005db072bdaaf900`;
the stage-079 direct-provider receipt names that same object. Historical
provider, package and dynamic ancestry remain inherited.

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `3d36c67101606c5d0d8b1e47c0c00fa06e5eceb0370a1baa4b086b5017128c65` |
| `result.json` | `2ea08d98108465c1d1e48e1296e32a2f15aceebadae682231c00b87e8c00d552` |
| `outer-terminal.json` | `ede299f578e43719e4e673307fd95b7626a05298b8e96e717f25746ec03234f3` |
