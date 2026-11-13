# Observed generated-graph compilation

On 2026-11-04 the canonical-import generated `P64QCube81.lean` compiled
with Lean 4.32.0, exit 0, empty output and no warnings. It is a generated
graph definition, and this check alone asserts no residual equivalence or
iPRA endpoint. From the repository root:

```sh
LEAN_PATH=/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M4000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/p64-qcube81-candidate \
  Computability/DiophantineConsistency/research/p64-qcube81-candidate/P64QCube81.lean \
  -o /tmp/P64QCube81.olean
```

```text
P64QCube81.lean    25f05a17cf291072514bbbe1b477edad173bd497e5dc019be01df811fd5661eb
graph.json         41c8602480cee0e9a21d3a4cd2a7719fa395bd6aabba821aeb7a9f5c776a3db3
P64QCube81.olean   f2b88d807ac99ebfa8a73b25ed354a302b93a35f53eda9816b3c842502b7a64f
P64Graph.olean     4be074aa56722e991b3c067e22a00d19e2b90b8ab97b0755cc606eecb0b2445c
Lean binary        e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
```

The direct graph object is from the captured P64 overlay. Full transitive
source/object, package, dynamic-library and search-path ancestry was not
independently audited in this check.
