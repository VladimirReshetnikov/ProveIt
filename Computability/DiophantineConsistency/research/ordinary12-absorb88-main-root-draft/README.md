# Two-norm gap for actual 88-graph zeros

`Absorb88MainRoot` proves that the 88 and 89 graphs have the same main
residual and extracts its main Pell norm from an actual 88-graph output
zero. The extraction assumes all 12 inputs are positive and takes place in
the indicated models of IΣ₁. `Absorb88GraphGap` combines that norm with the
88 graph's first Pell root and the separately checked
[`Absorb88TwoNormGap.gap`](../ordinary12-absorb88-two-norm-gap-draft/README.md).
For a positive actual 88 zero and positive model value of `beta`, it proves

```
eta + zeta ≥ 8*((X*Y)*Y) + 4.
```

No transport-sign hypothesis is used. The proof does not establish transport
positivity, 88/89 reverse existence, or an iPRA endpoint. The source comments
calling the modules drafts predate the successful checks recorded below.

## Observed checks

On 2026-11-04, Lean 4.32.0 compiled each module with exit 0. The first module
reported `main_same` depends on `propext`, and `main_zero` and `main_root`
on `propext`, `Classical.choice`, and `Quot.sound`; the graph-gap theorem
reported the latter three axioms. No `sorryAx` or warnings were reported.
From the repository root, after building the generic gap object in `/tmp`:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
for TASK_MODULE in Absorb88MainRoot Absorb88GraphGap; do
  LEAN_PATH=/tmp:/tmp/absorb89-chain-gpc9zymd/lib:$TASK_LEAN_PATH \
    /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
    -M3000 -j1 -DElab.async=false \
    --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-main-root-draft \
    Computability/DiophantineConsistency/research/ordinary12-absorb88-main-root-draft/$TASK_MODULE.lean \
    -o /tmp/$TASK_MODULE.olean || break
done
```

Source and result SHA-256 values:

```text
Absorb88MainRoot.lean   a7a60e0f221b953536e7fd9edb6c1f6ed0d83ce3330fe9102fa110ac09467651
Absorb88MainRoot.olean  f5c725deeddd1fcad2faf31a607e34307547ac9f7c4d4de9c2f61552617eab40
Absorb88GraphGap.lean   e52e57650bb3dba7ea44fbda99abbc321771151b3b6e5707cfc221596e356961
Absorb88GraphGap.olean  4221086c49220f43faaab42cb0159aade3b847c3f9369edc9844e976f820b7f3
```

The directly used `Absorb89Main.olean` and `Absorb88TwoNormGap.olean` hashes
were `cddaa25c969a1751e99dfe1387d0f2f1bcddbf556208e6cc2c50639681d97bf6`
and `ff1f89e6c669f00370641823a9a0f6c841eb0411ecb7db1d225d10efc04c5536`.
Temporary prebuilt providers were inherited; their complete project,
package, dynamic-library, and search-path ancestry was not audited.
