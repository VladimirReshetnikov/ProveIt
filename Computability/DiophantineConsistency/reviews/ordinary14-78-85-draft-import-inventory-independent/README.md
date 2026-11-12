# Independent source review: static 78/85 draft import inventory

The independent checker verifies the captured root, every listed source hash,
initial-header import edge, unique bare-module resolution within research,
complete reachability from the root, and dependency-first order. It also
checks that each directly named qualified module has the recorded source path
and hash. The author's static receipt is replayed separately.

This is deliberately not a build or provider audit. It does not recurse through
qualified-source imports, inspect objects or search paths, verify a toolchain,
run Lean, or establish model equivalence. Header parsing stops at the first
nonblank non-import line, as stated by the author packet.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-78-85-draft-import-inventory-independent/check.py > /tmp/draft-import-inventory-independent.json
cmp /tmp/draft-import-inventory-independent.json reviews/ordinary14-78-85-draft-import-inventory-independent/result.json
```
