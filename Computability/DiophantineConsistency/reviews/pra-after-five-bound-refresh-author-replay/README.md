# Historical five-bound dependency refresh

This is the source snapshot immediately before the later upstream `PRASppow2WitnessBound` change. The author rebuilt 12 affected local modules after five supporting bound files changed; the independent replay uses a hash-verified frozen copy of all 246 reachable local sources, preserving the same repository-relative module paths. Source/object/check log hashes match the author. The frozen tree is external to the current workspace at the path in `frozen-source-location.txt`.

An initial peer attempt failed because Lean rejected a source outside its default workspace root; the failed receipt is preserved under `failed_root/`. The corrected replay supplies the frozen tree as Lean's root. Foundation source/object anchors are authenticated; remaining Foundation and Mathlib transitive dependencies are inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-after-five-bound-refresh-author-replay/replay.py --parent /tmp/pra-after-four-pra-independent-4gykvw94/lib --source-dir /tmp/pra-five-bound-frozen-root-qcr693jk/Computability/DiophantineConsistency/Lean/DiophantineConsistency --lean-root /tmp/pra-five-bound-frozen-root-qcr693jk
```
