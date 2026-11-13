# Root74 lexical `linear_combination` import audit

This read-only source analysis examines the 159 inert files in the committed
root74 slim overlay and the recorded lexical project-import graph. Eight draft
modules contain the token `linear_combination`. A graph search finds a recorded
project-header path to `Mathlib.Tactic.LinearCombination` for six; it finds no
such path for `PairEvalRingBridge` and `OwnZeroGuardStrict74` within this
bounded graph. The receipt records source lines, observed paths, and all
unexpanded external/package/Foundation leaves.

This is not Lean dependency resolution and no absence conclusion follows:
unexpanded leaves may themselves import the tactic, generated imports or runtime
behavior may matter, and token matching is lexical. No Lean error or successful
elaboration has been observed. The separately reviewed inert import snapshots
for those two modules each prepend exactly the tactic import. In-memory
regression controls confirm that each corresponding bounded source graph would
then contain a direct lexical edge; this does not establish provider coherence
or a working build. Original reviewed clients and overlays remain unchanged.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root74-tactic-import-audit/check_source.py | cmp - research/ordinary14-root74-tactic-import-audit/observation.json
```

No Lean run, launch readiness, model/iPRA endpoint, physical-byte or PDF
binding is claimed.

Independent source review: [root74 tactic import audit](../../reviews/ordinary14-root74-tactic-import-audit-independent/README.md).
