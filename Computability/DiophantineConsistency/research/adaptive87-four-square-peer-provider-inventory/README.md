# Peer-overlay candidate for the 88/30 instantiated closure

This read-only inventory inspects `/tmp/nine-ipra-guarded-peer-20261102-a/lib` against the **658 project names** in the source-declared closure of the proposed conditional model client plus the 87 bridge instantiation, pinned by `research/adaptive87-four-square-local-mod4-model-draft/result.json`. The source edits are unelaborated. No object, source, provider, or prior receipt was modified.

All 658 `.olean` paths currently resolve: 11 are regular files and 647 are symlinks whose targets reside across 12 distinct provider roots. This includes every one of the 14 names absent from both historical HA87 and current14-base roots in the earlier bounded scan. The receipt records each qualified name, resolved object path, SHA-256, and provider count. It does not check that the resolved objects were compiled from the current sources, that their imports are coherent, or that this overlay has suitable package/toolchain objects or companions.

A deliberately limited adjacent-source heuristic looks for `src/<qualified-module>.lean` alongside each resolved object's own `lib/` directory: 99 source snapshots match current bytes and 559 are absent at that conventional location. Those matches do not prove object provenance. The separately identified HA87 frozen source tree accounts for 174 selected HA87 objects: 173 source snapshots match current bytes; `NaturalExpression` differs in proof text. Source drift alone establishes neither incompatibility nor compatibility. The special HA87 comparison, every object and available source hash are recorded individually.

`reviews/nine-variable-ipra-peer-stages-eleven-fifteen/README.md` describes retained stage-specific peer evidence and its limits; the present scan does not replay or authenticate that evidence, nor extend it to the entire overlay. In particular, 658 filenames and object hashes are **not** an authenticated provider selection or proof that an 88/30 build is feasible. A guarded full source/provider consistency and dependency audit remains necessary. The 87 bridge itself depends on FactorUnits even though the alternative conditional model client does not.

Reproduce from the DiophantineConsistency directory:

```sh
python3 research/adaptive87-four-square-peer-provider-inventory/check.py > /tmp/adaptive87-peer-provider-current.json
cmp research/adaptive87-four-square-peer-provider-inventory/result.json /tmp/adaptive87-peer-provider-current.json
```

The scan reads the approximately 246 MB of resolved object bytes to hash them; it invokes no Lean process and writes only the scratch receipt. `/tmp` artifacts may disappear or change, in which case the result must be reexamined.
