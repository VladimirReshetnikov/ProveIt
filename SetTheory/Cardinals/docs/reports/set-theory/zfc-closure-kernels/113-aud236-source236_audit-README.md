# Source audit of the incoming 236-state construction

This supplement audits the source part of `ZFC236_Construction_2026-10-19.zip`, newly added in ProveIt commit `0b5fec6980cc3a5ba7dd47b404f0cbbe9a451c02`. The 236-state construction is upstream work. The fresh audit and controlled NIP compatibility check here add evidence and clarify what can be combined; they do not claim a 235-state machine.

The input DAG is exactly the 287-entry structure array with root 286 used by the adjacent `source237_experiments` package. Node 234 is changed from `(233,(122,115))` to `((233,122),115)`. All three chunks are closed, with 245, 160 and 132 instruction occurrences. Sequential associativity therefore proves their equality for arbitrary natural register values and any surrounding source context.

Fresh replays of the incoming builder and independent source checker both pass. Exactly 537 source paths change, while all 6,455 ordered instructions and every guard successor remain unchanged. The number of live source nodes stays 224 and the maximum zero run stays six; maximum path depth increases from 48 to 49. The four literal decoder edits at states 177 and 185 match exactly.

The useful effect is a changed helper edge. The new `177/1 → 212` completes a three-step predecessor-bit detour needed to merge state 223 into 182. Thus a source change that leaves source size unchanged and increases depth can reduce the final binary state count. A source-cost objective alone would miss this benefit. The binary fold and full runtime are checked elsewhere in the parent package.

`check_compatibility.py` supplies an additional control-graph equality check. It applies binary increment and bit-stripping to each source path, then decodes the result with zero padding through a complete binary trie. This is independent of the incoming checker's ordered-interval successor calculation. Equality of these ordered graphs transports the parent's register invariants by instruction index without recalculating the invariants.

The rotation prefix is `1110100100110110101010011100001`. The six-leaf NIP specialization uses the disjoint prefix `1110100101`. The checker applies both source edits in both orders and proves literal equality of the resulting leaf lists. The joint source has 6,449 leaves and score `(224,6,49)`. NIP's inherited scratch-register precondition remains required; commuting source rewrites does not remove that hypothesis.

The tempting five-row NIP decoder graft remains invalid on the literal 236-state table. On the unchanged instruction `CI8` at path `01010`, the standard legal all-zero register frame returns correctly in 636 transitions. The edited table returns after 648 transitions with the same incorrect tape difference found at the earlier 237-state checkpoint. No smaller binary count follows from the source compatibility.

## Files and replay

This directory is designed to be copied to `source236_audit/` beside `source237_experiments/` and `machines/` in the parent deliverable. It needs only Python's standard library. The adjacent source kit provides `source_core.py`, `finite_runtime.py`, `nip_counterexample.py`, and their pinned JSON/table data. The machine directory provides `sites_logical236.json` and `zfc236_old.tm`.

From this directory:

```sh
python -B check_compatibility.py
```

Paths may be overridden with `--kit`, `--machines`, and `--output`. The default output is a new `compatibility_replay.json`; `compatibility.json` is the saved fresh result. Do not use Python `-O`.

`sourcecheck.json` records the fresh incoming independent-checker replay; `source_certificate.json` records the fresh incoming source-builder replay. Their original programs remain attributed to the incoming 236-state package, which the parent deliverable retains. `compatibility.tex` is a short report section. `MANIFEST.json` gives the exact file list and hashes, without duplicating the earlier package or the 6,455-row source data.
