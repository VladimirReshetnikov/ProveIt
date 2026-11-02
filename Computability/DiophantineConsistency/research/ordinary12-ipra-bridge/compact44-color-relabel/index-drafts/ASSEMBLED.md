# Author-only index permutation assembly

Exploratory session 81403 actually exited 0 without warnings or `sorryAx` on the unchanged `CompactRelabelInverseAssembly.lean` source. It joins the fifteen author-only forward/inverse cuts into `CompactRelabelDraft.forward_roundtrip`, checks every supplied compact index lies in the intended range, derives no duplicate old-to-compact indices from the explicit inverse, and applies the equal-length subpermutation theorem to prove

```
CompactRelabelDraft.rowIndices.toList.Perm CompactRelabelDraft.compactIndices
```

where `compactIndices = [0] ++ List.range' 2 941`, the compact indices other than 1. The roundtrip theorem's Lean axiom report is `[propext, Quot.sound]`; the final permutation report is `[propext, Classical.choice, Quot.sound]`. The complete output is in `observations/assembly01.log`. The earlier first wrapper failed on an omitted `--root`; the direct `List.Perm` attempt timed out, and the merge-sort shortcut failed with `sorryAx` in its diagnostic, all retained separately.

This updates the historical uncompiled status in `README.md` and `FORWARD-CUTS.md`. The theorem is **author-only exploratory evidence** over the coherent successor overlay. It has not been independently paired or audited; the inverse array's relation to the external finite receipt is checked separately. The finite row equality and color permutations still require a coherent paired replay, and all-model tiling transport, compact44 calibration and an iPRA endpoint remain open.
