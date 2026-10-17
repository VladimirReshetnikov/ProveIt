# Attribution and licensing boundaries

This work starts from **Vladimir Reshetnikov / ProveIt**, pinned at commit `43026ff42f0939f09b9e95495248cfadcad38e38`. ProveIt's register permutation and blank startup already supplied the 252-state baseline. No credit for discovering that baseline is claimed here.

The underlying 254-state machine and calculus were designed by **Mira-Cult**. **Jeff Ketchersid (`jeff87654`) and contributors** supplied the upstream verification. **Andrew James Wade** supplied the public compiler framework. **mira-emmy** supplied the public 253-state reduction. The pinned ProveIt sources credit these contributions; the imported source notices are preserved.

The new research in this archive consists of the cache-result MP source transformation, its ordinary proof-block soundness/completeness argument and calculations, the exact changed machine and new safe physical register assignment/startup, the fresh source-to-decoder binding certificate, and the specifically labeled additional minimization experiments. It was prepared with AI assistance and has not received independent human proof review.

## Imported material

- `upstream/LICENSE.ProveIt` is ProveIt's MIT No Attribution license. It applies according to the scope of that repository's grant.
- The upstream verification snapshot is **excluded from ProveIt's blanket MIT-0 grant**. `upstream/README.proveit.md` preserves this boundary and the original authorship information. This archive does not relicense the unchanged upstream `Dag254.v` / `Prog254.v` material or claim a new blanket license over third-party material.
- The unchanged `.lean` files and research notes are pinned ProveIt reference extracts. They are included to make the mathematical dependencies reviewable; they are not represented as a standalone newly built formal project.
- The unchanged strict-affine engine is imported from ProveIt's research material, at the exact path in `PROVENANCE.json`.
- Optional experimental inputs retain their source bytes and original workspace layout. Their manifest distinguishes copied upstream inputs from new experimental files. Any separately included compiler license continues to apply to its associated files.

`PROVENANCE.json` identifies the primary source URLs and byte hashes. The top-level `SHA256SUMS` identifies the complete release contents. Copied documentation may contain links to dependencies outside this selected reference subset; those dependencies remain in the pinned ProveIt repository.

The report's ZFC theorem is an ordinary mathematical claim supported by the stated construction and inherited proof-specific calibration. The included Python checks, unchanged Lean source references, and a proof-assistant kernel build have different roles. No fresh local Lean or Coq certification of this variant is claimed.
