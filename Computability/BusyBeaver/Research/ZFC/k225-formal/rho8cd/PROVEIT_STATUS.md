# Status in the maintained proof checkpoint

This directory preserves upstream research from `159397838a` / `4fdc59197a` and `2ca3a5c16f` / `d93adc4174`. Its raw README and renderer describe the upstream construction and reported focused checks. They are not new receipts for the maintained checkpoint. No delivered renderer, search program or Rocq compiler ran during either import.

The current [phase-eleven Lean checkpoint](../verification/k215/simplification/phase11/README.md) adopts the generic 58-step derivation with its two final single-use aliases inlined. It retains the exact numeric adapter, composition and lifting interfaces. All eight affected modules and both external ZFC endpoint clients pass fresh Lean checks. The maintained producer reads the attributed source as pinned data, checks the original derivation and both inlinings, and reproduces the exact checked core. The original numerical rendering remains recoverable from `4fdc59197a`.

The live Rocq `DomRho8.v`, regeneration record, manifest and `regenerate215.py` retain the exact earlier checked bytes. The proposed four-file change remains recoverable in Git history. Consequently, this directory's command examples do not imply that the live regeneration route has adopted the new derivation. The [merge record](../verification/k215/simplification/phase9/upstream-merge/README.md) binds this boundary.

The 58-step proposal internalizes lifting and composition and removes the private seed wrapper. Its [original static comparison](../verification/k215/simplification/phase10/upstream-merge/source-review/review.md) measured 755 bytes / 35 lines saved before the two inlinings. The adopted core saves 1,016 bytes / 43 lines over phase ten, with the same public interface and assumptions. Kernel/API, affected endpoint and producer-reproduction checks now pass. The delivered `--core` command remains a historical rendering route; the maintained producer uses pinned source data without running that renderer.

The later `88c8114d21` research merge also proposes a separate 56-step `Lukasiewicz` proof. Its exact source is preserved in the [phase-eleven merge record](../verification/k215/simplification/phase11/upstream-merge/README.md); the maintained Lean module retains its checked bytes pending comparison with shared-basis proposals and local API/endpoint checks. New research renderers and Rocq files were imported as data and were not executed.

**Update (shared basis, after batch 212).** The shared-basis proposal is now applied on the Lean side:
[`derivation_core.txt`](derivation_core.txt) is a 58-step derivation whose goals are the row,
composition, prefixing, K, Peirce and S; `DominatedImplication.lean` renders it with `k`, `peirce` and
`s` exported, and the `Lukasiewicz` namespace is an adapter over it (domination holding everywhere),
replacing that module's separate derivation (both files: 811 → 409 lines against phase eleven's bytes).
`lake build` of `DominatedImplication`, `DomRho8`, `KCodeDom`, `Lukasiewicz`, its importers and
`KEndpoint` passes.
