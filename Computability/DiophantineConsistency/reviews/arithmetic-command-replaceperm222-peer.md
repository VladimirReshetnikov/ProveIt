# Independent actual C222 raw-command replacement review

Reviewer: `controller_certificate`, 26 October 2026. Author: root. **PASS; no source correction requested.** I read the complete 115-line main and 34-line Checks before executing, along with the complete actual WordPerm222/StepPerm222 sources, the actual EnumPerm pack/decode/cstep definitions and Cantor inverse contracts. I also read the complete author replay driver, detailed final/development records and the preserved failed diagnostics. Root's prose author receipt was still being written; this review binds the frozen source and replay packet directly.

## Exact scope and mathematical findings

Main SHA256 `92b7602593e268995e14c2d808f4dfd6b72fb3379e263ad705485c630c71efcb`; Checks SHA256 `6b1f854b1742216f7280b377f10375d704d10f743fb3745ba1a604c79338ddd8`. Author packet `reviews/arithmetic-command-replaceperm222-replay.json` SHA256 `7761a874d97aedc5d90557f0bc861b947a146bf60be86bcb41a0ec4099863455`; its 13-file bundle manifest SHA256 `eabbb717a17665a89f22a0cf04c1b9b6637a362427bba9d97c10515401ca3794`.

`replaceValue` retains precisely the actual command's meaningful fields. Tags0/1 retain no argument; tag2 retains the first payload argument; AX tags retain the first and second payloads in literal y-then-x order. The fixed Σ1 graph has unbounded reconstruction witnesses, correctly allowing the replacement tail to exceed the original raw code. Its totality is over arbitrary internal IOpen inputs, not only valid standard command codes. It does not rely on tag positivity or a shifted program-pointer interpretation.

Projection preservation, tail replacement, repeated replacement and restoration of the original tail follow the actual Cantor projection identities. The single-command effect theorem splits both short tags before ignoring unused payload projections. Thus it retains the old working counter and the actual AX arguments, while correctly allowing irrelevant projections to change. Raw0 remains NIP, including its h=1 halting branch; no hidden nonzero or successful-step premise is present. The focused checks explicitly retain the AX y/x order and zero-result equivalence.

The Nat adapters use the four literal EnumPerm.pack forms and actual pack_decode for every raw input. They do not assume an old254 replacement layout or semantics. This is a raw word-tail and one-command-effect result; it does not establish append execution, full enumeration/compiler correctness, proof-calculus soundness or PA/HA consistency calibration.

I authored some prerequisite C222 template/seed and checker-interface leaves elsewhere in the accepted closure. I did not author this replacement packet or the WordPerm222/StepPerm222 command interfaces. This receipt is independent review of the new root packet, with explicit source inspection of its relevant prerequisites; it is not an independent reproof or fresh compilation of that prerequisite closure.

## Independent private replay

Fresh main/check replay PASS in 7.176 / 1.906 seconds under `lean -M6000 -j1 -DElab.async=false`. Main diagnostics are empty; all13 checks report exactly `propext`, `Classical.choice`, and `Quot.sound`. Both fresh objects are byte-identical to the author:

- Main object SHA256 `4e18ca3077d3037e1590750c30a3e93e68d07d215f40d9ee4ca903c0d48b9115`.
- Checks object SHA256 `599da0e6a8ee41891ac5d0cb7818c12a55a049072564054a96c247345a439261`.

Private overlay: `/tmp/command-replaceperm222-controller-peer-eoqs3xl4`. Both reviewed targets were excluded from reused objects and freshly produced there. Exactly107 source-authenticated cached prerequisites,86 Foundation modules,365 artifacts and37 explicit external primary boundaries were reused. All1095 inherited/explicit input pins, the actual reconstructed dependency graph/import lists, compiler, external primaries, source snapshots, author bundle and final source/object pins were verified. There was no Foundation or other prerequisite build. LEAN_PATH excludes the shared project cache and retains only the private overlay plus the recorded package/toolchain roots. The512MiB disk guard passed before both invocations.

Independent detailed record: `reviews/arithmetic-command-replaceperm222-controller-peer-replay.json`, SHA256 `e93eff7973ffd66811517bb41b8a5ce9ea42f79166ba30bbcb0a5890289aeffd`. Durable snapshots/logs/timings/driver/RESULT and a pinned FILES manifest are in `reviews/arithmetic-command-replaceperm222-controller-peer-replay/`.

The first peer preflight stopped before creating an overlay or invoking Lean because the inventory deduplicates repeated public/meta imports while the first parser preserved duplicates. Inspection of actual Foundation.Meta.IntProver confirmed that only duplicate names differed. The corrected parser deduplicates in first-occurrence order; no import was removed from the dependency set. The prior driver and explanation are pinned in the peer record. Both actual peer Lean invocations passed first try. The author's earlier failed lower-bound/MP-projection attempt remains preserved and is not counted as accepted compilation evidence.

No frozen source, shared object, shared documentation or Git state was changed.
