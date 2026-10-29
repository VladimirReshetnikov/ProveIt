# Construction Pell ordinate bound validation

Source commit `530dc224fb8ac1e0fb4b6ba3c92a0823cfa2a5c6` and parent `5ac8de3f96feab11e5ed723bdd9bce8a87f5d344` match the tested final and baseline source snapshots of `ArithmeticConstructionBoundPell.lean`. The baseline and final SHA-256 values are `c8e6c082403ef2a1c9c9bd63ea9c96a7bd6e6971d0bb4a187e85ca21c539037b` and `bfb6db9d60d53d0d6283081e6a8b92e3feff4b9c1295f316d9a0bd64cb284ef8`. The affected proof originated in Claude-coauthored commit `f1463077445`.

The change moves `x_le` before `y_le` and derives `y_le` from `x_le` and the existing recurrence coordinate bound. It removes three net lines and preserves definitions, imports, hypotheses and theorem statements.

Paired target and direct-client builds all passed; all logs were empty. Target objects differ, while both client objects match byte-for-byte across phases:

| Module | Baseline SHA-256 | Final SHA-256 |
|---|---|---|
| `ArithmeticConstructionBoundPell` | `7f8fea870109c68a2b3e4ff71830cde705c7ef33c697e5ad6cb7455781760203` | `95d95b360bb0aa99926976882e0a659c629e293b1879d71ba9abb3894a57fe1f` |
| `ArithmeticConstructionAssembly` | `e7f69999cd0ced816ece92c68ae5ffe60052e3c4802a464c946eee29053d3e71` | `e7f69999cd0ced816ece92c68ae5ffe60052e3c4802a464c946eee29053d3e71` |
| `ArithmeticConstructionBound` | `b99aa2b68acf9b93716c38e30381921cdb8bed6ed822990d73a9b72da5f9c259` | `b99aa2b68acf9b93716c38e30381921cdb8bed6ed822990d73a9b72da5f9c259` |

The initial lane used a cached `ArithmeticPellAuxiliarySeed` object without a matching source-current producer. The refreshed lane uses the source-matched object; each of its six resulting objects exactly reproduces the respective initial lane object. Eight refreshed probes pin the phase-specific target, Recurrence and AuxiliarySeed objects. All 32 target names, printed type/axiom output and sampled 29,056 simp and 13,253 instance registration lines match byte-for-byte. These comparisons do not prove equality of proof bodies or all persistent extensions.

The following eleven direct project providers have matching successful source/object producer receipts. Their hashes and paths refer to temporary files which may later disappear:

- `ArithmeticOuterSeed`: object `4a0d306bca37b4750344c30e3d1236bbc0464b708b223fa8cee43696c22b537f`, source `b4b52261c47dd58fa3cf49a2ca79cee73c5e5013cc3cc4aa1ad340bcfe24b15f`; `/tmp/construction-share/refresh-records.json` (record SHA-256 `c32e5316b3b927ced46611fdf2ae754e101f7916c18815dc105020aae75432f5`).
- `ArithmeticPellAuxiliarySeed`: object `b2a7e54ab326f100807de5abd87e63915af3434abd643cbe810df3e016deb0ff`, source `f3769f93fe14b8ad50310050e8dbf9b7fa4347adda34af63eeee1abe470fd2c2`; `/tmp/auxiliary-seed-positive/final-records.json` (record SHA-256 `06254046e705da2986ee2cd8da90197ac6eb0c82848b1f457bbc27092a0158c8`).
- `ArithmeticTilingWord`: object `fbc52af7dfde701c4abf3a40104f8ab694ce2c4f51086ad23645e26efb92de22`, source `b412f70d7089bd9387b00cfa6a5d82b75baaf3cf9d665d85ce9f1e8b8e64c049`; `/tmp/tiling-band-dispatch/final-records.json` (record SHA-256 `f177197a98c41348cd140fa89242b77015ac6d791cdb46089e5b7370422e363b`).
- `ArithmeticPackingCells`: object `463c6d28cd093ae86ca51b9806a01172d3e6fede16d3ab80358f48caaa207b5b`, source `587aba5c1fdc98187f40301e613d3594c5b579dd5da6c070bc73651bc92e8174`; `/tmp/packing-rotation-simplify/final-records.json` (record SHA-256 `91612d609dff484ea7479cb45f6f78eea063a33fa0398fe2704a544109db3c4f`).
- `ArithmeticRankForcing2011`: object `6f662b989ef254022389ba70e4bcecfadced9b72b99e26533891e71f4efbb7b0`, source `5dc4f4170b0d2e0202dade59dd2da97e511d5869ee5b1db2e624367b69a8394d`; `/tmp/four-positive-wrappers/refreshed-final-records.json` (record SHA-256 `84e3b7e2c3cd762f3c6096b5badbc584bcb4af9092cf49c16c33160582341c2c`).
- `ArithmeticController`: object `9d7d5436e5e98c3d025254e27714ae0f1f532a037ee5844f05a4a6b373681126`, source `ad3dc1fe546f22f92134860b2ec0bf94a0983a163c2dd2d166639a34ca1e79d2`; `/tmp/construction-share/bound-refresh-records.json` (record SHA-256 `cbfd3d03e804f7893827e48560bf30baa886676b059aff126c2cef9404398150`).
- `ArithmeticConstructionUnit`: object `3e3f5908d210bd4ade3b9c4905f1cec32c43c44758ed24fa9c67ac48f093666e`, source `12b2d20c5aeb22bca72c7caa02e8fcaf28d3eff7e1559240ec4cdf62c37e297e`; `/tmp/variation-tail-sharing/refreshed-common-records.json` (record SHA-256 `a5ed04614c1afe0672fad225f73e3e87b4ba7b7e26639229e2ad8d8bdefad208`).
- `ArithmeticConstructionVariation`: object `1d5398ef9465346996d318960a4d4ad41af6111059e60cd58cfdfd32c945b293`, source `fd64bbaaa59016ac501ed3d1e53124f0f9163fc51767cbf1428dd95dc78c2672`; `/tmp/variation-tail-sharing/refreshed2-final-records.json` (record SHA-256 `33cb5114083d883b00c9ea577571fda514f91e2a5a0b4a77d8281200a0cdc6ec`).
- `ArithmeticConstructionZero`: object `d7df6e08c7d2089edfba036b794f81905bb94499e5f0a3afcee32e161702229b`, source `fdef557a958ba7176529795359d5145a0e713ffe8a4a38a1f8609bd59d3e617c`; `/dev/shm/construction-tau-positive/final-records.json` (record SHA-256 `d85ead0b70933c85c2f087c12fad3732f18fc8e5576a7493b32b83f4a4447ef5`).
- `ArithmeticCurrentSentence2011`: object `42b8d5c746802687ba40fdaa93304c6c5f0513a5b0f674c8434795081febbfdb`, source `10c1a2e92f05c9765e91fd872050b25c23a94754ec87a0122aebd2e4c90c13e6`; `/tmp/signed-pairs-factors/final-records.json` (record SHA-256 `bb15b29690d49eef61b2f4f18a995c497db65fa1cfd9f0c9441899be5000e843`).
- `ArithmeticLocalNormalization`: object `f78f08081135f5295c9516cd97208d5799818700223c01c3c767ebc84f29006d`, source `5d5c6d4850083c1cc1993cad50da5b88dba39948a034133d19f1d2169f477803`; `/tmp/construction-share/bound-refresh-records.json` (record SHA-256 `cbfd3d03e804f7893827e48560bf30baa886676b059aff126c2cef9404398150`).

The additionally pinned current Recurrence object `0b58739aea61f13a516c86ccab1dad0d39021fda50bf84ff91ab3f5cd557d5f0` matches source `b2c9d9dc41be16aa503540851c3c9752e2c475a947666f79eb9ea539aebe14af` in `/dev/shm/shared-pell-recurrence/final-records.json` (record SHA-256 `25f1a912a593a0ef8360a5c43c36f5de4d8f7a1e555101d27cd64745b555fbee`). Its source hash was sampled at review and matched the successful producer’s before/after source pins.

The final client input records sample the baseline workspace target source before adoption; the final target build separately links the actual object to the final source snapshot. Other project, Foundation and Mathlib dependencies remain cached; no full source-current transitive build is claimed. Raw logs and compiled objects are not included in this note. Timings are single shared-load observations.

Key external validation records and scripts (temporary, not included):

- `/dev/shm/pell-bound-coord-refresh/baseline-records.json`: SHA-256 `5ca6327e6e5ff2c265aa221a2ad042c352afedb7b30c1c173e303d25435cb59e`.
- `/dev/shm/pell-bound-coord-refresh/final-records.json`: SHA-256 `e728c5c69ff5d2955588193f4e0d0f67b86ace1d85fdcbdefd5b8caa6d72b0bc`.
- `/dev/shm/pell-bound-coord-refresh/probe-records.json`: SHA-256 `6be11f68bedf1c0978079d04a2e637fceb4033cb0655cf9623e9629431342ccb`.
- `/dev/shm/pell-bound-coord-refresh/audit.py`: SHA-256 `e443e2ca8f11e27b511a25102d4b259ece8abcff6d83d01cfdd90c1f25f044cc`.
- `/dev/shm/pell-bound-coord-refresh/audit.log`: SHA-256 `83a0335cd48b08c7663afc27cd96057043c7c8ba948a356f1337433b3f6cadb9`.
- `/dev/shm/pell-bound-coord/baseline-records.json`: SHA-256 `005eb80e7598f7e3f6a0306a73dd11622ceb5955ae6c0dccd9647a2bb2564a2a`.
- `/dev/shm/pell-bound-coord/final-records.json`: SHA-256 `f953a48c7735c6ad693c62daa42b0769032f87d0df0cabe13a2d04f34619226b`.
- `/tmp/pell-bound-coord-peer-audit.py`: SHA-256 `35b24addfcdca16371e877fe514b8093a0adbd826319e493072504915f320f1c`.
- `/tmp/pell-bound-coord-peer-audit.log`: SHA-256 `fe36af82a3355d9b6948cf4a7652078426cb03fe031a7447ac0170ee36ea64e2`.
- `/tmp/pell-bound-coord-peer-review.txt`: SHA-256 `7e2c27ea730e860ccb25beccf010827f1e04454835cdcf392bb5c608075abe00`.

The independent review checked the six refreshed builds, initial/replay object correspondence, target/client first-path and source pins, all eight three-object probes, eleven direct producer associations and the Recurrence association. It independently compared the source snapshots to the commit and its parent. Full replay requires the external records, build environment and excluded compiled objects.
