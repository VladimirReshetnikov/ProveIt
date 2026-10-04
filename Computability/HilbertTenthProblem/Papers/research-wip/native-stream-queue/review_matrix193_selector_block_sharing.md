# Independent review of shared matrix selector blocks

**PASS, with no requested correction.** Root read the complete frozen helper and companion and independently checked all four full arrays. The operation saving is 92 = 46M + 46A per variant. Every complete polynomial and positive witness interface is unchanged relative to its immediate terminal-power parent.

| Author artifact | SHA-256 |
|---|---|
| [Helper](matrix193_selector_block_sharing.py) | `25a3416d94475f1df98aa34f20a9e182e4ea6fcc2e39ff6b47c401eadd40790a` |
| [Receipt](matrix193_selector_block_sharing.json) | `cfaab226e28465ee1332bd38915ca49e6befe91a2931181d19eaf66603121584` |
| [Proof](matrix193_selector_block_sharing.md) | `0f42494cede122d0373fb1fb8c249ea612d480e13fa651f7ece4daff76e42cd9` |

The nine intervals are disjoint in each word and contain 55 common coefficients. Their Horner evaluations cost 92 rows; the 26-block X and 51-block Y partitions require 150 paid concatenation rows. The resulting 242-row component replaces 334 rows. All five required Q powers are already paid, and the full sequential source audit checks their availability together with all selector leaves. This is a concrete partition, not a global optimum.

## Independent evidence

The separate [review checker](review_matrix193_selector_blocks_checks.py) derives the replaced producer sets from the actual old/new array difference. Exactly two retained definitions change, 332 old internal producers disappear, and 240 new internal producers appear. It checks the private consumer boundary of both components and literal equality and ordering of every surrounding row. Full topology, backward liveness, interfaces and arithmetic counts are independently recomputed.

The independent local algebra is stronger than comparing the author's grouped coefficient lists: it recursively expands both entire selector outputs through the paid group additions into the 98 raw edge-hat values and Q. Every raw-hat coefficient agrees exactly. This covers the two full words in each controller variant, including the LOAD chart value. The proof works at arbitrary formal Q and selector values; no typing or division is used.

A separate full-circuit congruence interpretation binds these expanded cuts to the actual expressions of Q and the raw hats. It checks every common register and the complete output. This establishes the whole commutative-ring identities on identical supplied coordinates, independently of the author's modular diagnostics. All sixteen complete fixed coefficient words are also expanded, matching 2,704 entries, and their entire 553-row component remains literal.

The author helper's explicit old/new finalizer traces were read in full: they verify the output, native multiplier, one-plus-SOS, unique residual squares, full sum tree and private consumer boundary. The independent surrounding-row check also covers all finalizer and native definitions; the separate review checker does not claim a second implementation of that trace. The full output identity itself is independently proved.

| Variant | M | A | Total | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| None | 686 | 732 | 1,418 | 141 | 35,587 |
| Flow | 685 | 730 | 1,415 | 140 | 53,345 |
| Population | 685 | 730 | 1,415 | 140 | 53,347 |
| Both | 684 | 728 | 1,412 | 139 | 71,105 |

All 5,660 rows are covered. Exact degrees transfer through the full polynomial identities on unchanged variables; this review does not rerun the inherited native or leading-degree theorems. The valid fixed-program recipe and full positive zero tuples are unchanged relative to the immediate parent. Earlier terminal-carry and IDLE comparisons retain only their ordinary-input projection scope.

## Replay and limits

| Independent artifact | SHA-256 |
|---|---|
| Checker | `cf5ee9aefaae474047bf1c16b2caaaa924f18ee8c71e550c9b7b60aac1f08282` |
| [Receipt](review_matrix193_selector_blocks_checks.json) | `7bc08f3ed89d498fc7042a3e40f0d9549ed2fa825cf1d22b741058456070709f` |

Fresh author and independent normal/optimized exact receipt replays from `/` pass. The review checker accepts `--root` for the installed dependency directory and `--author-root` for the new trio, defaulting to `/tmp`; set the latter to the installed directory after publication. Use mutually exclusive `--output` and `--expect`. Canonical JSON receipt equality distinguishes types, and all guards stay active under optimized Python.

No predecessor code was executed or imported, no giant accepting trajectory or native Pell tuple was constructed, and no arbitrary coefficient slice is claimed to be universal. The separate universal84 bound remains unchanged.
