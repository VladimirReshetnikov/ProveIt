# Annotated renaming constructor sharing: validation

Source commit `056ae83a35295110fb661debe1f0f331d5f9c130`, parent `128d91fcb5777b8a08d1f8c378bcd34865353403`. The target source SHA-256 in parent is `7446348dc765c31954f802e744b3be4903c4f6be04cc77e7382de8e52427d9d4`; in the commit it is `b2b614db72b193f2a4b4ee14132757ff8f98d82963694802efb3e812281b0df1`. Both match the tested snapshots. Moving the existing public binaryForm and unaryForm definitions earlier permits their use as uniform witnesses, replacing tag-specific construction in two proofs. The change removes nine net lines and changes no existing definitions, statements, assumptions or imports. The original proof is attributed to `69b1d0693c1`; no Claude coauthor is asserted.

Both source-ordered phases built the target and nine affected modules with status zero and empty logs. All nine unchanged module objects are byte-identical; the target objects differ. Source and object SHA-256 hashes below are from the paired build records.

| Module | Source SHA-256 | Baseline object SHA-256 | Final object SHA-256 |
|---|---|---|---|
| `AnnotatedRename` | `7446348dc765c31954f802e744b3be4903c4f6be04cc77e7382de8e52427d9d4` / `b2b614db72b193f2a4b4ee14132757ff8f98d82963694802efb3e812281b0df1` | `43d047f0bbf27554affb4c70eafb7ac2bfd2b087de714d166867a19b97fad8e7` | `b20496d005a7652c02105a3d1abbe7f20695a5ed8866fae1c0049e2ab41dc684` |
| `AnnotatedRenameCode` | `ee0682dd2320d2afd91cf69fbf20de2b2aca4bef02cbd226c8a7ed9500a3c3f2` / `ee0682dd2320d2afd91cf69fbf20de2b2aca4bef02cbd226c8a7ed9500a3c3f2` | `4924a49f2dc9a1d2ffb5f557ee42372d2298c0a3d50bf618ccf5f0bbc16549ce` | `4924a49f2dc9a1d2ffb5f557ee42372d2298c0a3d50bf618ccf5f0bbc16549ce` |
| `AnnotatedRenameArithmetic` | `0ece88c11fabd2326385963c9b782d76f91ec61ac6a31f839042f855ec6e34e0` / `0ece88c11fabd2326385963c9b782d76f91ec61ac6a31f839042f855ec6e34e0` | `bf29cdd77c792aceaeb7b3f13eb1d9cdf559cd5c9450c65057c242828d37b277` | `bf29cdd77c792aceaeb7b3f13eb1d9cdf559cd5c9450c65057c242828d37b277` |
| `AnnotatedRenameLocal` | `88fcfc5e0f1110596da793c736188003d01aa3fe654683d8cce651181be0ef5f` / `88fcfc5e0f1110596da793c736188003d01aa3fe654683d8cce651181be0ef5f` | `69e502337add2f5f0973423a91cc03e6160ea3c9ce50ac7ae0072ec0358cdb1d` | `69e502337add2f5f0973423a91cc03e6160ea3c9ce50ac7ae0072ec0358cdb1d` |
| `AnnotatedRenameLocalPR` | `13d1804e9ac4a574d258e9f8a9c116d8931fa0a9bf3510ec2b650d4542f452bd` / `13d1804e9ac4a574d258e9f8a9c116d8931fa0a9bf3510ec2b650d4542f452bd` | `c2e2905752863fc8ab94403d00fafd0f6592fb7fff7062a364d6be44138eb3e5` | `c2e2905752863fc8ab94403d00fafd0f6592fb7fff7062a364d6be44138eb3e5` |
| `AnnotatedRenameScan` | `e30bac0b7c2bffc94a23173d919c720ae9d68f20e7a59a6098e7a714794c1c83` / `e30bac0b7c2bffc94a23173d919c720ae9d68f20e7a59a6098e7a714794c1c83` | `108d73f63d3483af362f36522e488a6000eeebf16172892972ac7f718ebc8707` | `108d73f63d3483af362f36522e488a6000eeebf16172892972ac7f718ebc8707` |
| `AnnotatedRenameScanPR` | `c265a49c1d62a73c4779539b5f5b31ae0cbf6d64010bccfa944abb0ab85c01d8` / `c265a49c1d62a73c4779539b5f5b31ae0cbf6d64010bccfa944abb0ab85c01d8` | `6f4b900acc2819da3b822e9361af6ab8ee27d9e3a31e777075cbac2a492cc610` | `6f4b900acc2819da3b822e9361af6ab8ee27d9e3a31e777075cbac2a492cc610` |
| `AnnotatedBound` | `cfecd9e36dcc48b17285b86737714c9ce54db7457e382fc154fb9208230b5c97` / `cfecd9e36dcc48b17285b86737714c9ce54db7457e382fc154fb9208230b5c97` | `75a6f41e63a9c9f880074ae5ac0b91d1352f5e97a145ec55ee0a1da4d5954013` | `75a6f41e63a9c9f880074ae5ac0b91d1352f5e97a145ec55ee0a1da4d5954013` |
| `AnnotatedBoundLocal` | `4dd12d3261805173e63dc3368676fadaf88c47c34a88f77bf2535f88a2768ca5` / `4dd12d3261805173e63dc3368676fadaf88c47c34a88f77bf2535f88a2768ca5` | `e6725aa9fabdd4deb060ac9ee08d1f26f96a252fecbd88f68632a6194c5e97ac` | `e6725aa9fabdd4deb060ac9ee08d1f26f96a252fecbd88f68632a6194c5e97ac` |
| `AnnotatedBoundScan` | `78c4a1b1552f05b65eb7534114c27f6ecb341be69b6bf76d232ca689a76ab4f7` / `78c4a1b1552f05b65eb7534114c27f6ecb341be69b6bf76d232ca689a76ab4f7` | `dfcfc48feec5aedf1fa8e94b00971f0cde587532ce26cf9b9cf32e49f191d670` | `dfcfc48feec5aedf1fa8e94b00971f0cde587532ce26cf9b9cf32e49f191d670` |

Eight probes pin the exact ten phase objects. All 486 namespace declaration names, printed types and axioms match byte-for-byte, as do sampled global simp and instance registration reports. These comparisons do not establish equality of proof bodies or every persistent extension. `AnnotatedRenameCode` is the sole tracked direct importer; the other eight rebuilt modules are downstream. The umbrella and wider transitive closure remain unbuilt or cached.

The three external direct project inputs match source-current successful producer rows (object SHA-256 / source SHA-256):

- `AnnotatedCodeArithmetic`: `78a1154dcc2839802487d9cc39b09a8832b2edace38fd2cd7d24d0700783b0e5` / `f83ffce78772a76babae394f8b827d2bcdcc77b6776c20b749aaf216b4f32364`; `/tmp/finite-two-rows/common-records.json`.
- `NatIterate`: `a2b3584a30113ae1887a0a67198cc6f51f809c98f3acd0c26f5e6ab3ba48e2ed` / `c52148b71e86cc8f8713889f92bc321160292cc9ab1b6237ae417fc8f847fb2a`; `/tmp/annotated-bound-witness/common-prior-records.json`.
- `AnnotatedClosure`: `cc1d25d027b1aa30483dbb170cde4c8d3ed277c9d969dcba0a273eecfbe37205` / `b57ceb87516be3ff3a2c715ddf1fecd190031010d93512ca7b5fdaeb0189b641`; `/tmp/annotated-bound-witness/common2-records.json`.

Final client input records sample the baseline workspace source path for AnnotatedRename; the final target build separately links its actual object to the final source snapshot. Other project, Foundation and Mathlib transitive dependencies remain cached, so no full source-current closure is claimed. No raw logs or compiled objects are included in this note.

The following transient external records and independent-review artifacts are identified by SHA-256; they may not remain available, and full validation requires them and the compiled dependencies:

- `/dev/shm/annotated-rename-construct/baseline-records.json`: `8e3ad88923d6ee34bafb9caafc8c65f963fecba890532f745da5a0d969f003ee`.
- `/dev/shm/annotated-rename-construct/final-records.json`: `5d7c7fe42091cf8000840a30f54b926b8067f70218df178e65330eff74223226`.
- `/dev/shm/annotated-rename-construct/probe-records.json`: `1e3e7ab228fd5db018c049184295613e58ae2c6e78aa7bc929ebeac54c741b17`.
- `/dev/shm/annotated-rename-construct/build.py`: `de716e453864af07bca5635b679288742cac8686305fb4563ea6f722a956e1cb`.
- `/dev/shm/annotated-rename-construct/probe.py`: `0918df1ddb0e1de889d90a38fd951b87fc5355db2e079a1e9a2c581fa0f7fc30`.
- `/dev/shm/annotated-rename-construct/audit.py`: `0e6f94e863b8207f8e4ae749a24eebbc853b465590c22e5c848eb36a85caeeab`.
- `/dev/shm/annotated-rename-construct/audit.log`: `1b90fb41ca226decfa334378ea1816c74b11dd2f115fc39d763cc1240dce3dfd`.
- `/tmp/annotated-rename-construct-peer-audit.py`: `a02fc09080b820a19762219d7cfeedb832a448ed3559f570e4787c4d73aab41e`.
- `/tmp/annotated-rename-construct-peer-audit.log`: `0869c635bdb937ac80304ad5e164a7c73b7d82ad85382bb0e928e62282a0f4f8`.
- `/tmp/annotated-rename-construct-peer-review.txt`: `7b4f88c51911e56b8a7b7c053d032fcf688b205bbef8ee2924e513e1fd9898a0`.
- `/tmp/finite-two-rows/common-records.json`: `b822fd24d0554bce9f4f24f9f8e01c785e9a3925fb6ecfe1004e800eb1fcaf89`.
- `/tmp/annotated-bound-witness/common-prior-records.json`: `5e0c3bd5fc248da7501aa711fdd8319a26fe7a8e91ff88d6fa0d210b5e5fdf78`.
- `/tmp/annotated-bound-witness/common2-records.json`: `126000b7411fd5e5b3422d685e719291ed1fa608264ad48aab020bd01ca257c5`.

Independent review checked the paired builds, actual first paths and object/source pins, all ten-object probes and comparisons, the three provider associations, and commit/parent snapshots; the reviewer did not rerun Lean. The reviewer found no issue.
