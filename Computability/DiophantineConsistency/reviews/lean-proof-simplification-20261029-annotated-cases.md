# Annotated local-check case analyses: validation

Source commit `a2349090407141da823bf7660cbbae0c15eb975a` and parent `1bcd99bcf9dc65dc03d5819d480a589425cb2372`. Both localCheck_correct proofs replace eleven per-tag inequalities with two uniform bounds and one shared small-tag simplification. The source diff removes 30 net lines; definitions, assumptions, imports and existing theorem statements are unchanged. The original proofs came from commits `521b699865f` and `12a8d2671f8`; no Claude coauthor is asserted.

Parent/commit source hashes:

- `AnnotatedRenameLocal.lean`: `c091126cb9b6b4403b1bff8d2dbe13400e1bb92610002bee30f3826e713a150f` / `88fcfc5e0f1110596da793c736188003d01aa3fe654683d8cce651181be0ef5f`.
- `AnnotatedBoundLocal.lean`: `afc683cae12529a1606298e39be58e214688cbf5f447ee15ca3d9225def43c36` / `4dd12d3261805173e63dc3368676fadaf88c47c34a88f77bf2535f88a2768ca5`.

All 14 source-ordered builds pass without warnings. The seven paired output object hashes are:

| Module | Baseline | Final |
|---|---|---|
| `AnnotatedRenameLocal` | `a2cae2d7efbb1d2fe897c240f15fa5b816e879ad056fc53f6a1722ba634fb1bd` | `69e502337add2f5f0973423a91cc03e6160ea3c9ce50ac7ae0072ec0358cdb1d` |
| `AnnotatedRenameLocalPR` | `c2e2905752863fc8ab94403d00fafd0f6592fb7fff7062a364d6be44138eb3e5` | `c2e2905752863fc8ab94403d00fafd0f6592fb7fff7062a364d6be44138eb3e5` |
| `AnnotatedRenameScan` | `108d73f63d3483af362f36522e488a6000eeebf16172892972ac7f718ebc8707` | `108d73f63d3483af362f36522e488a6000eeebf16172892972ac7f718ebc8707` |
| `AnnotatedRenameScanPR` | `6f4b900acc2819da3b822e9361af6ab8ee27d9e3a31e777075cbac2a492cc610` | `6f4b900acc2819da3b822e9361af6ab8ee27d9e3a31e777075cbac2a492cc610` |
| `AnnotatedBound` | `75a6f41e63a9c9f880074ae5ac0b91d1352f5e97a145ec55ee0a1da4d5954013` | `75a6f41e63a9c9f880074ae5ac0b91d1352f5e97a145ec55ee0a1da4d5954013` |
| `AnnotatedBoundLocal` | `f06b5be7fb818261fc78158c9a3b482eaccf069383963c6d50faba86b3b8a65f` | `e6725aa9fabdd4deb060ac9ee08d1f26f96a252fecbd88f68632a6194c5e97ac` |
| `AnnotatedBoundScan` | `dfcfc48feec5aedf1fa8e94b00971f0cde587532ce26cf9b9cf32e49f191d670` | `dfcfc48feec5aedf1fa8e94b00971f0cde587532ce26cf9b9cf32e49f191d670` |

All five unchanged module objects match byte-for-byte. Both changed target objects differ. Target CPU timings were 2.21/2.21 s and 2.58/2.56 s for baseline/final respectively; each is a single shared-load observation, not a benchmark. Eight probes pin the seven phase objects; of 297 common declaration names, 293 printed type/axiom reports match and four generated reports change. Eighteen further generated public proof names disappear, with no added declarations. Sampled default simp and instance registrations match. These checks do not show proof-body equality or equality of all persistent extensions.

The four changed names are `AnnotatedRenameLocal.localCheck_correct._proof_4`, `_proof_5` and the corresponding two under `AnnotatedBoundLocal`. The removed names are `_proof_6` through `_proof_14` under each target. A tracked Lean/Python search and a scan of all 15 nonignored untracked Lean/Python files found no references to these affected names. Ignored files and the umbrella and downstream modules beyond the tested chain were not checked.

Three external direct project inputs match successful source-current producer rows:

- `AnnotatedRenameArithmetic`: object `bf29cdd77c792aceaeb7b3f13eb1d9cdf559cd5c9450c65057c242828d37b277`, source `0ece88c11fabd2326385963c9b782d76f91ec61ac6a31f839042f855ec6e34e0`; `/tmp/annotated-bound-witness/common2-records.json`.
- `NatIterate`: object `a2b3584a30113ae1887a0a67198cc6f51f809c98f3acd0c26f5e6ab3ba48e2ed`, source `c52148b71e86cc8f8713889f92bc321160292cc9ab1b6237ae417fc8f847fb2a`; `/tmp/annotated-bound-witness/common-prior-records.json`.
- `AnnotatedClosure`: object `cc1d25d027b1aa30483dbb170cde4c8d3ed277c9d969dcba0a273eecfbe37205`, source `b57ceb87516be3ff3a2c715ddf1fecd190031010d93512ca7b5fdaeb0189b641`; `/tmp/annotated-bound-witness/common2-records.json`.

Later final-build input source paths sample the workspace baseline before adoption; phase-specific target object hashes are separately tied to their final snapshots by target build records. The wider project, Foundation and Mathlib transitive closure was cached; no full current-source build is claimed. No raw logs or compiled objects are included here.

Transient external evidence and SHA-256 hashes (full validation requires these files and compiled dependencies):

- `/dev/shm/annotated-cases-93/baseline-records.json`: `4bf2d9d1cf8c3cc1f555461e24d5f4d018af633c361bf2671f10d05c7d05d668`.
- `/dev/shm/annotated-cases-93/final-records.json`: `7540b24407b81e936253fd20c00841fa9a9ae6c742e1afa8e47b8eb9ed73f344`.
- `/dev/shm/annotated-cases-93/probe-records.json`: `7ec762c004caedd6852c5caf77ebf9bb8c8faacb3d7fe4166ae1d6ff79d86d6b`.
- `/dev/shm/annotated-cases-93/README.txt`: `721e068c5cd6d9eaee990d89be80754b2ab67d8188a2917f77af0039671c4965`.
- `/dev/shm/annotated-cases-93/build.py`: `9cec5452ba46f7b98e31e0720db2274366f22b72ff601cc67602f4ae2bb7ccbe`.
- `/dev/shm/annotated-cases-93/probe.py`: `f32166b9bd9619c58defcacfe9c21edf3294d11a0349d92b63e6b5d07df564ee`.
- `/dev/shm/annotated-cases-93/audit.py`: `1e89b5343243544c57cc9d04d0f443b7befdc49d990c473f11bc84d159301930`.
- `/dev/shm/annotated-cases-93/audit.log`: `ab80b37e2a97e1fb8e0a17f7b01a732f3f014339cfbbb238c5bf553abb3a6c7a`.
- `/tmp/annotated-bound-witness/common2-records.json`: `126000b7411fd5e5b3422d685e719291ed1fa608264ad48aab020bd01ca257c5`.
- `/tmp/annotated-bound-witness/common-prior-records.json`: `5e0c3bd5fc248da7501aa711fdd8319a26fe7a8e91ff88d6fa0d210b5e5fdf78`.
- `/tmp/annotated-cases-93-peer-review.txt`: `a0d6d3eddae4fb0ec32c2e74e279c8edeb8a3b4b0d9699b423244ff45c1bfe47`.
- `/tmp/annotated-cases-93-peer-audit.py`: `67657c4088d0f9c2ee426264fecf910f409212310ddced00aafe3a955ac65441`.
- `/tmp/annotated-cases-93-peer-audit.log`: `eb4bb7d28432e2d3fafb0dc64309b62e5f4e2f38a1881a8aed1c5ad22414c6c8`.
- `/dev/shm/annotated-cases-93/baseline-names.log`: `acb431133f13b5156dedf2977b2f099ac4f1eab61b74b46f5ff884ce0ba9d95e`.
- `/dev/shm/annotated-cases-93/baseline-interfaces.log`: `401495fba862bca8f1e1ab346a942cc814611d572236c939463b243bf94b6036`.
- `/dev/shm/annotated-cases-93/baseline-simp.log`: `f04f35e8bcc4451c86266e0d8affb6bc8b4661e93f42b3fb9bc5fdd28e85eb61`.
- `/dev/shm/annotated-cases-93/baseline-instances.log`: `b958f5d177ef1751ebe64e01e930e5146ea6f41b6d18be4877f0fad9dbac1a0e`.
- `/dev/shm/annotated-cases-93/final-names.log`: `02b5c5af0129914e75753ff3fff5c5ac6f059952df4265756e3a903d58c003a1`.
- `/dev/shm/annotated-cases-93/final-interfaces.log`: `712860de0abc8160158d6f00fe22adf2bdf3b8e22eec95da88b216ac2a2bc575`.
- `/dev/shm/annotated-cases-93/final-simp.log`: `f04f35e8bcc4451c86266e0d8affb6bc8b4661e93f42b3fb9bc5fdd28e85eb61`.
- `/dev/shm/annotated-cases-93/final-instances.log`: `b958f5d177ef1751ebe64e01e930e5146ea6f41b6d18be4877f0fad9dbac1a0e`.

The independent review checked both commit snapshots, all 14 builds and first-path input hashes, seven-object probe associations, generated-name changes, reference searches and all three producer links. External paths are temporary and may later be unavailable.
