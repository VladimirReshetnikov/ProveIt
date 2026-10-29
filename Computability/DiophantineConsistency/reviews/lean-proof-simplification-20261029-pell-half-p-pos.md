# Pell half-index source index positivity: validation

Source commit `d2be49222c91d021f14dee4f4d64d5aa4899a8f4`, parent `44e63039900056303f3b11d7f8c87b65b6d7605a`. The changed `ArithmeticPellHalfIndex.lean` source SHA-256 is `6b9b17bafac0d909d68dec84f67dfe314059bf673e15ef2945bbfe8de93853ef` in the parent and `9a284bab88a2553569a1c68485ded379b7f5c21a3842c15ab40a1985f4449edd` in the commit; both match the tested snapshots. The change removes four net Lean lines by deriving positive index `p` from the positive ordinate and the zero recurrence, while preserving the theorem statement, assumptions, definitions and imports. The original proof came from `90e177c431c`; no Claude coauthor is asserted.

All paired source-ordered target and direct-client builds passed. The target objects differ; all three direct-client objects are byte-identical across phases. Target and production-client logs are empty; both checks logs contain identical expected `#print axioms` output with no warnings.

| Module | Baseline object SHA-256 | Final object SHA-256 |
|---|---|---|
| `ArithmeticPellHalfIndex` | `7f364e0050215da692cdd8d09b4f15cc656ecf4e6ff5303a7bfba732fe421d5d` | `5afaaea0b2b8a9adafd5e37c9799d387e56b1c9a07fd6e5f8f9bad8ef16ecc02` |
| `ArithmeticPellHalfIndexChecks` | `bbf47b3656dec1812190f63f6484a8bc89833ef141aaa2cf0ef15b3682353cbf` | `bbf47b3656dec1812190f63f6484a8bc89833ef141aaa2cf0ef15b3682353cbf` |
| `ArithmeticPellFirstIndex` | `994b90ca744768cfb199e3ee48d947f05f17692d18034b1a27d7e9f07dd84d4f` | `994b90ca744768cfb199e3ee48d947f05f17692d18034b1a27d7e9f07dd84d4f` |
| `ArithmeticPellAuxiliarySeed` | `77a7611beed37708c840269caf2d7f042fd3c9ad2a8aaa32d98fafd6df044743` | `77a7611beed37708c840269caf2d7f042fd3c9ad2a8aaa32d98fafd6df044743` |

Eight probes pin the exact target, FirstIndex and AuxiliarySeed objects and eight provider objects in each phase. The 53 combined namespace declaration names and printed types/axioms, 28,977 sampled simp entries and 13,170 sampled instance entries match byte-for-byte. This does not establish proof-body equality or equality of all persistent extensions.

IntegralSolution and IndexDivisibility were rebuilt from current source against current Recurrence, KnownUnit and CommonUnit. The ten following source/object associations match successful source-current producer receipts. Parent source hashes are computed from git, not inferred from object bytes.

| Provider | Parent source SHA-256 | Pinned object SHA-256 | Producer receipt |
|---|---|---|---|
| `ArithmeticPellRecurrence` | `b2c9d9dc41be16aa503540851c3c9752e2c475a947666f79eb9ea539aebe14af` | `0b58739aea61f13a516c86ccab1dad0d39021fda50bf84ff91ab3f5cd557d5f0` | `/dev/shm/shared-pell-recurrence/final-records.json` |
| `ArithmeticPellKnownUnit` | `529a598f08f9bdc4dd3f7ded48948699296a9328cd5b4b892a7aaa014bd8b980` | `029b153d3ad6f3289fe6f05e8029a10c76e8d07a3cdde0c089b99894f1f78dbc` | `/dev/shm/known-unit-x-positive-refresh/final-records.json` |
| `ArithmeticPellCommonUnit` | `85b2d661536f3353da857b9c9f9c3ca14f1e860dde7c71a25d7c151864b640ea` | `5c2708c81cf38575b8d6ab0674a6961fd91ecc96c6738a6075b056a9bb033275` | `/dev/shm/known-unit-x-positive-refresh/final-records.json` |
| `ArithmeticPellIntegralSolution` | `6f8f08e11cfdd1890507608187ab5a8ea7fb37c102653668aa91ad5ad1b830b5` | `aef539992eae3308695ab6294c033a33616708cab9356ec00952a8af67cf4d8f` | `/dev/shm/pell-half-p-pos/common-records.json` |
| `ArithmeticPellIndexDivisibility` | `fc0e2fc57734a6043a9f43b0877a805ff4b53f76d9e978d7088c9a02a79c5feb` | `b8dfc8d43a583d7c06f1dcb70b9a1d9697ec377943afbc9db878f9c6cafd5a35` | `/dev/shm/pell-half-p-pos/common-records.json` |
| `ArithmeticPellPeriodicity` | `6327f5f4ab6dcf4a2adec32f8fc080588844ea431e0ad58dddb0e4d9b9a3a213` | `af38b702578ce3523e47ac5a4c73b3294bc287c53a5f0dd0aff064f9da7e5892` | `/dev/shm/shared-pell-recurrence/final-records.json` |
| `ArithmeticPellResidueClasses` | `df4884c9c9cc4446163deb37aede62fea410d5d686d89de1e30aa58331bcbe5a` | `a5afe2834ee7419f9b5b7d6ac47a6886891d91a489cf771169b18843ed298867` | `/dev/shm/mod-nested-share/final-pell-records.json` |
| `ArithmeticModularCancellation` | `2f10842ad2446145da3a595b20fa0f85db6e9d6f95285609f07455a8ae885e8b` | `a638651a192ec2fda296d64eb50951b0fcd14b2764b083168509da15db55ec35` | `/dev/shm/mod-nested-share/final-records.json` |
| `ArithmeticPellFirstNorm` | `1a28867ced88fb1b56b872bf900052c3035a4a42502ea024b1f4a7ef5347b816` | `98944850cfe61fa88a2a6f1271edd15fe0b5dcb1e0619862a7c7b7a756e2ba65` | `/dev/shm/known-unit-x-positive-refresh/final-records.json` |
| `ArithmeticPellSquaredSeed` | `9e4cc08b5992b2074d2046ef7cb4d2854b0147cc66829897b7d6ac7c5f4d8ec7` | `05808ba096f9f3ec7fedd2b8b1561c0c2e5b6f7ff1b6faa2808765d891cf1034` | `/dev/shm/shared-pell-recurrence/final-records.json` |

Client input-source rows for HalfIndex sample the baseline workspace before adoption; the final target build separately links the actual client input object to the final source snapshot. The initial isolated attempt used an older ResidueClasses object and is not the validated paired lane. Other project, Foundation and Mathlib transitive dependencies remain cached. No complete source-current closure is claimed. Compiled objects and raw logs are excluded from this note.

Temporary external evidence, which may later be unavailable, is identified by path and SHA-256:

- `/dev/shm/pell-half-p-pos/README.txt`: `415e516c82313247b0e0e4727e5016f026a0cd1684756be719ba5bc7ad3708b1`.
- `/dev/shm/pell-half-p-pos/build-common.py`: `070745334cbcb89b9b11d719abdbb0c30986b88809d6af09b0e2cce0ace1d828`.
- `/dev/shm/pell-half-p-pos/common-records.json`: `f2a681e2715ae61b0d9f222faf9ac4f49e9bc85cb78116f306d8dbe2081e7a6a`.
- `/dev/shm/pell-half-p-pos/build.py`: `f130812f153ebd176db5c105183d76b73f33d560a6ebcaf6a4d6a95150da1efd`.
- `/dev/shm/pell-half-p-pos/baseline-records.json`: `d8b5733ce419892c605d70070e6644c7416a33231090b60b2f561b2451170e36`.
- `/dev/shm/pell-half-p-pos/final-records.json`: `49a7d13e81ad102109d607eb2e2741f0bfb3834c179286828f6405fa2922e28e`.
- `/dev/shm/pell-half-p-pos/probe.py`: `d13f3eac4b459d1b85272835ca3acb0abc58dccb6d58cc3e4193ce12326f344e`.
- `/dev/shm/pell-half-p-pos/baseline-probe-records.json`: `1001480d060045d700905f3c61feef6b18a65d75fcd7e6a6151251e55b90112f`.
- `/dev/shm/pell-half-p-pos/final-probe-records.json`: `bb8f9f51bc208d4b21a525ffa83c7410a2cebb2a45b905e347e5dc27b474aedc`.
- `/dev/shm/pell-half-p-pos/audit.py`: `6ea36935c66cc5612d80cd5a8d6e56da1aee6f709bdde2d9a00522df605a60e3`.
- `/dev/shm/pell-half-p-pos/audit.log`: `9f2af38025ccb717f61db4abfcc5835631b56a3e97b81f7b6d1b18447d0aa169`.
- `/tmp/pell-half-p-pos-peer-review.txt`: `d85910a895c93801d13c96fd0c5422d6276e88b3780ea8b4e0fee213a392afd6`.
- `/tmp/pell-half-p-pos-peer-audit.py`: `8a7a4ff78b08de927d0d8846a2c1ec5847449edc47ccd73bc594ac33dbbf3d71`.
- `/tmp/pell-half-p-pos-peer-audit.log`: `2e0f20097cc978b7c5e36dd5a9f0f6ee8e78267644b3371266f0b0ebeb683496`.
- `/dev/shm/shared-pell-recurrence/final-records.json`: `25f1a912a593a0ef8360a5c43c36f5de4d8f7a1e555101d27cd64745b555fbee`.
- `/dev/shm/known-unit-x-positive-refresh/final-records.json`: `2f3b06da18484d8d4a85768087d4aa89e5eeadff64570f6ba8b8331c79e64c1a`.
- `/dev/shm/mod-nested-share/final-pell-records.json`: `f23ea97a4a4930761fc28a4103cf091f825ec0701e4f916053d13fd314c0ec1b`.
- `/dev/shm/mod-nested-share/final-records.json`: `6c4dc0db5d49a43755a4e4141c23b0e80a5eb00309042f7ffcc616d446fa737d`.
- `/dev/shm/pell-half-p-pos/baseline-names.log`: `d662ce60963bd6fa141686b2abb9bb1bf095abe4953601435ffa8dd94641625c`.
- `/dev/shm/pell-half-p-pos/baseline-interfaces.log`: `e885c31c2ab4a0cc60019440f082d96d7446264781ee7fe7338e9875777ba9d6`.
- `/dev/shm/pell-half-p-pos/baseline-simp.log`: `1155a4269c860037b3b1a73a73fa0e86719a8ae5829b2c3c2cfa353b7dfe03b4`.
- `/dev/shm/pell-half-p-pos/baseline-instances.log`: `e28e1c1803e0859325238647862ce48f47eef5734ba6af240cf8bdcfa40c3326`.
- `/dev/shm/pell-half-p-pos/final-names.log`: `d662ce60963bd6fa141686b2abb9bb1bf095abe4953601435ffa8dd94641625c`.
- `/dev/shm/pell-half-p-pos/final-interfaces.log`: `e885c31c2ab4a0cc60019440f082d96d7446264781ee7fe7338e9875777ba9d6`.
- `/dev/shm/pell-half-p-pos/final-simp.log`: `1155a4269c860037b3b1a73a73fa0e86719a8ae5829b2c3c2cfa353b7dfe03b4`.
- `/dev/shm/pell-half-p-pos/final-instances.log`: `e28e1c1803e0859325238647862ce48f47eef5734ba6af240cf8bdcfa40c3326`.
- `/dev/shm/pell-half-p-pos/baseline-ArithmeticPellHalfIndex.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-half-p-pos/baseline-ArithmeticPellHalfIndexChecks.log`: `586b4dbf8a87cf8bba9e4d1a651cca5d3d079b9c1417e2af85cbfcbd2442edf0`.
- `/dev/shm/pell-half-p-pos/baseline-ArithmeticPellFirstIndex.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-half-p-pos/baseline-ArithmeticPellAuxiliarySeed.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-half-p-pos/final-ArithmeticPellHalfIndex.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-half-p-pos/final-ArithmeticPellHalfIndexChecks.log`: `586b4dbf8a87cf8bba9e4d1a651cca5d3d079b9c1417e2af85cbfcbd2442edf0`.
- `/dev/shm/pell-half-p-pos/final-ArithmeticPellFirstIndex.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-half-p-pos/final-ArithmeticPellAuxiliarySeed.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

The independent review verified all builds and first-path associations, 11-object-pinned probes, client identity, provider receipts, warnings and postcommit snapshots. Full replay requires the external files, compiled dependencies and the recorded Lean environment.
