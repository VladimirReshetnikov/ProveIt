# Pell ordinate growth sharing: validation

Source commit `24f81fcabcf222992dca8db5201e06e96a31a48d`, parent `726bb505a9d4eede15d6fe3bd4561a9f0535b95f`. The three baseline and final source snapshots match the parent and commit byte-for-byte, respectively. The change shares Congruences' ordinate-growth argument in ArithmeticPellRecurrence and retains existing Congruences and StrongDivisibility public statements as wrappers. It removes their duplicated proofs (23 insertions and 34 deletions) without changing imports. The original proofs arose in commits `6809609c61b`, `20eb14ccb97` and `5b38027dcc0`, credited to Vladimir Reshetnikov.

| Source | Parent SHA-256 | Commit SHA-256 |
| --- | --- | --- |
| `ArithmeticPellRecurrence` | `b2c9d9dc41be16aa503540851c3c9752e2c475a947666f79eb9ea539aebe14af` | `5c0f23fd82a0f3de3e36d2854efe0f068431c9b1382be08adbec92297874d6e6` |
| `ArithmeticPellCongruences` | `afdb16050ac37d0c213d7124f1821ea4ef8aa2137253a120fb1d517781e1b157` | `55f33f956f04fee933127a7141f2a5668ba573fc298a9dd0b83aa820d1b6011b` |
| `ArithmeticPellStrongDivisibility` | `c20fc77d6483ea342b53053e966022cc25ab27d786206ff52f733adc9d25429b` | `5ec15e3c0416dfe9fe5d43193c685fb94146315870a7475623639e45a9cc5219` |

Both 12-module lanes passed. They include all eight tracked direct clients of the changed modules, one of which is itself changed, and the KnownUnit and CommonUnit intermediate providers. A tracked import graph traversal found 51 transitive Recurrence consumers, including two changed modules and 49 unchanged; not all transitive consumers were rebuilt. All paired build diagnostics match after phase-path normalization and contain no warnings.

| Module | Baseline object SHA-256 | Final object SHA-256 |
| --- | --- | --- |
| `ArithmeticPellRecurrence` | `0b58739aea61f13a516c86ccab1dad0d39021fda50bf84ff91ab3f5cd557d5f0` | `5cf46612a8c5223ea6f881ad0fc4b3e74a482a27cc6043b96e3737591a4c3386` |
| `ArithmeticPellRecurrenceChecks` | `527e705fca517a51ac379150cbb7f7fd70f771b8f02ed0c8aba70dbd2520eb89` | `527e705fca517a51ac379150cbb7f7fd70f771b8f02ed0c8aba70dbd2520eb89` |
| `ArithmeticPellClassification` | `c70752648f0ae5bc4a186364c2de2e4beb20eacf5c8611b6f66931c7553f15d8` | `814543fb77cb5246b4f072ba6881118bb99585bf00f5d22e9e406952bd3d79e6` |
| `ArithmeticPellStrongDivisibility` | `1ffd2773a1455819b3480597da20e8dbc16ccaf4f17c38e5db2b17bc34aafd0d` | `43866830d2891df7f183a167cde451b66de33e89285f2ac4e2300ce9935d05d3` |
| `ArithmeticPellStrongDivisibilityChecks` | `fba63022e2f6451e6788e1ce9cf7026e0313be33f9aa8cf5505ba8319a07f97c` | `fba63022e2f6451e6788e1ce9cf7026e0313be33f9aa8cf5505ba8319a07f97c` |
| `ArithmeticPellCongruences` | `1e91f92544d245ec86a0d3399470b2bf821c46e79b29d815ff103663de634722` | `0276d7cc796754c3439ff23ee6500ea5388da1c84b89d586481a7acda2026c81` |
| `ArithmeticPellCongruencesChecks` | `d41502e1a740c2f21a5604b99e8b96b3704708add8063ad83720badc42579850` | `d41502e1a740c2f21a5604b99e8b96b3704708add8063ad83720badc42579850` |
| `ArithmeticPellKnownUnit` | `029b153d3ad6f3289fe6f05e8029a10c76e8d07a3cdde0c089b99894f1f78dbc` | `a737c9c9f4063c69a9cc191580151e46012e816c355e1ff7ccccaf30742bf3d7` |
| `ArithmeticPellCommonUnit` | `5c2708c81cf38575b8d6ab0674a6961fd91ecc96c6738a6075b056a9bb033275` | `c157826d80136fa1d108256ee740967898b6539f1bb64d6e35bb8c5f2daae217` |
| `ArithmeticPellFirstNorm` | `bab7ce73467466a0032aac354a802dfcca264a250531ff702df779e39ff473f9` | `4ccee60fa09bb585de8e26c8982296d4c65d168c634124b1faa217e37a13ad55` |
| `ArithmeticPellPeriodicity` | `af38b702578ce3523e47ac5a4c73b3294bc287c53a5f0dd0aff064f9da7e5892` | `adda9489a2a9076319b86fdaa63a827b301d47dc5377af47e2e3d1c66542678b` |
| `ArithmeticPellIntegralSolution` | `aef539992eae3308695ab6294c033a33616708cab9356ec00952a8af67cf4d8f` | `99cb3ee7e70bd31320c675534ce2a61bc27e47803b0991531e44d4516acc81c3` |

The three Checks objects match. Six other unchanged client objects differ; their exact cause is undetermined. The imported object graph changed. Four probes per phase imported the 12 pinned phase objects and enumerated declarations, types/axioms, and global simp and instance registrations. Of 149 baseline and 150 final declarations, the 148 common declarations have matching type and axiom reports; `ArithmeticPellRecurrence.ordinate_add_ge` and `ordinate_strictMono` were added and the private StrongDivisibility `y_add_ge` was removed. All 28,977 simp and 13,169 instance entries match byte-for-byte. This does not establish equality of proof bodies, every persistent extension, or downstream name resolution. A tracked/nonignored untracked Lean/Python search of 90,633 files found no reference to the removed helper's full private name; ignored files and external consumers were outside scope.

The initial lanes consumed a stale ArithmeticGcdNormalization object, built from source `8c358248bb5ce148ad412e4901a726829c69a037bb424d88816a62b26cbeb314` instead of the current source. Its provider was rebuilt from current source SHA-256 `bd203be2a1cf32efa43c3809a50fdef104963b3dd9b430b59417c4257bc6d456`, producing object `c2ba374dd946d5aee4df1d91cf60b97935180915c43d00ba3b2c2726b1e81da6`. Both phases then replayed StrongDivisibility, StrongDivisibilityChecks, CommonUnit and IntegralSolution. The corrected records pin the direct first paths, object and source hashes; the initial stale-provider records remain available separately. The provider's Foundation and Mathlib inputs and the larger transitive closure remain cached; a source-current rebuild of the entire closure is not claimed.

Independent review `/tmp/pell-growth-peer-143-review.txt` checked the proof, paired builds, first paths and phase-output associations, probe pins, reports, tracked graph, the private-name scan, and postcommit source snapshots. It found no defect. The compact note does not include raw logs or objects, and the transient files below may later be unavailable. `compare.py` checked workspace baseline sources before adoption; that check is expected to fail against the postcommit checkout, where the three files now match the final snapshots.

External evidence and SHA-256:

- `/dev/shm/pell-growth-sharing-141/baseline-records.json`: `4981187fb38504c144c79a6e2c9902a2782b84a731d43a7cd8efdc5eac7abae6`.
- `/dev/shm/pell-growth-sharing-141/final-records.json`: `469e166c968d1d7e4f77d63ecd13be2b3d77f6f134fafa98c3831d24423c28a7`.
- `/dev/shm/pell-growth-sharing-141/baseline-cached-provider-records.json`: `76e4b19bc1db9655dce098b75e1d8614fa7f7d1c5dd77d7c715e67498a57e584`.
- `/dev/shm/pell-growth-sharing-141/final-cached-provider-records.json`: `b0dfa2686e2a9cbb76d3f95e2fe54bb8dc7856288244d78432f0f8fd6c533c52`.
- `/dev/shm/pell-growth-sharing-141/baseline-probe-records.json`: `65458ea82554f45773ff85c21aafda351fec3d59003f5593c7d1b04fa1af223f`.
- `/dev/shm/pell-growth-sharing-141/final-probe-records.json`: `574a8c7ef27849596b3078662f39422038ba899b53bac86ae6031f4eb29ffd84`.
- `/dev/shm/pell-growth-sharing-141/refresh-record.json`: `ea41510e3d8a62c009899f3ec7d6378f19b0a1176f44b34e311fb191bfca5408`.
- `/dev/shm/pell-growth-sharing-141/README.txt`: `b375fcef5a0b8cc579f0d93e7044512fda2d7e3dee4623ea316d25a473bb39d8`.
- `/dev/shm/pell-growth-sharing-141/build.py`: `7a2f59341b01db1d9dcc4ee28e8c034d8c5a7420ca6f3e71e8400aad71b55360`.
- `/dev/shm/pell-growth-sharing-141/refresh.py`: `1f60c8e02aaf3b0e5aab1818e2d144f066229733f2926cf8820698b0583e6100`.
- `/dev/shm/pell-growth-sharing-141/replay.py`: `d470b1810bfd9a7ee05772b194cf80b1ba540192ba0aa1c674482256f5f45dda`.
- `/dev/shm/pell-growth-sharing-141/probe.py`: `53dac3df24f33f855832b31d204fd5001a4d2ac69117dddaac3fd47d94a0512d`.
- `/dev/shm/pell-growth-sharing-141/compare.py`: `b95ce101bab9b9241f94e9f9923756ad883113e7ff1498a0f54033c46f51cbc2`.
- `/dev/shm/pell-growth-sharing-141/compare.log`: `b81e08b83e39a8a0a59fc759ab6462d36ed6cde3a86e0f4df4621b15347e1c91`.
- `/dev/shm/pell-growth-sharing-141/reference-scan.py`: `dbe704080869f4e8bc4dbb72a0ce60c56bd05785cf187d89f65bdbbfe7f2d44b`.
- `/dev/shm/pell-growth-sharing-141/reference-scan.log`: `f93d95de5251686199a6209fe39b78ad956fba5d8b51d47353323bde7e0bfca9`.
- `/tmp/pell-growth-peer-143-review.txt`: `c2c5bd4152aadf624e06336787ba615611e17f78863842b56424f68d73696fb6`.
- `/tmp/pell-growth-peer-143.py`: `3b4494919e45cd23fa61debddbf7b41ba34d9ff94c56f653d7c8c5ed99d57737`.
