# Shared stronger Pell coordinate bound: validation

Source commit `7388945528d5d666d0f73ac2ecda333082c5c885`, parent `43df52d30d9f800034ea4c0f9d9be133ae787680`. The change extracts the duplicated `(b+1)*ycoord t b < xcoord t b` argument into the ordinary public theorem `ArithmeticPellPowerRecovery.x_gt`, reuses it in `y_lower`, and retains `ArithmeticOuterSeed.x_gt` as a wrapper. It removes two net lines without changing imports, assumptions or existing theorem statements. OuterSeed’s replaced argument came from Claude-coauthored commit `5fcd5632b3b`.

Both changed target source hashes match the parent/commit and tested baseline/final snapshots:

- `ArithmeticPellPowerRecovery.lean`: parent `dd9a12a8ff1811d974e0df2e5a98d78d702041a6a0e779bdfd2425375f818a7b`; commit `d242b25c32e03ff62a474835380d3b77f91ac1c0ac6e9415670a249bd64d32e2`.
- `ArithmeticOuterSeed.lean`: parent `b4b52261c47dd58fa3cf49a2ca79cee73c5e5013cc3cc4aa1ad340bcfe24b15f`; commit `78db14630fd6f01ef36f227ab4681e620624b07130b20c284e950153cd0011a7`.

All paired source-ordered target and five tracked direct-client builds passed in both initial and refreshed lanes. All seven refreshed output objects reproduce their corresponding initial-lane object. Three client objects match across phases; HalfBinomialSandwich and ConstructionBoundPell differ. Target and production-client logs are empty; both checks logs have identical expected `#print axioms` output with no warnings.

| Module | Baseline object SHA-256 | Final object SHA-256 |
|---|---|---|
| `ArithmeticPellPowerRecovery` | `5fd246d87260fa5467f39833cb91c8bebd2da6921304cfe4ca5a4657887d9e92` | `bf44666e140c4863ccff083975d8a85ce05c949689edc7c80e6415fb5c0b4644` |
| `ArithmeticPellPowerRecoveryChecks` | `a547df0df23bea532566c31ef528e6f9ba5764d99f01fadddb08a532e9469248` | `a547df0df23bea532566c31ef528e6f9ba5764d99f01fadddb08a532e9469248` |
| `ArithmeticHalfBinomialSandwich` | `e660053c5c3297012120ea8bab1e0dfec45c5fb0568ef654bbeb59f0481aaeb3` | `61db8eb1a1f287bbe58c3e72eb05d4fb3f810dff6361892cf044364b856e69c0` |
| `ArithmeticCarrierRadix2011` | `5d49d2dc9af2bbd3b694b035d6cdd408755ad94835fc498241c3bacf71a1e119` | `5d49d2dc9af2bbd3b694b035d6cdd408755ad94835fc498241c3bacf71a1e119` |
| `ArithmeticOuterSeed` | `1495b7c778124491773fd3dd19a4a1c25f29addc9f1ecca6984b7081cbacb46a` | `7cfb8a4d7c2cac0d8188fed5792585854ac68e1987928943486d68c86f3dc2c8` |
| `ArithmeticConstructionBoundPell` | `95d95b360bb0aa99926976882e0a659c629e293b1879d71ba9abb3894a57fe1f` | `1980d51eaadd5d22d1c81217ae25342b5b183df4c0d65575324839587be3cb6a` |
| `ArithmeticConstructionAssembly` | `e7f69999cd0ced816ece92c68ae5ffe60052e3c4802a464c946eee29053d3e71` | `e7f69999cd0ced816ece92c68ae5ffe60052e3c4802a464c946eee29053d3e71` |

Eight refreshed probes pin the seven built objects and seven provider objects per phase. All 120 common namespace declaration/type/axiom reports and sampled simp and instance registrations match; one new public theorem is added. These reports do not establish proof-body equality or equality of every persistent extension.

The following twelve external direct project inputs and additionally pinned HalfIndex object match successful source-current producer receipts. Parent source hashes are computed from git, not inferred from object bytes.

| Provider | Parent source SHA-256 | Pinned object SHA-256 | Producer receipt |
|---|---|---|---|
| `ArithmeticPellFirstIndex` | `5d0c42fb3e4dd68cd527f634b911ce9bcfa4a1722f0f6d28147203338dd977d3` | `24290ef5a4d3a3979a2c107320694d9cbbd1853655ca222a73750d4b5b181b4f` | `/dev/shm/firstindex-bound/final-refresh-records.json` |
| `ArithmeticPow` | `d7f033c291d70c5078eacd33c5ce25334f0d64b1bcc8be66e449e88a5b1d7e00` | `a46405c9e2a29f37da4c6e0ff917d17793da86e9c669602de2fe40b0b55dcf23` | `/tmp/pow-perturbation/final-records.json` |
| `ArithmeticCarrierSoundness2011` | `60a28e45d4f0c1776bd7f72cd24197c1c35e1f45abfc9f71f2fefd610cc72c66` | `a9b3588787c4ecd29e1d7a16a29d39d8174a48268f4202ba104185b5c4247070` | `/dev/shm/firstindex-bound/final-refresh-records.json` |
| `ArithmeticRadixAlignment` | `e0ef467294c6223e4cf0dc986b4943c495edd166fb9f2c956360c84f7c6381b4` | `212a7ec4ccb23469e596e66cb08690a3395486c6a4562ca5c2488b6424d1c8fa` | `/tmp/radix-positivity/final-records.json` |
| `ArithmeticHalfBinomial` | `35e749c1e5757314d772a03308d84d3a322a61ce93e4cd5c3293b659f2af8b00` | `5213cd5dbfaefcab5f47a14d1e0fe4cb40ec522be4e37e1f05af92f043ea507d` | `/tmp/binom-expansion-zero/final-records.json` |
| `ArithmeticPellAuxiliarySeed` | `f3769f93fe14b8ad50310050e8dbf9b7fa4347adda34af63eeee1abe470fd2c2` | `77a7611beed37708c840269caf2d7f042fd3c9ad2a8aaa32d98fafd6df044743` | `/dev/shm/pell-half-p-pos/final-records.json` |
| `ArithmeticTilingWord` | `b412f70d7089bd9387b00cfa6a5d82b75baaf3cf9d665d85ce9f1e8b8e64c049` | `db92ef94779be73a6bc6b79dde7edfadfec9958a6a0c36c72011a55bd212ce31` | `/tmp/rowrel-sharing/alternate-records.json` |
| `ArithmeticPackingCells` | `587aba5c1fdc98187f40301e613d3594c5b579dd5da6c070bc73651bc92e8174` | `0ba3df188c1fae546e103aee68f47e96deda4c4a1782e33da6bd1c6a932b0f1a` | `/dev/shm/claude-transport-sharing/assembly-phase-records.json` |
| `ArithmeticRankForcing2011` | `5dc4f4170b0d2e0202dade59dd2da97e511d5869ee5b1db2e624367b69a8394d` | `6f662b989ef254022389ba70e4bcecfadced9b72b99e26533891e71f4efbb7b0` | `/tmp/four-positive-wrappers/refreshed-final-records.json` |
| `ArithmeticController` | `ad3dc1fe546f22f92134860b2ec0bf94a0983a163c2dd2d166639a34ca1e79d2` | `9d7d5436e5e98c3d025254e27714ae0f1f532a037ee5844f05a4a6b373681126` | `/tmp/construction-share/bound-refresh-records.json` |
| `ArithmeticConstructionUnit` | `12b2d20c5aeb22bca72c7caa02e8fcaf28d3eff7e1559240ec4cdf62c37e297e` | `3e3f5908d210bd4ade3b9c4905f1cec32c43c44758ed24fa9c67ac48f093666e` | `/tmp/variation-tail-sharing/refreshed-common-records.json` |
| `ArithmeticConstructionVariation` | `fd64bbaaa59016ac501ed3d1e53124f0f9163fc51767cbf1428dd95dc78c2672` | `1d5398ef9465346996d318960a4d4ad41af6111059e60cd58cfdfd32c945b293` | `/tmp/variation-tail-sharing/refreshed2-final-records.json` |
| `ArithmeticPellHalfIndex` | `9a284bab88a2553569a1c68485ded379b7f5c21a3842c15ab40a1985f4449edd` | `5afaaea0b2b8a9adafd5e37c9799d387e56b1c9a07fd6e5f8f9bad8ef16ecc02` | `/dev/shm/pell-half-p-pos/final-records.json` |

The initial lane had historical objects for HalfBinomial, RadixAlignment, RankForcing and ConstructionVariation; the refreshed lane uses the source-matched objects listed above. The initial FirstIndex *workspace source sample* was historical while its imported object already matched the subsequently committed candidate; the refreshed sample matches that object’s producer. For each changed target, later final-phase client input source paths sample the baseline workspace before adoption; phase target build receipts link the actual objects to final snapshots. Other project, Foundation and Mathlib transitive dependencies remain cached; no complete source-current closure is claimed. Compiled objects and raw logs are excluded from this note.

Temporary external evidence, which may later be unavailable, is identified by path and SHA-256:

- `/dev/shm/pell-x-gt-share3/README.txt`: `3c7e855122f414fe3dbdfc227ca9724d1db323aa7aa408a5b2fc37a6fea4b458`.
- `/dev/shm/pell-x-gt-share3/build.py`: `51fd2263b3c24d467f948a7707e81179323ac2a8d246a607b02c630c9186630f`.
- `/dev/shm/pell-x-gt-share3/baseline-records.json`: `f34c7e802f1d3b8e378b242862db1b8e5b50b56c17bb7b6441e5e21184795f2a`.
- `/dev/shm/pell-x-gt-share3/final-records.json`: `ca0f78e5d854533f1280a2023bc1ca5c3e08166e7054d1d9165b03c02e2bec18`.
- `/dev/shm/pell-x-gt-share3/probe.py`: `9b12d172d67094bef5372cfb47853e18d7da2ce457a56425f5b3455b853dc446`.
- `/dev/shm/pell-x-gt-share3/probe-records.json`: `103c99a0dbd6a241aba21abdbae61d65e78f7c1df26340b4ac5220f618cf2b98`.
- `/dev/shm/pell-x-gt-share2/baseline-records.json`: `a98ba1f9e621ed4f468059cd3fc747dc7db8552f64ee59fa28b75fa91d3efa6f`.
- `/dev/shm/pell-x-gt-share2/final-records.json`: `4b9f63d4e4fca8e735a1d74dbedc1f6595a51c288b2eb6b6adff2ee0c88a8b4c`.
- `/tmp/pell-x-gt-share3-peer-review.txt`: `e7c7d33cfc6a10eeb0b20003a9a09d8ef439456fdffae364b728585ea8c65ac5`.
- `/tmp/pell-x-gt-share3-peer-audit.py`: `fc447c6b91af9a27c82a2515c7e4364d35a88cb74a9a94cf7b5a2d5a197cc280`.
- `/tmp/pell-x-gt-share3-peer-audit.log`: `318306c40d297ac982440ec942a041009e386f408c741d6cb03095486ba27e4c`.
- `/dev/shm/firstindex-bound/final-refresh-records.json`: `d4657ba153c11c7f631b4fb69c9744fc804a2e69105186bf62a33698ea7cf7ba`.
- `/tmp/pow-perturbation/final-records.json`: `1412171380c5eb24bb10d284aaff5d237893c7df4ceb877eddac3d7d458fc140`.
- `/tmp/radix-positivity/final-records.json`: `eb68266ab3da1636cccdbc9b2d94ce6044cf3abe637d56bcea7f03461eaea30a`.
- `/tmp/binom-expansion-zero/final-records.json`: `3f038dc7033835b5c9cad4ccd3fd95939e6de369545da2bbdada6f61db158be6`.
- `/dev/shm/pell-half-p-pos/final-records.json`: `49a7d13e81ad102109d607eb2e2741f0bfb3834c179286828f6405fa2922e28e`.
- `/tmp/rowrel-sharing/alternate-records.json`: `489e3f3962b15ae9a904aa878ed982b6f6e91a4063a193992f84986ab8a98c0f`.
- `/dev/shm/claude-transport-sharing/assembly-phase-records.json`: `239d3c5bf6f174413a89534c249e79f536e51764205617dab03adb134b88c745`.
- `/tmp/four-positive-wrappers/refreshed-final-records.json`: `84e3b7e2c3cd762f3c6096b5badbc584bcb4af9092cf49c16c33160582341c2c`.
- `/tmp/construction-share/bound-refresh-records.json`: `cbfd3d03e804f7893827e48560bf30baa886676b059aff126c2cef9404398150`.
- `/tmp/variation-tail-sharing/refreshed-common-records.json`: `a5ed04614c1afe0672fad225f73e3e87b4ba7b7e26639229e2ad8d8bdefad208`.
- `/tmp/variation-tail-sharing/refreshed2-final-records.json`: `33cb5114083d883b00c9ea577571fda514f91e2a5a0b4a77d8281200a0cdc6ec`.
- `/dev/shm/pell-x-gt-share3/baseline-names.log`: `e3dc14297907492126fe286484ff4f400abf051eac67677171d1670f98669684`.
- `/dev/shm/pell-x-gt-share3/baseline-interfaces.log`: `3c76c105cf35bf5f6e83af239c287d6db5ae0341813950646e54969d7bd48a88`.
- `/dev/shm/pell-x-gt-share3/baseline-simp.log`: `4355181dc8ca50bc80fe2675165f75d40c4fb09208e01f6fb8668323d60d52f2`.
- `/dev/shm/pell-x-gt-share3/baseline-instances.log`: `42d0e1f09ff74e0973c905f9ab5860b46d99bd1c5957ad23430be97e79f84c4c`.
- `/dev/shm/pell-x-gt-share3/final-names.log`: `d1dff349f2e9075a388cb491084c93665f424fdc8862d233fcbde7006ef19125`.
- `/dev/shm/pell-x-gt-share3/final-interfaces.log`: `7fd42c13cd41eefb7be188b3b5a13e64161641527da3e320603939a923f098bb`.
- `/dev/shm/pell-x-gt-share3/final-simp.log`: `4355181dc8ca50bc80fe2675165f75d40c4fb09208e01f6fb8668323d60d52f2`.
- `/dev/shm/pell-x-gt-share3/final-instances.log`: `42d0e1f09ff74e0973c905f9ab5860b46d99bd1c5957ad23430be97e79f84c4c`.
- `/dev/shm/pell-x-gt-share3/baseline-ArithmeticPellPowerRecovery.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/baseline-ArithmeticPellPowerRecoveryChecks.log`: `682690055e3f5aa57af685595c32ec7986955729e60b260705074bb0503bcb6b`.
- `/dev/shm/pell-x-gt-share3/baseline-ArithmeticHalfBinomialSandwich.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/baseline-ArithmeticCarrierRadix2011.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/baseline-ArithmeticOuterSeed.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/baseline-ArithmeticConstructionBoundPell.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/baseline-ArithmeticConstructionAssembly.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/final-ArithmeticPellPowerRecovery.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/final-ArithmeticPellPowerRecoveryChecks.log`: `682690055e3f5aa57af685595c32ec7986955729e60b260705074bb0503bcb6b`.
- `/dev/shm/pell-x-gt-share3/final-ArithmeticHalfBinomialSandwich.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/final-ArithmeticCarrierRadix2011.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/final-ArithmeticOuterSeed.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/final-ArithmeticConstructionBoundPell.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/dev/shm/pell-x-gt-share3/final-ArithmeticConstructionAssembly.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

The independent review verified 28 initial/refreshed builds, exact first-path associations, warnings, 14-object-pinned probes, provider receipts and postcommit snapshots. Full replay requires the external files, compiled dependencies and the recorded Lean environment.
