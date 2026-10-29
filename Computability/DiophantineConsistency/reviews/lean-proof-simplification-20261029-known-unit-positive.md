# Least-unit abscissa positivity validation

Source commit `1d38d9fc0704e2c199a39f1e0381bb657a5b82f0`; parent `8f153edc15ccc37f1b1f54c95888645b7c9f7404`. The original proof is attributed to `eecfc7f4e29`; no Claude coauthor is asserted. The simplification derives positivity of x from its positive norm product using `pos_of_mul_pos_left` instead of a zero contradiction, removing three lines without changing statements or assumptions.

`ArithmeticPellKnownUnit.lean` source SHA-256: parent `84908d9195b688f1e1c0b121b412c47706cebb94ca8fe722a6c29bd02bf1ec92`; commit `529a598f08f9bdc4dd3f7ded48948699296a9328cd5b4b892a7aaa014bd8b980`. The independent postcommit check confirms both match their tested source snapshots.

Paired refreshed builds of the target and three direct clients passed against the committed recurrence provider chain. The target objects differ; all three client objects are byte-identical between phases:

- `ArithmeticPellKnownUnit`: baseline object `cdbf782e3df25d0c4a0a57d80c3580cff8408d5a5c0c0e99b3b0019c278453cb`; final `029b153d3ad6f3289fe6f05e8029a10c76e8d07a3cdde0c089b99894f1f78dbc`.
- `ArithmeticPellKnownUnitChecks`: baseline object `c452f7a034e15e5573c19ddce0cd21ff3936c5fe858ddbd510ce99075a157482`; final `c452f7a034e15e5573c19ddce0cd21ff3936c5fe858ddbd510ce99075a157482`.
- `ArithmeticPellFirstNorm`: baseline object `98944850cfe61fa88a2a6f1271edd15fe0b5dcb1e0619862a7c7b7a756e2ba65`; final `98944850cfe61fa88a2a6f1271edd15fe0b5dcb1e0619862a7c7b7a756e2ba65`.
- `ArithmeticPellCommonUnit`: baseline object `5c2708c81cf38575b8d6ab0674a6961fd91ecc96c6738a6075b056a9bb033275`; final `5c2708c81cf38575b8d6ab0674a6961fd91ecc96c6738a6075b056a9bb033275`.

Target, FirstNorm and CommonUnit logs are empty; both Checks logs contain the same expected `#print axioms` output without warnings. The refreshed target, FirstNorm and CommonUnit objects differ from the earlier validation lane, while Checks matches. Eight probes pin the target, FirstNorm and CommonUnit objects plus Recurrence, Classification and Congruences providers. All 29 printed namespace declaration names/types/axioms and sampled global simp/instance registrations match within the refreshed pair and match the earlier baseline reports. These comparisons do not establish proof-body equality or equality of every persistent extension.

The following provider objects match successful current-source producer records:

- `ArithmeticPellRecurrence`: object `0b58739aea61f13a516c86ccab1dad0d39021fda50bf84ff91ab3f5cd557d5f0`; source `b2c9d9dc41be16aa503540851c3c9752e2c475a947666f79eb9ea539aebe14af`; `/dev/shm/shared-pell-recurrence/final-records.json`.
- `ArithmeticPellClassification`: object `c70752648f0ae5bc4a186364c2de2e4beb20eacf5c8611b6f66931c7553f15d8`; source `cc069bb389454028a91b2485615086c81f7e88d36d1da346d330ef56d7391198`; `/dev/shm/shared-pell-recurrence/final-records.json`.
- `ArithmeticPellCongruences`: object `1e91f92544d245ec86a0d3399470b2bf821c46e79b29d815ff103663de634722`; source `afdb16050ac37d0c213d7124f1821ea4ef8aa2137253a120fb1d517781e1b157`; `/dev/shm/shared-pell-recurrence/final-records.json`.
- `ArithmeticGcdNormalization`: object `c2ba374dd946d5aee4df1d91cf60b97935180915c43d00ba3b2c2726b1e81da6`; source `bd203be2a1cf32efa43c3809a50fdef104963b3dd9b430b59417c4257bc6d456`; `/tmp/gcd-product-positivity/final-records.json`.

The recorded shared-lane Classification object imports its final Recurrence object, and its Congruences object imports that Classification object. Each refreshed KnownUnit build also pins all three before and after. The final-phase clients sample the baseline workspace source path for KnownUnit; the final target build separately links their actual target object to the final phase source. Other project, Foundation and Mathlib transitive dependencies remain cached; no full source-current closure is claimed.

No raw logs or compiled objects are included. The following transient external files may not remain available:

- `/dev/shm/known-unit-x-positive-refresh/baseline-records.json`: SHA-256 `0e077da7601fe87c3833cb60735ea59b9f4f25ce993e6ab9906a0fd3cb6af71e`.
- `/dev/shm/known-unit-x-positive-refresh/final-records.json`: SHA-256 `2f3b06da18484d8d4a85768087d4aa89e5eeadff64570f6ba8b8331c79e64c1a`.
- `/dev/shm/known-unit-x-positive-refresh/probe-records.json`: SHA-256 `1e44ca24b9f0eaf671fa418f4b2d7122e75a5c5dc265819bf933a689b312326a`.
- `/dev/shm/known-unit-x-positive-refresh/audit.py`: SHA-256 `7c6725d5e9194a2bdeab70cc4a1ca4d37213e0ff2eba355e50640d6ec2f474aa`.
- `/dev/shm/known-unit-x-positive-refresh/audit.log`: SHA-256 `9c95e883597b9c3e3987209a4ef21f96afe2893a475eb36bbafc596047c6cd2c`.
- `/dev/shm/known-unit-x-positive-refresh/README.txt`: SHA-256 `27930b23edb25a49340adcb0a582ddee3f13f78b671613fa7699e0c2b517bac3`.
- `/dev/shm/shared-pell-recurrence/final-records.json`: SHA-256 `25f1a912a593a0ef8360a5c43c36f5de4d8f7a1e555101d27cd64745b555fbee`.
- `/tmp/gcd-product-positivity/final-records.json`: SHA-256 `d1bf4bae9291e2d871f9b2f03ec17bfe3471b424c628e36fa38b2b52699a92c9`.
- `/tmp/known-unit-x-positive-refresh-peer-review.txt`: SHA-256 `9c5cabaa300f3e3173ab058b623874c29d87da35f2bd1b607f55eb7b1832983c`.
- `/tmp/known-unit-x-positive-refresh-peer-audit.py`: SHA-256 `78add49a85f3044fc77f6bf6e203016c27a0a5a8f1965bb263531bb57fdee1b0`.
- `/tmp/known-unit-x-positive-refresh-peer-audit.log`: SHA-256 `10cac0f847d9d9801a535cd5ae3420a59a88c6600689c107aa4427e0e11e10cc`.

The independent review checked all eight builds, first-path source/object pins and provider edges, object-pinned probes and comparisons, client identity and the parent/commit snapshots. Full replay requires the transient evidence and excluded compiled dependencies.
