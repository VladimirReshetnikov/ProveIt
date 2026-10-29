# Positive first-norm solution index: validation

Source commit `8ed12b630d90ce3d8ffef5afc8ad38b73d685ac0`, parent `a5ab1b3f45262a06944c1086bb6aecf638c0d44c`. Their target source SHA-256 hashes are `0a6c3ecfbf1a6aa62fecf168de0757760b2e8606754d4ad1974f26add46cf501` and `1a28867ced88fb1b56b872bf900052c3035a4a42502ea024b1f4a7ef5347b816`, respectively, matching tested final and baseline snapshots. The change uses the positive ordinate and zero-index recurrence to prove the index is nonzero, removing four net lines while preserving imports, definitions, assumptions and theorem statements. Original proof lines were introduced in `ad92d07c8a9`; no Claude attribution is asserted.

Paired source-ordered builds of `ArithmeticPellFirstNorm`, `ArithmeticPellFirstNormChecks` and `ArithmeticPellFirstIndex` passed. Both client objects match byte-for-byte across phases. Both checks logs contain identical expected `#print axioms` output; other build logs are empty. No warnings occurred.

| Module | Baseline object SHA-256 | Final object SHA-256 |
|---|---|---|
| `ArithmeticPellFirstNorm` | `98944850cfe61fa88a2a6f1271edd15fe0b5dcb1e0619862a7c7b7a756e2ba65` | `bab7ce73467466a0032aac354a802dfcca264a250531ff702df779e39ff473f9` |
| `ArithmeticPellFirstNormChecks` | `f7a6de3b6ad7c072b34fe992854628c11cd3dc413cbc164c9eb451f449a424f0` | `f7a6de3b6ad7c072b34fe992854628c11cd3dc413cbc164c9eb451f449a424f0` |
| `ArithmeticPellFirstIndex` | `ee0eda7f8414917b15fc6a479d9a03ec7fe36ba7768d4e809dd96f9f5b05017f` | `ee0eda7f8414917b15fc6a479d9a03ec7fe36ba7768d4e809dd96f9f5b05017f` |

Eight probes pin each phase target, KnownUnit, Congruences and HalfIndex objects. The 17 target namespace names, printed types/axioms (92 lines) and sampled simp/instance registrations (28,968/13,167 lines) match byte-for-byte. These checks do not establish proof-body equality or equality of all persistent extensions.

Direct source-matched project-provider associations are:

- `ArithmeticPellCongruences`: source `afdb16050ac37d0c213d7124f1821ea4ef8aa2137253a120fb1d517781e1b157`, object `1e91f92544d245ec86a0d3399470b2bf821c46e79b29d815ff103663de634722`, producer `/dev/shm/shared-pell-recurrence/final-records.json` (record SHA-256 `25f1a912a593a0ef8360a5c43c36f5de4d8f7a1e555101d27cd64745b555fbee`).
- `ArithmeticPellKnownUnit`: source `529a598f08f9bdc4dd3f7ded48948699296a9328cd5b4b892a7aaa014bd8b980`, object `029b153d3ad6f3289fe6f05e8029a10c76e8d07a3cdde0c089b99894f1f78dbc`, producer `/dev/shm/known-unit-x-positive-refresh/final-records.json` (record SHA-256 `2f3b06da18484d8d4a85768087d4aa89e5eeadff64570f6ba8b8331c79e64c1a`).
- `ArithmeticPellHalfIndex`: source `9a284bab88a2553569a1c68485ded379b7f5c21a3842c15ab40a1985f4449edd`, object `5afaaea0b2b8a9adafd5e37c9799d387e56b1c9a07fd6e5f8f9bad8ef16ecc02`, producer `/dev/shm/pell-half-p-pos/final-records.json` (record SHA-256 `49a7d13e81ad102109d607eb2e2741f0bfb3834c179286828f6405fa2922e28e`).

The final client records sample the baseline workspace source path for the changed target; the final target build separately links its actual source snapshot and object. Other project, Foundation and Mathlib transitive dependencies remain cached; no complete source-current closure build is claimed. Raw logs and compiled objects are not included.

Temporary external evidence paths and SHA-256 hashes (they may no longer be available later):

- `/dev/shm/firstnorm-time-positive/baseline-records.json`: `cceb8271b4219d712d29339031a928580c6ab33331afe62d057b327e15769a7d`.
- `/dev/shm/firstnorm-time-positive/final-records.json`: `8cfbff4350cc08800274cbbfe69c21f3792d32f088c1aa349321a67b0773c256`.
- `/dev/shm/firstnorm-time-positive/probe-records.json`: `66a4c2ece8b8cf1949b4d60c088046e6dda68ae3abd23cd588b21d4c00d87ea5`.
- `/dev/shm/firstnorm-time-positive/build.py`: `54d3d27e6a811d1a9d0329a1110394dc8f270ebb1c03d0526e64489adbc81b8d`.
- `/dev/shm/firstnorm-time-positive/probe.py`: `9b8b0abc56719ab2fb3a9371bf32c18d2139bd46c46263ab87002255e4870b9b`.
- `/dev/shm/firstnorm-time-positive/audit.py`: `e19a4f2b2f4fb1ffdfe4f0a226492c54b921d0f0add21a12c4829b94390269f1`.
- `/dev/shm/firstnorm-time-positive/audit.log`: `871718272eaa3452939ca3bb5911e708eff138e5b99432114a1ddda695f245dd`.
- `/tmp/firstnorm-time-positive-peer-review.txt`: `4fd4b5bcae74ccfef63b7988d3c59d6866fcad5a6f8ba0f8e0a460f8887c1981`.
- `/tmp/firstnorm-time-positive-peer-audit.py`: `7c4ea80c850b1f17549f087dc1d710bcb2ba4bf8a0f801ec7f2e9877f1c70300`.
- `/tmp/firstnorm-time-positive-peer-audit.log`: `ee34eac1042f9b3302b96cf8e5c9a7f999e18d5ed973b469e06f2b3208f66c44`.

The independent postcommit review checked all paired builds and logs, exact first-provider and target-to-client object pins, probe comparisons, three provider associations and commit/parent snapshots. Full replay requires the external files, build environment and excluded compiled objects.
