# Shared represented Pell coordinate bound: validation

Source commit `7d85310ff92946946b50d1ff92a36b58cb399692` and parent `fe6a2aac3f527d20bcb989b275e27a19e07f1c03` match the tested final and baseline source snapshots. The change moves two coordinate-bound proofs into `ArithmeticPellRecurrence.ordinate_lt_abscissa` and retains both existing `y_lt_x` statements as aliases. It removes six net lines, adds one public theorem, and adds no imports or registrations.

The source SHA-256 hashes (parent / commit) are:

- `ArithmeticPellRecurrence.lean`: `03949bb0b0e769f18befadab188a0b2d82ed830fda6e3e0fb65389b71a1677a2` / `b2c9d9dc41be16aa503540851c3c9752e2c475a947666f79eb9ea539aebe14af`.
- `ArithmeticPellIntegralSolution.lean`: `66469938b38f9049e0f2c6311b411bb30de2c9daa26c0f383652bde40267f666` / `6f8f08e11cfdd1890507608187ab5a8ea7fb37c102653668aa91ad5ad1b830b5`.
- `ArithmeticPellPeriodicity.lean`: `27f0089eef0b1da679d0a79b24eafc0d18be047c2bcc69b240f78b321f040cdd` / `6327f5f4ab6dcf4a2adec32f8fc080588844ea431e0ad58dddb0e4d9b9a3a213`.

All twelve paired baseline/final builds passed. All three direct importers of Recurrence and all five direct clients of the two wrappers were built; PellCongruences was also rebuilt. The three check-module objects match; all other tested objects differ, including Classification, StrongDivisibility, Congruences, IndexDivisibility, SquaredSeed and ResidueClasses. Target and production logs are empty; check logs contain matching expected `#print axioms` output and no warnings.

The following table records the baseline/final SHA-256 of every compiled object (the objects themselves are not retained in this note):

| Module | Baseline | Final |
|---|---|---|
| `ArithmeticPellRecurrence` | `0a5e3d0594e08a1be69f6cf5d8c4ce9d06c35d1591c809c9bafcd277470e4399` | `0b58739aea61f13a516c86ccab1dad0d39021fda50bf84ff91ab3f5cd557d5f0` |
| `ArithmeticPellRecurrenceChecks` | `527e705fca517a51ac379150cbb7f7fd70f771b8f02ed0c8aba70dbd2520eb89` | `527e705fca517a51ac379150cbb7f7fd70f771b8f02ed0c8aba70dbd2520eb89` |
| `ArithmeticPellClassification` | `0ff552f5b80c50b31fa6b8e2cd04246e025c8703e1aa07dde639e358d046ce9a` | `c70752648f0ae5bc4a186364c2de2e4beb20eacf5c8611b6f66931c7553f15d8` |
| `ArithmeticPellStrongDivisibility` | `60d01da479be4d1a8837f2035e3013ec2da624cf4a0b9df5d7bbecbaab507a72` | `1ffd2773a1455819b3480597da20e8dbc16ccaf4f17c38e5db2b17bc34aafd0d` |
| `ArithmeticPellCongruences` | `42211a61d89377ab8b5a8629836ce49d81c465a61dd8a960e67766d43f6bf558` | `1e91f92544d245ec86a0d3399470b2bf821c46e79b29d815ff103663de634722` |
| `ArithmeticPellIntegralSolution` | `d658dd9405d28707078586711228e209ba93156113b0b97d338aef48efc3197a` | `aef539992eae3308695ab6294c033a33616708cab9356ec00952a8af67cf4d8f` |
| `ArithmeticPellPeriodicity` | `e12da1534c76d92f593859ea360edb7c120cda2042ebaf72923bc8178189bfa1` | `af38b702578ce3523e47ac5a4c73b3294bc287c53a5f0dd0aff064f9da7e5892` |
| `ArithmeticPellIntegralSolutionChecks` | `08d2179ce5d9ec991b1344b39cb72b27e52908dd4ff6cc45a7bf08c347e963e9` | `08d2179ce5d9ec991b1344b39cb72b27e52908dd4ff6cc45a7bf08c347e963e9` |
| `ArithmeticPellIndexDivisibility` | `f371d5f12e89cbf8648ba9390086465f244b7dac67bce7d16f0a691d585ec4f2` | `b8dfc8d43a583d7c06f1dcb70b9a1d9697ec377943afbc9db878f9c6cafd5a35` |
| `ArithmeticPellPeriodicityChecks` | `4f003f7cb9cfe14779b207256e16fcbea9bcb5329b0559943f5e7cafe2dd6ba4` | `4f003f7cb9cfe14779b207256e16fcbea9bcb5329b0559943f5e7cafe2dd6ba4` |
| `ArithmeticPellSquaredSeed` | `2f475634a71552d93d9620f6b8bb9649df4beb913617d4ff59a42fd9e0e36c89` | `05808ba096f9f3ec7fedd2b8b1561c0c2e5b6f7ff1b6faa2808765d891cf1034` |
| `ArithmeticPellResidueClasses` | `821c53dea2af0240b63e85a28702e5f36a5f858d9fd8dbb11bba4e2ed2e64f6a` | `81e0c4d76d035963134cc1aeddd713a3da12af0850e561cf89ee9f9120464c22` |

Eight combined probes pin all twelve respective phase objects. The 147 common namespace names, printed types and axioms agree, with one new public Recurrence theorem; sampled simp (28,977) and instance (13,169) registrations match byte-for-byte. These reports do not prove proof-body or full persistent-extension equality.

The tracked Lean import graph has 51 transitive Recurrence consumers, including the two changed wrappers, of which 49 are unchanged; 36 are downstream of the wrappers. The two wrappers and 13 other consumers inherit the new ordinary declaration in addition to those 36 downstream modules. No new imports, simp rules or instances were added. The three direct Recurrence clients were rebuilt, but no complete transitive rebuild or performance claim is made. A single shared-load baseline/final observation recorded 13.13/13.95 user CPU seconds for Recurrence; three direct clients recorded 1.98/2.03, 8.27/8.63 and 6.78/7.26 seconds. These observations are not a benchmark.

The direct external project objects GcdNormalization, CommonUnit and ModularCancellation match their source-current producer records listed below. The CommonUnit object was built against the then-current KnownUnit object from `e9c6492417`; this and other project, Foundation and Mathlib transitive dependencies remain cached. Full source-current transitive closure is not claimed.

The independent review checked the 24 builds, eight object-pinned probes, graph counts, three direct-provider associations and postcommit snapshots. Raw logs and compiled objects are not included. The following temporary external evidence paths and SHA-256 hashes may cease to be available; full verification requires the external evidence and build environment:

- `/dev/shm/shared-pell-recurrence/baseline-records.json`: `4ec023172a95e74f883be97d0914bd3e8adda43ee4ac9eddf2f2f61f07e4cdde`.
- `/dev/shm/shared-pell-recurrence/final-records.json`: `25f1a912a593a0ef8360a5c43c36f5de4d8f7a1e555101d27cd64745b555fbee`.
- `/dev/shm/shared-pell-recurrence/baseline-probe-records.json`: `eaa5d858f49365e71e57f949b9ec55d306981cacef2f4b155210a123e25c03e9`.
- `/dev/shm/shared-pell-recurrence/final-probe-records.json`: `4dc883c89b5dee5eadfc746f9f49f7d3612b93f64b8beaae554008860c4d6c5b`.
- `/dev/shm/shared-pell-recurrence/build.py`: `3cabb2a488a14155bf49f9b2d2ea1fb75839b3cd436c9ffba6ba2cb094ff7dbe`.
- `/dev/shm/shared-pell-recurrence/probe.py`: `7aca58fca69bcd4ad6ef9e2d3c3f48ff5e0c10f904f1e3278879daa14750c408`.
- `/dev/shm/shared-pell-recurrence/audit.py`: `c4b517ed0d8245ac9ea5049fb992fc1b672e0a6c9ef8cecde0691980892b78a5`.
- `/dev/shm/shared-pell-recurrence/audit.log`: `f209f99c458af46a73b361997bc3742789de5a1280831ec69d2256cbe1523a42`.
- `/tmp/gcd-product-positivity/final-records.json`: `d1bf4bae9291e2d871f9b2f03ec17bfe3471b424c628e36fa38b2b52699a92c9`.
- `/dev/shm/pell-common-positive/final2-records.json`: `e08f15e912c2b70309e5bee5a27014f88e332e10897ed32f6ae876b91f52ebf5`.
- `/tmp/shared-modular-cancel/records.json`: `dbcffd99ff983fb26550f3098bb801fb3f5f11dcb44c425b21b74d80ec2a5062`.
- `/tmp/shared-pell-recurrence-peer-audit.py`: `5ab4b02547e5a06ceccdc9836d08aa6f225ac5ea5fdbf105e960aa0f45865ea9`.
- `/tmp/shared-pell-recurrence-peer-audit.log`: `9f6a47725fa1aef54501e195971a35963e90474f783f674325ed93712cc2fa45`.
- `/tmp/shared-pell-recurrence-peer-review.txt`: `71cb5874e53307be63c463f381f1c7a80b59fe4a17d272486359380945217d0f`.
