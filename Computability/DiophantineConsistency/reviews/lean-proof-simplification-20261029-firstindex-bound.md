# Pell first-index lower bound: validation

Source commit `d3b30c1953073197e3865e8cd685234e7a640396` and parent `dfa1f00e7e257643b290e3055c7b65d828ec8ec3` match the tested final and baseline source snapshots. Parent source SHA-256 `b345506fef9ec078f8fa801967685fa93adba99b5b16d277aa9ebb1998a899e0`; commit source SHA-256 `5d0c42fb3e4dd68cd527f634b911ce9bcfa4a1722f0f6d28147203338dd977d3`. The proof originally appeared in `531058ae33f`, with no Claude coauthor asserted. It replaces an indirect contradiction with strict multiplication cancellation, removing two net lines. Existing theorem statements, imports and assumptions are unchanged.

Paired target and all three direct clients pass using the refreshed providers. The three client objects match byte-for-byte across phases, and every refreshed output matches its corresponding original-lane output. Target, PowerRecovery and CarrierSoundness logs are empty; the checks logs contain identical expected `#print axioms` output without warnings.

| Module | Baseline object SHA-256 | Final object SHA-256 |
|---|---|---|
| `ArithmeticPellFirstIndex` | `994b90ca744768cfb199e3ee48d947f05f17692d18034b1a27d7e9f07dd84d4f` | `24290ef5a4d3a3979a2c107320694d9cbbd1853655ca222a73750d4b5b181b4f` |
| `ArithmeticPellFirstIndexChecks` | `4ed71602be08ad2891bfd0d79c8cc27d79594eb333c5c20549e3db63c8f74c3a` | `4ed71602be08ad2891bfd0d79c8cc27d79594eb333c5c20549e3db63c8f74c3a` |
| `ArithmeticPellPowerRecovery` | `5fd246d87260fa5467f39833cb91c8bebd2da6921304cfe4ca5a4657887d9e92` | `5fd246d87260fa5467f39833cb91c8bebd2da6921304cfe4ca5a4657887d9e92` |
| `ArithmeticCarrierSoundness2011` | `a9b3588787c4ecd29e1d7a16a29d39d8174a48268f4202ba104185b5c4247070` | `a9b3588787c4ecd29e1d7a16a29d39d8174a48268f4202ba104185b5c4247070` |

Eight probes pin each exact phase target object plus current-source HalfIndex, FirstNorm, NegativeNorms, SignedPairs and equation-syntax objects. The 10 target namespace names, printed type and axiom output, and sampled 28,977 simp and 13,170 instance lines match byte-for-byte. These reports do not establish proof-body equality or equality of every persistent extension.

The refreshed direct provider associations are:

- `ArithmeticPellHalfIndex`: object `5afaaea0b2b8a9adafd5e37c9799d387e56b1c9a07fd6e5f8f9bad8ef16ecc02`, source `9a284bab88a2553569a1c68485ded379b7f5c21a3842c15ab40a1985f4449edd`; producer `/dev/shm/pell-half-p-pos/final-records.json` (record SHA-256 `49a7d13e81ad102109d607eb2e2741f0bfb3834c179286828f6405fa2922e28e`).
- `ArithmeticPellFirstNorm`: object `98944850cfe61fa88a2a6f1271edd15fe0b5dcb1e0619862a7c7b7a756e2ba65`, source `1a28867ced88fb1b56b872bf900052c3035a4a42502ea024b1f4a7ef5347b816`; producer `/dev/shm/known-unit-x-positive-refresh/final-records.json` (record SHA-256 `2f3b06da18484d8d4a85768087d4aa89e5eeadff64570f6ba8b8331c79e64c1a`).
- `ArithmeticNegativeNorms`: object `8de5c11d5adf956b8fd30c56606a1679017df6e8e6a8667b910f17bd80e37fc1`, source `0b1732d9079df9257b3066d90a49f3d95b5d96ea2d2c7aef2b433e913158d84d`; producer `/dev/shm/neg-norm-y/final-records.json` (record SHA-256 `ddb1e58e069c9c8a4d7ddae7c2557d5fda55df877df35926b687d1e023227a2b`).
- `ArithmeticSignedPairs`: object `590bf56e9b0c3baef94cbb204f0a473a64b919967538a9920760e1167d44f5eb`, source `ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d`; producer `/tmp/signed-pairs-factors/final-records.json` (record SHA-256 `bb15b29690d49eef61b2f4f18a995c497db65fa1cfd9f0c9441899be5000e843`).
- `CurrentEquationSyntax2011`: object `28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae`, source `112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9`; producer `/dev/shm/pell-y-six/refresh2-records.json` (record SHA-256 `121901f4d33ff9160a9f4aa377096a751c5f504851cf67c203dd7b8cd7f99d3c`).

The earlier lane used pre-commit HalfIndex and older NegativeNorms/SignedPairs objects; the refreshed lane pins current-source replacements. Other transitive project, Foundation and Mathlib dependencies remain cached; no complete source-current closure is claimed. No raw logs or compiled objects are retained in this note. Full replay requires the temporary external evidence listed below, which may later be unavailable.

External evidence SHA-256 hashes:

- `/dev/shm/firstindex-bound/baseline-records.json`: `c426b18121ae632bac226a8a9e493d6c0441870f992dc4c29d16ac235d681596`.
- `/dev/shm/firstindex-bound/final-records.json`: `526edc57255871c4a8f54bc765936b4979ce184276069069bec5a4f028edfd48`.
- `/dev/shm/firstindex-bound/baseline-refresh-records.json`: `fb81cef0214e74d8fb0157b533149dbf8165678ec3fd61695900523cefecc957`.
- `/dev/shm/firstindex-bound/final-refresh-records.json`: `d4657ba153c11c7f631b4fb69c9744fc804a2e69105186bf62a33698ea7cf7ba`.
- `/dev/shm/firstindex-bound/probe-records.json`: `7273c73891bc08d3d1d6c4b9d84235c380004695531fde7e81811011e8cd57bc`.
- `/dev/shm/firstindex-bound/audit.py`: `9fac3eefdeb9dd928440a31a831516d6a5a16655058daae6246345b7afd6b5eb`.
- `/dev/shm/firstindex-bound/audit.log`: `d9cbe0929f8551b0eedf3f9cca3e04d61950dd82690e88856676c088f080ba6b`.
- `/tmp/firstindex-bound-peer-audit.py`: `1ee185630d30089c477507e2e994121ab749b0aa1e0fba56865030d176233122`.
- `/tmp/firstindex-bound-peer-audit.log`: `530af4f8dd2a8942d7904de49add1ed7e56bfa958a39c5927ff62bb6e6b3a328`.
- `/tmp/firstindex-bound-peer-review.txt`: `d03e7c1401c798d8b1d843afafc5f6863fb99364bfd4b6dbebc73098a56a5ffc`.

The independent review verified all 16 initial/refreshed builds, first-provider/source pins, target-to-client associations, eight six-object probes, report comparisons, source-current producer receipts, and the parent/commit snapshots. The review checked the recorded build evidence; it did not itself rerun Lean.
