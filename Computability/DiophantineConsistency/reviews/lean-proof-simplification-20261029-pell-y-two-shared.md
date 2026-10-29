# Shared two-step Pell ordinate validation

Source commit `b876051618c800b2a26453d48a9c46df46566329` and parent `e3527a49f98aeafa75617f8274ba6e079a9c4d7b` match the tested final and baseline snapshots for both targets. The change replaces three separate two-step ordinate derivations with one public `ArithmeticPellHalfIndex.y_two` theorem; it removes six net Lean lines without changing existing definitions, imports, assumptions or theorem statements.

All fourteen paired builds passed for the two targets and five tracked direct clients. The checks and CarrierSoundness objects match byte-for-byte; AuxiliarySeed and PowerRecovery objects differ. Target and production logs are empty. Both checks modules emit identical expected `#print axioms` output with no warnings.

| Module | Baseline object SHA-256 | Final object SHA-256 |
|---|---|---|
| `ArithmeticPellHalfIndex` | `5afaaea0b2b8a9adafd5e37c9799d387e56b1c9a07fd6e5f8f9bad8ef16ecc02` | `ea09732132db24587cc02e20200fb84f55ba37f9d071b1602c6993572392d9a6` |
| `ArithmeticPellHalfIndexChecks` | `bbf47b3656dec1812190f63f6484a8bc89833ef141aaa2cf0ef15b3682353cbf` | `bbf47b3656dec1812190f63f6484a8bc89833ef141aaa2cf0ef15b3682353cbf` |
| `ArithmeticPellFirstIndex` | `24290ef5a4d3a3979a2c107320694d9cbbd1853655ca222a73750d4b5b181b4f` | `7fe453cd8b701f3e49044a44b1fc113dfb7dba39d5373f21b11af7c59525e62f` |
| `ArithmeticPellAuxiliarySeed` | `77a7611beed37708c840269caf2d7f042fd3c9ad2a8aaa32d98fafd6df044743` | `0b874ccf77e55d3a814d3e2cb1a6dcc756d5cb0f87eba5ee67c7ad63e8ee01ea` |
| `ArithmeticPellFirstIndexChecks` | `4ed71602be08ad2891bfd0d79c8cc27d79594eb333c5c20549e3db63c8f74c3a` | `4ed71602be08ad2891bfd0d79c8cc27d79594eb333c5c20549e3db63c8f74c3a` |
| `ArithmeticPellPowerRecovery` | `6f3522b965cb55e4229ba8007fa5f01babeacc4df94e8f3df76a9a15c5d01b18` | `2faa94f4e5005a0a48129e6626128af7e437bc9ff4c059d34892caedbd99eedd` |
| `ArithmeticCarrierSoundness2011` | `a9b3588787c4ecd29e1d7a16a29d39d8174a48268f4202ba104185b5c4247070` | `a9b3588787c4ecd29e1d7a16a29d39d8174a48268f4202ba104185b5c4247070` |

Eight probes each pin seven phase objects plus Recurrence, KnownUnit, CommonUnit, IntegralSolution, IndexDivisibility, Periodicity, ResidueClasses, ModularCancellation and FirstNorm. All 137 common namespace declaration/type/axiom reports and sampled global simp/instance registrations match, with one public `y_two` addition. These printed comparisons do not establish equality of proof bodies or all persistent extensions.

Both target source snapshot hashes (parent / commit):
- `ArithmeticPellHalfIndex.lean`: `9a284bab88a2553569a1c68485ded379b7f5c21a3842c15ab40a1985f4449edd` / `a5a70709f8a3266f81dd5b2d56f7c711cb44cfdcf73a9dc11d37fac7e779c2d7`.
- `ArithmeticPellFirstIndex.lean`: `5d0c42fb3e4dd68cd527f634b911ce9bcfa4a1722f0f6d28147203338dd977d3` / `078011c8798040aa54b1bc482df4703a0d5167ac39c25aeaab2018f4f83e36ec`.

Seven external direct project providers match successful source-current producer records:
- `ArithmeticPellIndexDivisibility`: source `fc0e2fc57734a6043a9f43b0877a805ff4b53f76d9e978d7088c9a02a79c5feb`; object `b8dfc8d43a583d7c06f1dcb70b9a1d9697ec377943afbc9db878f9c6cafd5a35`; receipt `/dev/shm/pell-half-p-pos/common-records.json` (SHA-256 `f2a681e2715ae61b0d9f222faf9ac4f49e9bc85cb78116f306d8dbe2081e7a6a`).
- `ArithmeticPellResidueClasses`: source `df4884c9c9cc4446163deb37aede62fea410d5d686d89de1e30aa58331bcbe5a`; object `a5afe2834ee7419f9b5b7d6ac47a6886891d91a489cf771169b18843ed298867`; receipt `/dev/shm/mod-nested-share/final-pell-records.json` (SHA-256 `f23ea97a4a4930761fc28a4103cf091f825ec0701e4f916053d13fd314c0ec1b`).
- `ArithmeticPellFirstNorm`: source `0a6c3ecfbf1a6aa62fecf168de0757760b2e8606754d4ad1974f26add46cf501`; object `bab7ce73467466a0032aac354a802dfcca264a250531ff702df779e39ff473f9`; receipt `/dev/shm/firstnorm-time-positive/final-records.json` (SHA-256 `8cfbff4350cc08800274cbbfe69c21f3792d32f088c1aa349321a67b0773c256`).
- `ArithmeticPellSquaredSeed`: source `9e4cc08b5992b2074d2046ef7cb4d2854b0147cc66829897b7d6ac7c5f4d8ec7`; object `05808ba096f9f3ec7fedd2b8b1561c0c2e5b6f7ff1b6faa2808765d891cf1034`; receipt `/dev/shm/shared-pell-recurrence/final-records.json` (SHA-256 `25f1a912a593a0ef8360a5c43c36f5de4d8f7a1e555101d27cd64745b555fbee`).
- `ArithmeticNegativeNorms`: source `0b1732d9079df9257b3066d90a49f3d95b5d96ea2d2c7aef2b433e913158d84d`; object `8de5c11d5adf956b8fd30c56606a1679017df6e8e6a8667b910f17bd80e37fc1`; receipt `/dev/shm/neg-norm-y/final-records.json` (SHA-256 `ddb1e58e069c9c8a4d7ddae7c2557d5fda55df877df35926b687d1e023227a2b`).
- `ArithmeticSignedPairs`: source `ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d`; object `590bf56e9b0c3baef94cbb204f0a473a64b919967538a9920760e1167d44f5eb`; receipt `/tmp/signed-pairs-factors/final-records.json` (SHA-256 `bb15b29690d49eef61b2f4f18a995c497db65fa1cfd9f0c9441899be5000e843`).
- `CurrentEquationSyntax2011`: source `112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9`; object `28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae`; receipt `/dev/shm/pell-y-six/refresh2-records.json` (SHA-256 `121901f4d33ff9160a9f4aa377096a751c5f504851cf67c203dd7b8cd7f99d3c`).

The final client input source paths for changed targets sample the baseline workspace before adoption; actual phase-specific objects are linked to final source snapshots by target build rows. Other project, Foundation and Mathlib dependencies remain cached; no full current-source transitive build is claimed. The initial isolated try lane is exploratory; the paired lane is authoritative. Timings are single shared-load observations.

The following transient records are external to this note and may no longer be available later:
- `/dev/shm/pell-y-two-shared/baseline-records.json`: SHA-256 `da554c2a517ae6085e5155a274def387bac328fb8f501c960c12d9769af64f15`.
- `/dev/shm/pell-y-two-shared/final-records.json`: SHA-256 `dc573cbe441cbe485c7cbe7414346f7dce2fd18321b8fe7c7aac447ef41d3980`.
- `/dev/shm/pell-y-two-shared/baseline-probe-records.json`: SHA-256 `b14d8549ca56177a32dbd0985d3e7037b36bd48c6d9202f91010aaab60719dbe`.
- `/dev/shm/pell-y-two-shared/final-probe-records.json`: SHA-256 `0336f013a38c690dcd88c3dd94075579a774a5c34a2b00fc762179fa7c77262a`.
- `/dev/shm/pell-y-two-shared/build.py`: SHA-256 `9ffb8b114eb55ca9bf1b339c0aeba92c54a49b6ae356aa3638a68f26ac294586`.
- `/dev/shm/pell-y-two-shared/probe.py`: SHA-256 `ff4f836ef648a31d41896e77273f05c018c7b5e76838cb6d609254e69ac714a7`.
- `/dev/shm/pell-y-two-shared/audit.py`: SHA-256 `b5110e1ad8088750a446384089ebf567fb206de3c84d657879bf6aff14f00f7c`.
- `/dev/shm/pell-y-two-shared/audit.log`: SHA-256 `d45bd215e38861171ebcde31e6f8a168379492c3c4c25eab03a6a550dd693080`.
- `/tmp/pell-y-two-peer-111-audit.py`: SHA-256 `862efaf232bda67f4cdd8db4a87d47cba2d682ff48efb88705f5dfd00d5561bf`.
- `/tmp/pell-y-two-peer-111-audit.log`: SHA-256 `5ab2406bf9adfebbc5aa5051064cc9ffd01e1fceafd49b8fba8ee1b0316b1bc8`.
- `/tmp/pell-y-two-peer-111-review.txt`: SHA-256 `f941db7f31cf8995a4640270c82665ee10340a2afa50fc3f7be145b43e16fd71`.

The independent review checked the proof, paired builds, first-path associations, all probes, project-provider receipts and postcommit snapshots. Raw logs and compiled objects are not included; full replay requires the transient external records, build environment and dependencies.
