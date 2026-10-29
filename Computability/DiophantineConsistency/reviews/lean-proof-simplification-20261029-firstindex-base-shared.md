# Shared first-index base identity: validation

Source commit `c0097510a1b910e3ee01d74843f93ec8d6c8f979` and parent `8cbd0f7b13ccffecef62049b958e1c5e7c106a9a` match the tested final and baseline source snapshots byte-for-byte. Source SHA-256: `078011c8798040aa54b1bc482df4703a0d5167ac39c25aeaab2018f4f83e36ec` (parent) and `f138ac017027faf4772cf8a310772465fdc0acd42a6391422086d2cdb64fc342` (commit). The change removes three net Lean lines by deriving the repeated B+2=2*Q+1 identity once; theorem statements, assumptions, definitions and imports are unchanged. Git blame traces the original arguments to `531058ae33f`; no Claude coauthor is asserted.

Paired source-ordered target and all three direct clients passed. Their object hashes are:

| Module | Baseline SHA-256 | Final SHA-256 |
|---|---|---|
| `ArithmeticPellFirstIndex` | `7fe453cd8b701f3e49044a44b1fc113dfb7dba39d5373f21b11af7c59525e62f` | `a4ce5a7c78434f2f64c5cafe4c5b4dfc9bf1c6ea3c494da3718818baf70565e7` |
| `ArithmeticPellFirstIndexChecks` | `4ed71602be08ad2891bfd0d79c8cc27d79594eb333c5c20549e3db63c8f74c3a` | `4ed71602be08ad2891bfd0d79c8cc27d79594eb333c5c20549e3db63c8f74c3a` |
| `ArithmeticPellPowerRecovery` | `2faa94f4e5005a0a48129e6626128af7e437bc9ff4c059d34892caedbd99eedd` | `2faa94f4e5005a0a48129e6626128af7e437bc9ff4c059d34892caedbd99eedd` |
| `ArithmeticCarrierSoundness2011` | `a9b3588787c4ecd29e1d7a16a29d39d8174a48268f4202ba104185b5c4247070` | `a9b3588787c4ecd29e1d7a16a29d39d8174a48268f4202ba104185b5c4247070` |

All three client objects match byte-for-byte. Target and production-client logs are empty; checks logs have matching expected #print axioms output and no warnings. Eight probes pin all four compiled phase objects and four provider objects. Their 94 common namespace names, printed types and axioms, and sampled global simp and instance registrations match byte-for-byte. These reports do not establish equality of proof bodies or all persistent extensions.

Five external direct project providers matched source-current successful producer rows:

- `ArithmeticPellHalfIndex`: object `ea09732132db24587cc02e20200fb84f55ba37f9d071b1602c6993572392d9a6`, source `a5a70709f8a3266f81dd5b2d56f7c711cb44cfdcf73a9dc11d37fac7e779c2d7`; `/dev/shm/pell-y-two-shared/final-records.json`.
- `ArithmeticPellFirstNorm`: object `bab7ce73467466a0032aac354a802dfcca264a250531ff702df779e39ff473f9`, source `0a6c3ecfbf1a6aa62fecf168de0757760b2e8606754d4ad1974f26add46cf501`; `/dev/shm/firstnorm-time-positive/final-records.json`.
- `ArithmeticNegativeNorms`: object `8de5c11d5adf956b8fd30c56606a1679017df6e8e6a8667b910f17bd80e37fc1`, source `0b1732d9079df9257b3066d90a49f3d95b5d96ea2d2c7aef2b433e913158d84d`; `/dev/shm/neg-norm-y/final-records.json`.
- `ArithmeticSignedPairs`: object `590bf56e9b0c3baef94cbb204f0a473a64b919967538a9920760e1167d44f5eb`, source `ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d`; `/tmp/signed-pairs-factors/final-records.json`.
- `CurrentEquationSyntax2011`: object `28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae`, source `112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9`; `/dev/shm/pell-y-six/refresh2-records.json`.

The final client records sample the baseline workspace FirstIndex source before adoption; the final target build separately links its actual object to the final snapshot. Other project, Foundation and Mathlib transitive inputs remain cached; no full source-current closure is claimed. Full replay requires the temporary external records and compiled dependencies, which are not included here.

Temporary external evidence hashes:

- `/dev/shm/firstindex-base-shared/baseline-records.json`: `7ae5afe36b6747e1d05641f7faaf5b9c2dfe92ac2f2dc6cce0e8d271aa94172b`.
- `/dev/shm/firstindex-base-shared/final-records.json`: `043e2888a145c80137b167395aaef7d743bab372d59bddf2ff432875021b6001`.
- `/dev/shm/firstindex-base-shared/probe-records.json`: `b4e120db2181399ddf5dcc20d01372447ad943d4f9506e47744d9458f4403c23`.
- `/dev/shm/firstindex-base-shared/build.py`: `d2fed8c4a958132a039701d071f4c8879cf152ef8d200ef77be3d51ea95bccd9`.
- `/dev/shm/firstindex-base-shared/probe.py`: `3e94ae5756ce78a28f88620d8602a70b3af7e534e3c8c93f131da9b79bb61bb2`.
- `/dev/shm/firstindex-base-shared/audit.py`: `effccd433779b5ec16d2f8637f871c158e8eb9fd214928293b2c5a9f63c1d341`.
- `/dev/shm/firstindex-base-shared/audit.log`: `1aa0c06c5f29f77e4c39d8db83083f96fb839e1ac96037a1151c926d7019b9f3`.
- `/tmp/firstindex-base-shared-peer-123.py`: `e12fc0ba05fbac53cf916ad437adb98a4df3d07e1b8ec2e0e405fb64079d377b`.
- `/tmp/firstindex-base-shared-peer-123.log`: `f9cbbadf213474600c2eef3bec90aa46d98b7f5c163a9157d84dfbd874baedc8`.
- `/tmp/firstindex-base-shared-peer-review.txt`: `45d5c532bf28dd94f6a9c07745f7efd88730102612ddd6279c6b298168a45756`.

The independent review checked the source and first-provider paths, all eight builds and eight probes, five provider associations, byte-identical client outputs, report comparisons and postcommit snapshots. Timings are single shared-load observations, not a benchmark.
