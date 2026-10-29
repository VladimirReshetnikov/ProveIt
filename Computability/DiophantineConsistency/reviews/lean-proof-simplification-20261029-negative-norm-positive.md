# Negative-norm descent positivity validation

Source commit `68cfd1dde1b95c11eaf639cdefbbe078d30ff94f`, parent `60a6bec4430e23e6b9fb2fc52e0f2d30d7871020`. `ArithmeticNegativeNorms.lean` has SHA-256 `f836b20c05266d9e05a4aa0ca813879b790793d0a004ae89ae15292eb6521a16` in the parent and `0b1732d9079df9257b3066d90a49f3d95b5d96ea2d2c7aef2b433e913158d84d` in the commit. Both match the tested baseline and final snapshots. The affected proof was introduced in `4a2735902f3`; no Claude coauthor is asserted. The edit removes five net lines.

Paired source-ordered builds of `ArithmeticNegativeNorms`, `ArithmeticNegativeNormsChecks`, and `ArithmeticCarrierSoundness2011` all passed. The target objects differ (baseline SHA-256 `b2bdbe9aa853aad19363d14d81792a27e2b9b49d18f8ce32ef4713cb94465d54`, final `8de5c11d5adf956b8fd30c56606a1679017df6e8e6a8667b910f17bd80e37fc1`). Both direct clients are byte-identical across phases: checks object `187428eaf70c455c709e211aa15f305e91bee9bb860a8cba63f4982e1db3206d` and production client `a9b3588787c4ecd29e1d7a16a29d39d8174a48268f4202ba104185b5c4247070`. Target and production-client logs are empty; check logs are identical and contain expected `#print axioms` output with no warnings.

The original production-client builds used an older `ArithmeticSignedPairs` object. A separate paired client replay with source-matched current providers passed, with the same byte-identical client object in both phases. Its three direct provider source/object pairs match successful producer rows:

- `ArithmeticSignedPairs`: object `590bf56e9b0c3baef94cbb204f0a473a64b919967538a9920760e1167d44f5eb`, source `ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d`; `/tmp/signed-pairs-factors/final-records.json`.
- `ArithmeticPellFirstIndex`: object `60bd7deb77e8a9f1d31c0a77e15423d655c5dd970a5d630315bfaa5dac7d1bae`, source `86e3a3698a1a78e713e80d876f8ccee0067dd8900854dcf6958cbe78abf96631`; `/dev/shm/pell-unit-advance-sharing-refresh/final-records.json`.
- `CurrentEquationSyntax2011`: object `28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae`, source `112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9`; `/dev/shm/pell-y-six/refresh2-records.json`.

Eight probes pin the exact phase target objects and yield byte-identical reports for 15 declaration names, 55 printed type/axiom lines, 28,810 simp lines, and 13,062 instance lines. This does not establish proof-body equality or equality of every persistent extension. The final-phase client records sample the baseline workspace source path for `ArithmeticNegativeNorms`; the final target build separately links the actual client input object to the final source snapshot. Other project, Foundation and Mathlib dependencies remain cached; no full source-current transitive build is claimed. An initial production-client attempt failed before elaboration because the overlay lacked project namespace entries; the successful paired builds used a corrected overlay. No compiled objects or raw logs are included in this note.

Temporary external records, which may no longer be available later, have these SHA-256 hashes:

- `/dev/shm/neg-norm-y/baseline-records.json`: `e82d35ef0dc392b642eb1a7a04d123a0d44f626abcb424c25e6e246b73ecaea0`.
- `/dev/shm/neg-norm-y/final-records.json`: `ddb1e58e069c9c8a4d7ddae7c2557d5fda55df877df35926b687d1e023227a2b`.
- `/dev/shm/neg-norm-y/baseline-replay-record.json`: `d1b2f6c0eb4caac4dff90ef5b6f9f494935b41aa0a57d0ca81f27b3d56c58699`.
- `/dev/shm/neg-norm-y/final-replay-record.json`: `fda90025f580ee66d300c97d99ec1e491c89bef0d83b0033f6423170af3025e9`.
- `/dev/shm/neg-norm-y/probe-records.json`: `6f1ee45f3908f387437d9519fb0e387488f21b1002e2b275acf3cd7044f0e497`.
- `/tmp/negative-norm-positive-peer-audit.py`: `b4a396dd6c143cc24a33d78ce1f984ac97f626967b6c0c07abf867614089a5e9`.
- `/tmp/negative-norm-positive-peer-audit.log`: `f6692268cd9c277052f02f503c5754ce695b0d40e4907d213a44e0cf16c84b01`.
- `/tmp/negative-norm-positive-peer-review.txt`: `5aa06836937bd0ec93893cfd64df2ab6176e424fa3ddcb8e6f4eeed58fd0908f`.

The independent review checked all six paired builds, first-provider paths and source/object pins, both refreshed client builds, target-to-client object associations, eight object-pinned probes, matching reports, all three current replay-provider associations, and parent/commit snapshots. It found no further concern. Full replay requires the external records, build environment and excluded compiled objects.
