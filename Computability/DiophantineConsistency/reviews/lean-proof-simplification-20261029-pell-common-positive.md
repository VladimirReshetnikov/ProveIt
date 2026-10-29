# Pell common-unit positivity validation

Source commit `dd1410705b55f7d15251f1dca0d84615f159333f`, parent `1d7be479ff1850a21fb904c4d017123184f2fb73`. The changed `ArithmeticPellCommonUnit.lean` source has SHA-256 `4611699ee28a5aac8a900395ecc965e570675607851be24de450f04af0f45734` in the parent and `85b2d661536f3353da857b9c9f9c3ca14f1e860dde7c71a25d7c151864b640ea` in the commit. Both match the tested baseline and final2 snapshots. The proof, originally introduced in `e072abe66cc`, removes 12 net lines; no Claude coauthor is asserted.

The paired, source-ordered baseline and final2 builds of `ArithmeticPellCommonUnit`, `ArithmeticPellCommonUnitChecks`, and `ArithmeticPellIntegralSolution` all passed. The target objects differ, with respective SHA-256 `323bd01ea0309cad4888b131a1b93289c0b6f3116073aecda815fea8f7c75c80` and `f8677bc94933a4cf829f28e7a25a14a1a536529c65444969163ffc565d9cce13`. Both direct client objects match byte-for-byte across phases: checks `cd325033bf3827f72c360b8be49c357101f137f1c9450a743e0013649156db5f` and integral solution `d658dd9405d28707078586711228e209ba93156113b0b97d338aef48efc3197a`. Target and integral-solution logs are empty; the checks logs are identical and contain expected `#print axioms` output, with no warnings.

Eight probes pin the exact phase target objects. All five target namespace declaration names, printed type/axiom reports, 28,968 simp lines, and 13,169 instance lines match byte-for-byte. These comparisons do not establish proof-body equality or equality of every persistent extension.

Source-matched direct-provider object and source hashes were independently checked against successful producer records:

- `ArithmeticGcdNormalization`: object `c2ba374dd946d5aee4df1d91cf60b97935180915c43d00ba3b2c2726b1e81da6`, source `bd203be2a1cf32efa43c3809a50fdef104963b3dd9b430b59417c4257bc6d456`; `/tmp/gcd-product-positivity/final-records.json`.
- `ArithmeticPellKnownUnit`: object `8e87f221e6527d3ca305b33a1944d908652a42c0340d8fc105585b3da3c1b1c8`, source `84908d9195b688f1e1c0b121b412c47706cebb94ca8fe722a6c29bd02bf1ec92`; `/dev/shm/pell-unit-advance-sharing-refresh/final-records.json`.
- `ArithmeticPellStrongDivisibility`, a direct integral-solution input: object `60d01da479be4d1a8837f2035e3013ec2da624cf4a0b9df5d7bbecbaab507a72`, source `c20fc77d6483ea342b53053e966022cc25ab27d786206ff52f733adc9d25429b`; `/tmp/pell-balance-sharing/final-records.json`.

The final2 client records sample the baseline workspace source path for `ArithmeticPellCommonUnit`; the final2 target build separately links the actual client input object to the final2 source snapshot. Other project, Foundation and Mathlib dependencies remain cached; no full source-current transitive build is claimed. Earlier exploratory `final/` and `short/` attempts are not the validated final2 lane. No compiled objects or raw logs are included in this note.

Temporary external records, which may no longer be available later, have the following SHA-256 hashes:

- `/dev/shm/pell-common-positive/baseline-records.json`: `27bc7dd0be5c2b1f392e13738d208c9f7b8b3842167868deac9106a39c5611d2`.
- `/dev/shm/pell-common-positive/final2-records.json`: `e08f15e912c2b70309e5bee5a27014f88e332e10897ed32f6ae876b91f52ebf5`.
- `/dev/shm/pell-common-positive/probe-records.json`: `61e83745623bc4ebb61992d30f7bd6aa7e223c21fc9b832ebaf9ac9f2a0791d3`.
- `/tmp/pell-common-positive-peer-audit.py`: `8cd0f27f0b3b2c8624371958e9b0471bd5fd0e7426f7c70829ccf98ddf75d6d0`.
- `/tmp/pell-common-positive-peer-audit.log`: `de3047b8c99fcded6ce6458e707a7d87c94b59e4200a4bac9fcb24d4e6d9d6d3`.
- `/tmp/pell-common-positive-peer-review.txt`: `dcdd48f5968df179c64fec7da2e21489cf6a9f3db86a62b4c857e13660403968`.

The independent review checked all six builds, source and first-provider object pins, target-to-client associations, object-pinned probes, matching reports, the three provider associations, and parent/commit snapshots. It corrected an earlier claim that the checks logs were empty; no other concern was found. Full replay requires the external records, build environment, and excluded compiled objects.
