# Pell upper-step square comparison validation

Source commit `fe8073db5a81331f4358c2b7803d5323728df795`, parent `0c5c9b3eb26ad2cb2164cf5dc814ffae6211a7c3`. Their target source SHA-256 hashes are `8b01819d4814e68efc399df146d705015a3ded742bedf5a5b59dc054ca3b016b` and `d242b25c32e03ff62a474835380d3b77f91ac1c0ac6e9415670a249bd64d32e2`, respectively, matching tested final and baseline snapshots. The change replaces a contradiction with an existing square-comparison lemma, removes two net lines, and preserves imports, definitions, assumptions and theorem statements. Original proof lines were introduced in `2340b0c06ba`; no Claude attribution is asserted.

Paired source-ordered builds of `ArithmeticPellPowerRecovery` and its three tracked direct clients passed. All three client objects match byte-for-byte across phases. Both checks logs contain identical expected `#print axioms` output; other build logs are empty. No warnings occurred.

| Module | Baseline object SHA-256 | Final object SHA-256 |
|---|---|---|
| `ArithmeticPellPowerRecovery` | `bf44666e140c4863ccff083975d8a85ce05c949689edc7c80e6415fb5c0b4644` | `6f3522b965cb55e4229ba8007fa5f01babeacc4df94e8f3df76a9a15c5d01b18` |
| `ArithmeticPellPowerRecoveryChecks` | `a547df0df23bea532566c31ef528e6f9ba5764d99f01fadddb08a532e9469248` | `a547df0df23bea532566c31ef528e6f9ba5764d99f01fadddb08a532e9469248` |
| `ArithmeticHalfBinomialSandwich` | `61db8eb1a1f287bbe58c3e72eb05d4fb3f810dff6361892cf044364b856e69c0` | `61db8eb1a1f287bbe58c3e72eb05d4fb3f810dff6361892cf044364b856e69c0` |
| `ArithmeticCarrierRadix2011` | `5d49d2dc9af2bbd3b694b035d6cdd408755ad94835fc498241c3bacf71a1e119` | `5d49d2dc9af2bbd3b694b035d6cdd408755ad94835fc498241c3bacf71a1e119` |

Eight probes pin each phase target and all three client objects. The 19 target namespace names, printed types/axioms (165 lines) and sampled simp/instance registrations (28,977/13,172 lines) match byte-for-byte. These checks do not establish proof-body equality or equality of all persistent extensions.

Direct source-matched project-provider associations are:

- `ArithmeticPellFirstIndex`: source `5d0c42fb3e4dd68cd527f634b911ce9bcfa4a1722f0f6d28147203338dd977d3`, object `24290ef5a4d3a3979a2c107320694d9cbbd1853655ca222a73750d4b5b181b4f`, producer `/dev/shm/firstindex-bound/final-refresh-records.json` (record SHA-256 `d4657ba153c11c7f631b4fb69c9744fc804a2e69105186bf62a33698ea7cf7ba`).
- `ArithmeticPow`: source `d7f033c291d70c5078eacd33c5ce25334f0d64b1bcc8be66e449e88a5b1d7e00`, object `a46405c9e2a29f37da4c6e0ff917d17793da86e9c669602de2fe40b0b55dcf23`, producer `/tmp/pow-perturbation/final-records.json` (record SHA-256 `1412171380c5eb24bb10d284aaff5d237893c7df4ceb877eddac3d7d458fc140`).
- `ArithmeticCarrierSoundness2011`: source `60a28e45d4f0c1776bd7f72cd24197c1c35e1f45abfc9f71f2fefd610cc72c66`, object `a9b3588787c4ecd29e1d7a16a29d39d8174a48268f4202ba104185b5c4247070`, producer `/dev/shm/firstindex-bound/final-refresh-records.json` (record SHA-256 `d4657ba153c11c7f631b4fb69c9744fc804a2e69105186bf62a33698ea7cf7ba`).
- `ArithmeticRadixAlignment`: source `e0ef467294c6223e4cf0dc986b4943c495edd166fb9f2c956360c84f7c6381b4`, object `212a7ec4ccb23469e596e66cb08690a3395486c6a4562ca5c2488b6424d1c8fa`, producer `/tmp/radix-positivity/final-records.json` (record SHA-256 `eb68266ab3da1636cccdbc9b2d94ce6044cf3abe637d56bcea7f03461eaea30a`).

The final client records sample the baseline workspace source path for the changed target; the final target build separately links its actual source snapshot and object. Other project, Foundation and Mathlib transitive dependencies remain cached; no complete source-current closure build is claimed. Raw logs and compiled objects are not included.

Temporary external evidence paths and SHA-256 hashes (they may no longer be available later):

- `/dev/shm/power-y-upper/baseline-records.json`: `931a538896cf697b69b3db335cc438f9b189a51507d3eedd525841bfad74f44a`.
- `/dev/shm/power-y-upper/final-records.json`: `85744de210129f565425ab89e31aaa87768f7c2a0bc959fb07d9f6828553051f`.
- `/dev/shm/power-y-upper/probe-records.json`: `b9c053286a26c18144c5888f232ead40aafbb21149843ac836686382af34b607`.
- `/dev/shm/power-y-upper/build.py`: `8d6f974d36a67cc60f0f326a9857a566fe9d78badb6063ad0afa817bb4900516`.
- `/dev/shm/power-y-upper/probe.py`: `c8cc6484dc4dfa4ed64c37e3b604dcdf393b8fbf3c68e7df0c45dbc121881813`.
- `/dev/shm/power-y-upper/audit.py`: `61d052b299cb3e4c32a77295d67366a607abd8703dbeece653520fa5d277731c`.
- `/dev/shm/power-y-upper/audit.log`: `6c64fcb5b000dcc17cbe03304bb5f1bac72d8c8f9281b3125a0211de4432db1c`.
- `/tmp/power-y-upper-peer-review.txt`: `220711f89274943a315d6946702f4f4075ec519b8ace8a62a31f987daf552743`.
- `/tmp/power-y-upper-peer-audit.py`: `fff139a486c2423f0ad3f3c95d739d2d9fe92803eaf129f032520eb26426ceaf`.
- `/tmp/power-y-upper-peer-audit.log`: `a3eceb77a1446ac874920df5e89d5eb9d4da636e27c00c574615700b28a31451`.

The independent postcommit review checked all paired builds and logs, exact first-provider and target-to-client object pins, probe comparisons, four provider associations and commit/parent snapshots. Full replay requires the external files, build environment and excluded compiled objects.
