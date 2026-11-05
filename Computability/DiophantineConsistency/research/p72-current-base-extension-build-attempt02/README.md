# P72 current-base extension: corrected attempt

The first [attempt](../p72-current-base-extension-build/README.md) stopped in
setup before Lean: it incorrectly required 1,016 base file links. The actual
authenticated current14 base has 1,000 regular files; 1,016 was the size of a
separate base-plus-106 overlay. This runner differs only in the corrected
count and a fresh output directory. Frontier independently checked the diff
and base inventory. The runner SHA-256 is
`04361b39845447f6f2a45f8997a26b6c58e7e695f1bae5dc0008f617f2972322`.

The no-Lean preflight returned exit 0 in actual session 43808; its retained
[output](preflight.json) SHA-256 is
`49356de344c045f2b949843df4bc6066c90d215c938b1be629b51dee991d8ac7`.
Actual build session 92122 was launched; supervisor PID 181752 was observed
running, and the first stages completed. The snapshot contains all 681 new
source files (snapshot manifest SHA-256
`4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8`).
These are **point-in-time running observations**, not a terminal success or
an iPRA endpoint claim. Per-stage progress and logs reside under
`/tmp/p72-current-base-extension-attempt02-20261105/` while it runs; the
actual outer session exit must be observed separately.

The single-worker Lean processes use a 4,000-MiB heap cap, sampled 5-GiB
session RSS threshold and 10-GiB host-memory floor, 180-second timeout and
5-GB disk precheck. Sampling and the provider/source observations have the
limits documented in the first packet; in particular, this is not a full
package-transitive or dynamic-load audit.

The run subsequently completed: actual outer session 92122 returned exit 0
with `PASS all 681 P72 source-snapshot extension modules`. Its retained
[terminal progress](terminal/progress.json) SHA-256 is
`f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a`.
The deterministic [evidence archive](terminal/stage-evidence.tar.gz)
contains all 681 source snapshots, row receipts and both logs per stage;
its SHA-256 is
`884525ff2103d805cdb8b891fedaa9cf8b9be4bc5f1c67efbf8e95353b533541`.
The runner completed its final source, object, direct guard, base and survey
rechecks. The P13 and P14 endpoint objects have SHA-256
`ef08b9c68b1f7a770f698b14fc65d221c7db399d924b69c9a3aa9e978464a48a` and
`ca06ffe7d590b250f7585ae75f7aa4a8d9c6e8a12b14096dc56ec55caeed41aa`.
Their [endpoint logs](terminal/0679-compile.txt) and
[P14 reports](terminal/0680-compile.txt) contain only `propext`,
`Classical.choice` and `Quot.sound` for the explicitly reported theorems.
Independent terminal audit is pending. This result proves the represented
standard iPRA endpoints on the recorded fresh project closure; the external
graph/file and fixed-byte degree checks are separate and the sampled and
package-transitive limits above remain.
