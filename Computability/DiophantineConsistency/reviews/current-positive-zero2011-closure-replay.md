# Completed current-source closure validation

Result: **PASS** for the exact source snapshot
`09eaa57ae5b80130ddb0aa5344f71e638ebb3e97`. The original driver ran once,
exited 0, and processed all **361** selected custom modules: **191 fresh
compilations and 170 source/object-authenticated cache reuses**. No module
failed, no command was retried, and no source or shared object was edited.

This is the execution receipt for `current-positive-zero2011-closure-plan.md`.
ROOT fully read and explicitly approved the pinned 196-line planner and
163-line driver before execution. I also read the complete two newly missing
prerequisites (`QuadraticFiber`, `TotalDegreeBound`) and the three incoming
modified sources in this closure (`NativeCyclicRotation`, `NativePellPower`,
`NativePellStepDown`) before launch. Unchanged modules retain their prior
author/peer mathematical-review boundaries; this replay is not a new
independent mathematical review of every source.

The serial run used `lean -M6000 -j1 -DElab.async=false`, with the shared
project object directory removed from `LEAN_PATH`. The private run is
`/tmp/current-positive-zero2011-closure-validation-20261026a`; unified-exec
session **48150** reached terminal exit 0. It ran from **19:30:32 to 20:06:38
UTC on 2026-10-26**, about **2,166 seconds**. The highest recorded RSS was
**6,086,664 KiB**, in `WangTiles942Data`, under the unchanged Lean `-M6000`
configuration. No observation timeout was treated as failure or used to
restart a live process.

The final source/output/toolchain/evidence/external-boundary rehashes passed.
After completion I separately rechecked all 361 recorded output hashes and
all 191 fresh exit codes, log hashes, and timing hashes. Both formerly absent
prerequisites passed. Fresh `PellRatio90` and `NativeHalfBinomial` were built
inside this closure; the older shared versions and the earlier private leaf
overlay were not used as custom prerequisites.

The target main log is empty. Its focused checks printed exactly these six
reports, each containing only `propext`, `Classical.choice`, and `Quot.sound`:

- `CurrentPositiveZero2011.packingData`
- `CurrentPositiveZero2011.not_conZFC_positive_zero`
- `CurrentPositiveZero2011.positive_zero_iff_not_conZFC`
- `CurrentPositiveZero2011.no_positive_zero_iff_conZFC`
- `CurrentPositiveZero2011.no_thirteen_positive_zero_iff_conZFC`
- `CurrentPositiveZero2011.not_conZFC_simultaneous_thirteen_zero`

| Target artifact | SHA-256 |
|---|---|
| Main source | `cdbd33de5ccb176c253d1cfca41f1d34b8d0121790a4b06c5d38d461b72b648c` |
| Checks source | `79a6dc417560cec163767f9d5af69c4ef647fb081b433ab0abd830dbf41ee44b` |
| Fresh main object | `629d9b6e21a33c0ddaa9d61e067a3c47e0435cb146fb30f6bab259b4026b68c0` |
| Fresh checks object | `c74a78cec6457027befbf2219859e18df01117875ba4dff0c11a8b5ed34524b3` |
| Checks log | `43722bf5203ae1996c3c1cb2099b4a770a190a56364d61114b9a4cc951a3fbcc` |

The target object hashes equal the earlier target-only replay. That equality
alone did not authenticate its dependencies; the present closure run supplies
the additional source/rebuild evidence. Among the 189 fresh modules with an
old shared object, 106 fresh object hashes differ from those observations.
No old object was restored to force equality, and byte differences are not
being assigned a single inferred cause.

Existing prerequisite logs contain linter/deprecation notices and four
large-exponent non-evaluation notices. These were preserved, not suppressed.
All compilers exited 0; no `sorry` declaration warning or error diagnostic
appeared. Besides the six target audits, three existing prerequisite modules
printed standard-only axiom reports.

Durable evidence is in the sibling `current-positive-zero2011-closure/`
directory. The scripts and manifest retain their previously approved hashes.

| Execution evidence | SHA-256 |
|---|---|
| `execution-state.json` | `e43280769624245f9caa2c9f9a85585adfec9ea71f3b0de06d6e35fa6ec44ac9` |
| `validation-driver.log` | `2467471feb7c993efbe2e63e3ab72a6c0d228b40e569716d056690c0db269b14` |
| `execution-logs.zip` (382 log/timing files, 84,187 bytes) | `ea0d83e409e3b824a9dd9452be80e4832e4d7d262306caff10b2a8d8b96f98e3` |
| Preserved Bridge cache receipt | `faca1ea428aee9e862699500b093bc7c1dda7642e03e40188d41495d320dad86` |

The log archive contains only generated text logs/timings, no executable
research code or compiled objects. Every archived file was checked against
its execution-state hash; archive integrity was checked after creation.

The precise scope remains the planned mixed closure: the unchanged machine
and Bridge cache is authenticated by earlier exact-source/object evidence;
installed external packages/toolchain remain an explicit precompiled boundary.
This is not a fresh rebuild of all machine or external-package modules. It
validates the external Lean equivalence for the actual fixed polynomial and
the actual syntactic consistency predicate, including all three accepted
thirteen-variable forms and their simultaneous positive witness. It neither
asserts consistency nor supplies an encoded internal-ZFC or HA derivation.

Incoming changes fetched after this snapshot, including the five proof-source
changes at `5a1db2b1f5`, were deliberately not merged during the run. A later
affected-source refresh must be recorded separately and cannot retroactively
be called part of this 361-module snapshot. My authorship of several native
and controller dependencies is disclosed in the prior endpoint peer review.
