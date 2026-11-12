# Root74 slim source route: refusal-only preflight

`inspect.py` is a read-only observation tool. It has **no launch mode** and
always exits nonzero with `can_launch: false`, including when its sampled
resource checks pass. On inspection error it returns a separate refusal. It
never invokes Lean, creates an output tree, allocates the shared slot, or
modifies provider evidence. The proposed output name is a non-reserved candidate,
not an authorization or a claim that an output directory is safe to create.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B research/ordinary14-root74-slim-no-lean-preflight/inspect.py
```

The JSON output records the exact identity and realpaths of selected committed
source/review evidence, retained P72/base metadata and key object files,
toolchain, Init, and manifest; compares all 159 overlay/original snapshots and
1,127 lexical project-source hashes; samples `/tmp` free space and Linux host
available memory; lists observed Lean PIDs and process-scan errors; and checks
13 historical output/companion suffixes for 159 draft, two proposed FreeJ and one DiscreteOrderedRingFacts
module names under the specified candidate roots. The latter reports same-name
paths and resolutions: an observed duplicate is not, by itself, proof of an
incorrect Lean resolution. It does not check all source or provider names, all
external and implicit Init search candidates, or full provider/package ancestry.
Selected pin matches and path observations are not immutability guarantees.
The output is a point-in-time observation, not a readiness receipt. Capture it
outside retained evidence if desired; the program itself writes nothing.

The separate root74 provider survey and its receipt are pinned, but
this inspector does not replay all of their historical companion checks. Its
lexical cut names `FreeJ13`, `FreeJ13Halt` and `DiscreteOrderedRingFacts` as
additional source candidates, not a complete build plan.

The retained single candidate route is the P72 PASS overlay with its linked
fresh base, guarded package, and the pinned v4.32.0 toolchain. The failed
retry roots have different same-source `ModelDifferenceRing` objects and must
not be added. A future runner must have a separately reviewed exact ordered
search path, source and companion plan, per-stage expected object resolutions,
immutable hashes or protected snapshots for the complete transitive package,
project and runtime ancestry, and explicit policy for dynamic dependencies.
It must recheck source, symlink targets, inputs and companions immediately
before and after each stage, and reject unknown/fallback paths. Neither the
lexical source graph nor this inspector substitutes for guarded `lean --deps`.

A future implementation would require independent prelaunch review and an
externally allocated exclusive Lean slot. A `/proc` scan is not an atomic lock;
a local advisory lock can coordinate only cooperating processes. Create a new
isolated source and output root only after authorization, prove all 159
materialized source bytes and the complete ordered output plan, reject all
existing output/companion names and alternate search candidates, and retain
all existing evidence. Check exact toolchain, Init and complete ordered provider
inputs before staging. Compile one stage at a time with the established guarded
resource monitor and independently auditable receipts: source and actual input
hashes/realpaths, dep resolution, all guard samples/errors, command/exit, output
and companion hashes, postflight changes and axiom reports. An absent or
ambiguous dependency, process, monitor, output, resource or postflight result
must refuse or stop; do not overwrite previous evidence.

The existing P73 guard requires `/tmp` available bytes **strictly greater than
5,100,000,000**, host `MemAvailable` at least 10 GiB, stopping at sampled
session RSS at least 4 GiB, 180 seconds per child, six hours total, and 0.2
second sampling. Guarded `lean --deps` and every compile require the same
resource checks, live-process/descendant discipline and slot allocation.
Sampling is not a hard kernel ceiling and cannot rule out unobserved spikes or
escaped processes. Before any actual run, independently verify that the monitor
covers descendants, handles monitor/proc errors fail-closed, and enforce all
these limits. No executable build runner is supplied or approved here.

This tool makes no Lean elaboration, provider-coherence, iPRA, physical-byte or
PDF claim. Existing unconditional blockers remain even if available disk rises.

Independent source review: [root74 refusal preflight](../../reviews/ordinary14-root74-slim-no-lean-preflight-independent/README.md).
