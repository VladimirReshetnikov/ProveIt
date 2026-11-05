# Design for a coherent structured-endpoint join

This is a **source-interface and execution design**, not a driver, a launched
build or a checked endpoint. The read-only [`inspect.py`](inspect.py) pins
the two client sources, the 61-module extension driver and guards, its source
plan, and the 1,000-module base manifest. Its captured
[`observation.json`](observation.json) records their direct import lists and
expected axiom-report names, and observed the base RUNNING and extension
state absent. The source-inspection process exited 0; no Lean was invoked.
Its `NOT_AUTHENTICATED_OR_LAUNCHED` readiness is deliberate.

The fresh base subsequently [completed with actual exit 0 and passed its
independent artifact audit](../../reviews/current14-fresh-base-independent/README.md).
The [v3 61-module extension](../../reviews/current14-extension-v3-terminal-independent/README.md)
subsequently completed with actual supervisor exit 0 and passed an artifact
audit. The two clients have not yet been built atop that extension; this note
does not claim a coherent structured endpoint.

## Preconditions and operator evidence

1. Observe the base watchdog's **actual outer process exit** and require exit
   0, base `PASS`, `CURRENT_AT_FINAL_CHECK` and no source drift. Run and
   review the pending independent 1,000-row source/object/log/guard audit.
2. Independently recheck the reviewed 61-module extension driver and pinned
   sources. Run its preflight, then the extension only after explicit process
   coordination. Retain an **outer extension process exit-0 receipt** with
   the exact extension state digest; the driver's own state file alone does
   not record an external observer's exit. Require 61 ordered successful
   rows and the extension's final guard authentication. Investigate any
   failure; do not treat an observation timeout as a failed or stopped job.
3. Reauthenticate the base and extension state, frozen and current source
   hashes, all base/extension output and companion guards, recorded direct
   imports and logs, selected package/Foundation provider and namespace
   shadow absences. The three extension-only Mathlib objects require the
   extra guards identified in the [extension plan review](../../reviews/current14-printed-port-extension-independent/README.md).
   Recheck these at the end. No unrelated historical project overlay is a
   substitute for the successful fresh base and extension.

The source graph for the [printed assembly](../current14-literal-port-assembly/Current14LiteralPorts.lean)
imports `DiophantineConsistency.CurrentKernel2011` and
`DiophantineConsistency.CurrentMaskRecipes2011`, both expected fresh
extension outputs. The [structured endpoint](../current14-structured-endpoint-draft/StructuredEndpoint.lean)
imports that assembly and `DiophantineConsistency.IPRAStandardCurrentEndpoint`,
the latter expected from the fresh base. Check each with the actual
compiler's `--deps`; explicit imports plus any implicit `Init` are the only
expected direct dependencies. Resolve all paths and companions against the
authenticated producers, not simply the first object with a matching name.

## Proposed isolated client runner

* Create a fresh, exclusive output directory and a frozen source copy after
  checking both current source hashes against the pins in `observation.json`.
  Never overwrite or copy in the earlier mixed-provider assembly object.
* Use a fresh **flat client object root** followed by the single coherent
  extension project overlay and the guarded package-only overlay. The
  extension project overlay already contains base-project symlinks and the
  61 freshly built project outputs. Reject project/Mathlib/Foundation/Init
  namespace shadows in the client root, reject external namespace shadows in
  the project overlay, sanitize Lean and dynamic-library environment
  overrides, and guard all direct imports and companions before and after
  each command. Compiler-reported path, module name, object hash and realpath
  must agree with the authenticated producer or guarded package input.
* Compile `Current14LiteralPorts.lean` first and `StructuredEndpoint.lean`
  second. Record source and runner hashes, exact commands and search path,
  process exits, full logs, object hashes and before/after guards. Compare the
  second client's direct assembly object to the freshly compiled first object.
  Require precisely the five named assembly axiom reports and the one named
  `Current14StructuredEndpoint.recipe_endpoint` report, reject errors,
  warnings and `sorryAx`, and allow only `propext`, `Classical.choice` and
  `Quot.sound` in the Lean metatheory reports. The reports do not add axioms
  to iPRA. Recheck all guards, logs and current source hashes at the end.
* A defensible initial resource policy is one Lean process at a time,
  `-M6000`, a 600-second per-command wall bound, sampled process-group RSS
  stop at 7 GiB, sampled `MemAvailable` stop below 10 GiB and sampled disk
  stop below 4 GB. Run with low CPU and I/O priority; do not kill an unrelated
  process. Samples are not hard reservations or proof of between-sample
  behavior. Preserve memory or timeout failures and only retry after a concrete
  source, environment or bound change. The earlier explicit-vector client
  exhausted kernel memory, so this existential approach may also fail.
* Require a complete terminal receipt from the coordinator, followed by a
  separate source/receipt audit and ideally a second isolated replay. Test
  rejection of running/stale/failed base or extension, source/object drift,
  missing or swapped companions, shadowed imports, forged axiom names and
  actual `sorryAx`, missing child/monitor samples, and existing output paths.
  Such controls must not launch Lean or modify the captured providers.

The proposed endpoint asserts a **Lean-level existential tuple** whose four
entries satisfy the mathematical recipes and whose associated iPRA formula
has the stated derivation. Its source has been [reviewed](../../reviews/current14-structured-endpoint-source-independent/README.md)
but has never passed Lean. The design does not imply that it will compile,
that the encoded ZFC predicate is a proof of consistency, or that TeX, PDF,
JSON, gzip or coefficient-byte semantics have been formalized. Full
package-transitive and dynamic-library provenance, transient mutations between
guards, and operating-system resource guarantees remain outside scope.

Reproduce the read-only interface observation with:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/current14-structured-endpoint-coherent-plan/inspect.py
```

The readiness and process-state fields are point-in-time and may change.
SHA-256: `inspect.py`
`a91f7fd160c120fbf11f0868465a50d601d5bf7fd68e85afb433f657cb4facde`;
`observation.json` `008d305ec006dc601f4f99bb4b9b3b2787264b8b9bfa266e5a5cbba87d81c36c`.
