# Planned current-source validation of the positive-zero endpoint

Prepared by `complemented47_review`. **Plan only: the build driver has not
been executed.** ROOT requested a complete source-authenticated custom import
closure before accepting a post-merge replay of
`DiophantineConsistency.CurrentPositiveZero2011` and its focused checks.

The approved source snapshot is
`09eaa57ae5b80130ddb0aa5344f71e638ebb3e97`. Every selected source was compared
byte-for-byte, by SHA-256, with its blob at that commit. Later documentation-only
commits are allowed; a changed selected source is not. The new untracked
object-language endpoint is outside these targets and is not included.

## Exact scope and cache boundary

The recursively parsed, topologically ordered closure contains **361 custom
modules**, not the complete project umbrella. Its proposed actions are:

| Action | Modules | Scope |
|---|---:|---|
| Authenticated reuse | 170 | 156 `BusyBeaver`, 8 `BoundedZFCConsistency`, 3 `FirstOrder`, 1 `ZF`, and `DiophantineConsistency.Computability`/`Bridge` |
| Fresh source replay | 191 | 161 `DiophantineConsistency` and 30 `Diophantine` modules |
| Precompiled external boundary | 59 direct imports | Installed Mathlib/package/toolchain modules; not a fresh transitive external-package build |

For all 170 reuse candidates, **both** the current source hash and current
primary object hash match a pre-existing authenticated receipt. Every custom
dependency of a reused module is itself in this closed reuse set. No custom
cache companion exists for these candidates. No module is accepted merely
because an object exists, its timestamp is recent, or its interface is stable.

The selected cache evidence is:

- `machine215-current-closure-completed.json`, SHA-256
  `95734ad98c79b4413c83ccff3ffa2060f4b008878a7782de1ba9dacb8e98bd73`.
  This retains its original 104-cache/64-fresh history and explicit later
  `KZip` rebuild. The current 168 source/object pairs all match that completed
  receipt. I read the original driver and full build/reauthentication account.
- `/tmp/diophantine-bridge-identical-cache-receipt.json`, SHA-256
  `faca1ea428aee9e862699500b093bc7c1dda7642e03e40188d41495d320dad86`.
  Its two recorded copied objects and exact sources match for `Computability`
  and `Bridge`; the remaining dependencies are covered by the machine receipt.

The other 191 modules are conservatively fresh. This does **not** mean that
every one lacks an earlier author or peer receipt: those numerous heterogeneous
receipts have not been exhaustively harvested into a reusable transitive
certificate. In particular, earlier target-only replays do not establish a
current dependency closure. Fresh replay here also avoids accidentally selecting
the known older shared `PellRatio90`/`NativeHalfBinomial` objects.

The missing shared custom objects are `QuadraticFiber` and `TotalDegreeBound`;
their current sources and import paths are included. `QuadraticCoding` and the
endpoint clients will be rebuilt, so an old client object cannot hide the new
prerequisite. Of the existing sources changed by incoming proofs, exactly
`NativeCyclicRotation`, `NativePellPower`, and `NativePellStepDown` occur in this
closure. These changes reach **82** selected modules, including the endpoint.
The manifest's broader comparison with pre-merge `c77fd6ac…` lists ten changed
paths: these three modifications plus seven locally added endpoint/construction
files. It distinguishes modifications from additions.

## Frozen planning artifacts

All artifacts are in `/tmp/current-positive-zero2011-closure-plan/`:

| File | Size | SHA-256 |
|---|---:|---|
| `plan.py` | 196 lines | `fce21bcc246d82485ef1cf99510eedcce4bf9d90e21c0ae34681ea385cac9a34` |
| `build.py` | 163 lines | `52912bc40b06ae6b5e5a621aa4b478ea6e06e5c8cbd7bc15a2471d02f16df8aa` |
| `manifest.json` | 512,212 bytes | `444272b7464611dcc25e4c9ccca84443300a5c54ec8d87d86bc44999131b3a21` |

Exact durable copies of all three files, with these same hashes, are saved in
the sibling `current-positive-zero2011-closure/` directory. That directory is
a provenance bundle, not a new project build hook.

I read both complete scripts and all subsequent edits. Only the read-only
planner was run. Both scripts parse as Python, and a separate non-building
validation rechecked the complete topological order, all 361 source hashes,
all 170 selected object hashes, and closure of the reusable dependency set.
The initial planner attempt correctly rejected a later documentation commit;
the final version checks the approved commit's ancestry and each exact source
blob instead of requiring unchanged `HEAD`. No Lean compilation occurred.

The manifest includes each module's source/object hashes, imports, evidence,
action/reason, the compiler and `Init` hashes, toolchain/lake configuration,
and the 59 direct external sources/objects with their 118 companions. External
files are pinned for drift detection, **not** presented as independently
recompiled or transitively source-authenticated packages. Installed external
dependencies remain an explicit trusted boundary.

## Proposed execution behavior

The driver creates a new private `/tmp/current-positive-zero2011-closure-*`
directory and symlinks only the 170 authenticated custom objects. It removes
the shared project object directory entirely from `LEAN_PATH`, rejects external
paths that shadow a custom module, and builds the other modules in dependency
order with `lean -M6000 -j1 -DElab.async=false`. It never invokes `lake build`,
executes research programs, copies package caches, or installs shared objects.

Every command has an exit code, timestamp, log hash, timing/RSS record, source
hash and output hash. The driver checks direct dependencies around compilation
and rehashes all selected sources, outputs, toolchain/evidence and direct
external bundles at completion. It stops on the first failure and refuses a
silent restart in an existing run directory. Observation timeouts are not
compiler failures; the recorded live process must be monitored to completion.
The final check requires exactly the six named endpoint axiom reports, each
restricted to `propext`, `Classical.choice`, and `Quot.sound`.

Existing primary objects for the fresh set total **124,641,712 bytes**
(about 119 MiB), excluding the two missing objects and any newly generated
companions. This is an estimate, not a disk bound. The driver requires that
estimate plus a 512 MiB free reserve initially, and stops before another
compile if free space falls below 256 MiB. It does not clean unrelated files.

After ROOT reads and approves the frozen driver, the proposed command is:

```text
python3 /tmp/current-positive-zero2011-closure-plan/build.py --manifest-sha256 444272b7464611dcc25e4c9ccca84443300a5c54ec8d87d86bc44999131b3a21 --run-dir /tmp/current-positive-zero2011-closure-validation
```

No success claim is made now. A successful run would establish the stated
mixed authenticated-cache/current-source closure and fresh endpoint check,
not a fresh rebuild of every machine or external-package module. It would
remain an external Lean equivalence for the actual fixed polynomial and
syntactic `DiophantineConsistency.ConZFC`; internal object-language ZFC
formalization and global equation minimality are separate claims. My prior
authorship of several native/controller prerequisites remains disclosed in
the existing endpoint peer review; this plan does not independently re-prove
those modules' mathematics.
