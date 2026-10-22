# Checked CM215 endpoint and the three-induction refactor

This component binds the existing CM215 transport proof to the current complete
K215/ZFC endpoint and checks the proposed shorter proof of `KSeed222.seed_eqFree`
through every affected dependency of that endpoint. The source snapshot is pinned
to ProveIt commit `56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3`. Four large kernel
reductions use explicitly recorded proof-only batching changes to fit the
available memory; all current machine, program, certificate data, imports, and
public endpoint statements are retained.

## What is checked

The recorded run has three gates. `SUMMARY.json` and the detailed receipts under
`evidence/` record their results.

| Gate | Project modules | Additional modules / clients |
| --- | ---: | ---: |
| Current K215 endpoint, with four proof-only batching changes | 184: 180 byte-identical, 4 batched | 2 typed audits |
| CM215 transport and complete endpoint | 7 | 1 independent typed audit |
| Shorter `KSeedModel222` proof, including every affected project dependency | 10 recompiled | 4 endpoint / audit clients recompiled |

The last row reuses the other 174 baseline project modules only after verifying
their source, object, object-companion, and log hashes. It also rechecks the CM215
endpoint against the changed theory proof. No compiled project objects are
included in this source-only delivery.

The refactor driver builds one unified object directory: it creates verified
links to the 174 unaffected modules, then compiles the ten affected modules into
new files. This is necessary because Lean resolves an entire package through
the first matching package root. No linked baseline object is overwritten.

`source_scope.py` checks all 184 module hashes against the original pinned
snapshot and the four exceptions in `batching/sources.json`. The resulting
scope is embedded in the CM215 and refactor receipts. This is not represented
as a byte-identical replay of all 184 original proof sources.

The complete CM215 theorem is

```lean
SetTheory.BusyBeaver.ZFC.CM215Endpoint.blank_halts_iff_zfc_refutation :
  KDenseBridge.BlankHalts CM215.CoreBridge.machineCM215 ↔
    BProv ZFCax_s [] Form.fBot
```

The independent client `CM215.IntegrationAudit.exact_finite_run_endpoint`
spells out the machine predicate, avoiding an opaque reading of the wrapper:

```lean
(∃ t : Nat, (CM215.CoreBridge.machineCM215.run t).state = none) ↔
  BProv ZFCax_s [] Form.fBot
```

`CM215Endpoint.nonhalting_iff_zfc_consistency` and
`CM215.IntegrationAudit.exact_nonhalting_endpoint` give the corresponding
negations. No consistency premise is assumed. The machine has type `Machine 215`,
and the independent client checks by `rfl` that its table has `215 * 2` binary
rows. The endpoint axiom reports contain only the established Lean principles
`propext`, `Classical.choice`, and `Quot.sound`; the checking scripts reject
`sorryAx`, `ofReduceBool`, and any other reported axiom. The table-length theorem reports `propext`.

These are external Lean proofs relating an exact machine to the repository's
finite ZFC proof predicate. The interpretation as a mathematical ZFC
nonhalting/consistency equivalence uses the inherited foundational calibration.
This component does not construct a new internally encoded ZFC derivation of
the entire equivalence, prove unconditional nonhalting, or establish a lower
bound on the number of states.

## What is new and what is inherited

The seven CM215 modules are inherited unchanged from the current repository's
`k215-transport` proposal. In particular, `CM215Endpoint.lean` was already
supplied as an integration wrapper, with a comment saying that the earlier
standalone packet did not freshly compile it. That historical comment is
preserved. This component completes its compilation against the exact current
K215 closure, adds `CM215Audit.lean`, and supplies the independent complete
verification receipts and portable rebuild scripts. The underlying marker
idea, table, and transport lemmas are not claimed as new here.

The refactor in `calculus/REMOVE_THREE_INDUCTIONS.patch` is also an existing
proposal, from
`k225-formal/verification/k215/simplification/proposals/affine-cores/calculus/`.
It applies exactly to the pinned source. This component supplies its checked
integration and recompiled dependency closure; it does not claim authorship of
the proposal. The KSeed refactor makes no generator change.

The four batching proofs are an application of the quarter-block technique
already present in the normalized and automatic-certificate proposals. They
replace only the proof bodies of `KSource215FwdCheck12` through `15`, each of
which checks 140 entries. Four private `decide +kernel` lemmas check 35 entries
each; a small Boolean equality recombines them into the unchanged public
theorem. Every quarter is checked by the kernel. No native-reduction axiom,
checker bypass, new certificate, or new program is introduced. The original
sources, unified patch, exact source exceptions, and technique attribution are
included. Batching increases these generated proof modules' source size; the
separate `KSeedModel222` refactor below is the measured source-size saving.

A small companion generator patch makes regeneration retain those four proof
bodies. It leaves `partition_source()` byte-identical and adds a separate
quarter-batching postpass in `write_partition()`. The original partitioner and
modified writer were replayed on an exact fixture reconstructed from the
pinned source files: all 18 emitted modules matched, with 14 original modules
and four checked overlays. The fixture, original and modified generator, patch,
verifier, and receipt are in `batching/generator/`. This check covers the
partition/writer stage; full certificate inference was not rerun.

The refactor removes the recursive helper proofs `enc_pos`, `enc_dec_enc`, and
`eqFree_dec_enc`, and replaces `derivable_bundle` with
`derivable_named_bundle`. It first proves derivability of a named bundle, then
uses the existing semantic encode/decode theorem in the already-required
irreflexive model. The local positivity fact for a doubly negated formula is
proved directly from pairing-code bounds. This removes three structural
inductions while preserving the public `seed_eqFree` statement and both exact
machine endpoints. Four old helper names are dropped or replaced; this is not
a claim that all possible clients of those helpers retain their API.

`KSeedModel222.lean` decreases from 269 lines / 11,711 bytes to 234 lines /
10,436 bytes, with the same imports. Line and byte counts include comments and
blank lines. A structural induction for `th_eqFree` remains.

## Why CM215 is an easy next candidate to certify

CM215 changes six binary transition rows of the existing K215 machine while
retaining 215 working states. Its local proof uses a state map that sends old
control 170 to new control 52 and fixes the others, together with three marker
conditions on nearby tape cells. A simulated old step takes one new step except
for four local cases, which take three. At simulation boundaries the whole tape
and head position agree. Positivity of the simulation lengths and deterministic
execution provide both halting directions even though the state map is not
injective.

The mathematical transport applies to arbitrary tapes and head positions from
the designated initial control; it is not a claim of equivalence from every
arbitrary internal control. The independent finite certificate checks 1,710
admissible radius-one cases, including the four exceptional cases. The Lean
proof checks the corresponding literal table and exact machine bridge, and the
complete endpoint imports the existing foundational proof instead of duplicating
it. Thus CM215 has a small *incremental* correctness proof; the full inherited
K215 closure remains a dependency.

The transition-table SHA-256 values are:

| Table | SHA-256 |
| --- | --- |
| `cm215/baseline215.tm` | `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090` |
| `cm215/marker215.tm` | `1f4f084f7293e2b042d5746039f793ff72ed429083b504970c939a5515e666cf` |

`cm215/sources.json` binds the inherited files to the pinned repository.
The historical commit field emitted by the inherited Python marker checker
describes that original packet; it is not the current-snapshot provenance.
The current source bindings are in `base_sources.json` and `cm215/sources.json`.

## Reproduce from the bundled source

Requirements are Linux or another POSIX platform with Python 3, `fcntl`, and
the official Lean **4.32.0** distribution, including its adjacent `lake`
executable. The recorded compiler is commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. The build needs no network access,
mathlib installation, or preexisting project cache.

Run from this directory, supplying the installed Lean executable and a new
output directory:

```sh
python3 reproduce.py \
  --lean /absolute/path/to/lean-4.32.0-linux/bin/lean \
  --out /absolute/path/to/new-verification-output
```

The default source is the included minimal `source/` snapshot. Alternatively,
pass `--repo /path/to/ProveIt`; all 188 required snapshot files must have the
pinned hashes. The 188 files are the 184 project modules, two original endpoint
clients, original verification driver, and toolchain selector. The driver
constructs an isolated workspace, discovers its import closure, and refuses
source/toolchain/object/dependency mismatches on resume. Only Lean's distributed
libraries are external to the project snapshot.

The compiler memory cap is 12,288 MiB for the baseline and refactor gates, and
4,096 MiB for the small CM215 transport. This is a cap, not a claim that every
module uses that much memory. A deliberately lower 4,096 MiB cap failed on the
baseline's `KSource215Data`; its later pass at the repository's supported cap
is recorded. Subsequently, the original unbatched `KSource215FwdCheck12` was
killed with exit 137 after 86.347 seconds under the environment's 8 GiB cgroup
limit, despite the larger Lean cap. At that point 155 unchanged project modules
had passed. Their sources, dependencies, logs, and object companions were
verified before reuse, and the original partial receipt was preserved.

The batched replacement of that same public theorem passed in 58.841 seconds.
Its highest sampled process memory high-water mark was 2,232,025,088 bytes
(about 2.08 GiB). `batching/memory_observations.json` records the sampling method
and results for the four modules. These samples are observed lower bounds on
per-process peaks, not a process-final peak measurement or a full-build speed
comparison. Original chunks 13–15 were not separately attempted after the
chunk-12 resource kill; the same transparent batching was applied proactively.
Large source-certificate chunks take much longer than the local CM215 proof.
The scripts serialize compiler invocations through
`/tmp/proveit-k215-proof-build.lock`.

`reproduce.py` does the following:

1. Hash-checks and copies the pinned source snapshot into the fresh output.
2. Checks the generator's 18-file fixture, then applies the four explicit
   proof-only batching overlays and the one-line
   driver diagnostic fix in `quiet_identity.patch`.
3. Builds all 184 baseline project modules and both typed endpoint audits,
   checking the 180-original / 4-batched source scope.
4. Builds the seven CM215 modules and the independent typed audit.
5. Rebuilds the refactored theory module, all nine affected project dependents,
   and four endpoint/audit clients with the altered modules first in `LEAN_PATH`.
6. Exercises the corrected baseline driver's verified resume path.

The one-line driver fix adds Lake's quiet option to compiler-identity queries.
Previously, first-run manifest-initialization diagnostics could become part of
the recorded compiler identity and cause an unchanged compiler to be rejected
on resume. The fix suppresses those diagnostics, preserving the actual compiler
version and binary/library hashes. It does not change any Lean proof or theorem.

The two small independent Python table checks can also be rerun:

```sh
cd cm215
python3 check_lean_binding.py
python3 check_marker_certificate.py
```

The kernel-checked Lean theorems, rather than the Python finite checks, justify
the complete machine endpoint.

To rerun only the generator postpass check, using the bundled pinned source:

```sh
python3 batching/generator/verify_generator.py --out /absolute/path/to/new-generator-check
```

## Evidence and integration

`evidence/baseline/` contains the original driver's complete inventory,
per-module attempt logs, resumptions, toolchain hashes, completed-object hashes,
and final verification receipt. `evidence/cm215/` and `evidence/calculus/` contain
the later gate receipts and logs, including printed axiom dependencies. Historical
absolute paths in these receipts identify the recorded run; the portable scripts
calculate paths afresh when reproducing it. An interrupted module is counted
only after recompilation succeeds and its completed record is written.

`evidence/original_partial_baseline/` preserves the original 155-pass inventory
and completed-object record before batching, together with the original failed
chunk-12 source and resource-failure record. The bundled `source/` contains the
original 188 pinned files, including the original four proof bodies.
`batching/` contains the four replacements; reproduction applies them explicitly.

Early symlink-root and noisy-toolchain-identity failures are retained under
`evidence/initial_failures/`; the lower-memory failed attempt and successful
resumptions are present under `evidence/baseline/`. They are not counted as
successful checks. `evidence/cm215_initial_client_failure/` preserves an initial
error in the new independent client: it omitted `open SetTheory`, and its
literal-table length check exceeded Lean's default recursion-depth limit.
The corrected client imports that namespace and sets `maxRecDepth` to 10,000;
the complete eight-module CM gate was then rebuilt. No inherited CM proof was
changed. `evidence/calculus_initial_import_failure/` preserves the initial
overlay-layout failure, before the refactored proof was elaborated: an empty
`BusyBeaver` package directory shadowed the baseline package root. The corrected
driver uses the unified object directory described above. No compiled objects,
local toolchain, or unrelated repository files are bundled.

For incorporation, apply the batching and calculus patches to the pinned
repository source, apply the generator postpass patch to retain batching on
regeneration, apply the one-line driver fix if desired, and place the flat CM215 modules in a
Lean source root reachable from the existing project. The recorded builds use a
separate source root so that this delivery need not choose a permanent module
namespace or repository layout. Upstream notices and licenses are preserved in
`licenses/`.
