# Current K215 endpoint closure: authenticated reuse and serial rebuild

This review records a completed current-source endpoint check, started and
finished on 2026-10-25. All 168 modules passed, including the 64 missing
modules compiled freshly. The final state is in
`.lake/machine215-current-closure/state.json` at the repository root.

The target is `BusyBeaver.ZFC.KEndpoint215`, including its theorem
`SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation`.
The current transitive project-source closure contains 168 modules. I
independently compared every source file with the corresponding file in
`/home/codex/.codex/worktrees/62ff/Proofs`: all 168 are byte-identical. The
topological order is checked against each current source's import list;
the only external imported module is the toolchain's `Init`.

The approved reuse boundary is 104 existing compiled objects from that
exact-source worktree. The other 64 modules are compiled from the current
checkout, sequentially, using `lake env lean -j1 -o OBJECT SOURCE`. No C
generation or `lake build` dependency scheduler is invoked. Any existing
`.olean.private`/`.olean.server` companions are copied with and hashed
alongside the corresponding cached `.olean`.

This is a mixed cache/rebuild check, not a fresh rebuild of all 168 files.
The cache objects are not taken from the phase-26 or phase-27 candidate
closures: phase 27 has 43 differing current sources and lacks
`KQ1ReplacementNative`, while phase 26 has 39 differing sources and lacks
that same module. A matching `KEndpoint215.lean` alone does not authenticate
either older endpoint object.

The Lean toolchain is exactly `leanprover/lean4:v4.32.0`:

- Compiler SHA256: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- `Init.olean` SHA256: `d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e`.
- Authored driver SHA256: `dd3c83b7fac9fed4629e7d5d73b50e145cace86bcb1e25ba1a81a4eed42fc56d`.
- Complete plan SHA256: `7a02540977e35b613a2a42133c1efbaaca1641c8086e3bdc6d8048057ff1f155`.

The driver and complete plan are respectively
`.lake/machine215-current-closure/build.py` and `plan.json`. The plan pins
every current source, every selected cache object, and the dependency
order. I read the complete newly authored driver before executing it; no
incoming cache build scripts were executed. Source hashes are rechecked
before and after each module, cache objects before copying, and the full
source closure and toolchain again at successful completion. The driver
holds an exclusive lock, records individual compiler exit codes and log
hashes, stops on the first failed module, and refuses a silent restart
when a state file already exists.

The original execution had unified-exec session **30231**, driver PID
**535234**, and persistent output in
`.lake/machine215-current-closure/driver.log`. The state file records the
active child PID, exact argument vector, log path, and completion history.
Observation timeouts must not trigger a restart or a duplicate build.

## Completed run and fresh endpoint audit

The original driver completed with status `PASS` and exit code 0 after
2489 seconds. Its final totals are **104 authenticated cached modules and
64 freshly compiled current modules**, with no failed module or restarted
driver. The final source/toolchain revalidation passed.

| Artifact in `.lake/machine215-current-closure/` | SHA-256 |
|---|---|
| state.json | dda2a880165baa31ad86bf53364b27f519dc18c396e07228075efd7a8fa9bb57 |
| driver.log | 01130ed431d5a95a8aa3fba0c70c108752fa65342f54beb705f65fa7e2215dff |
| EndpointAudit.lean | 8c8399852b680aaab40886892fe8ad1cc6c1f7b29716209231e2c006ef32d173 |
| EndpointAudit.log | 99ec76eb139a0374f458bab79e271a67e511e3cba07cc96aed1fdae68aba368e |
| 168-BusyBeaver.ZFC.KEndpoint215.log | 3a8c6dd0c002f263f898f5ed37ab83586bc9a308c52522fea79b2b2aec2cb320 |

The prepared `EndpointAudit.lean` was freshly compiled after the driver
finished. It composes `DecimalMachine215.blank_halts_iff_dense` with the
current `KEndpoint215.blank_halts_iff_zfc_refutation` for the actual decoded
machine, then takes negations for consistency. All four axiom reports,
covering both KEndpoint215 endpoints and both decimal compositions, contain
only `propext`, `Classical.choice`, and `Quot.sound`.

Exact input source hashes:

- `DecimalMachine215.lean`: `da9e49c1a5f47a10d1f385810e1e89d2e3f4f25fc438dc85cf2184efdc3c719a`.
- `KEndpoint215.lean`: `77b71164cf3cac4303ab786852e58969bc5c7332c5261aecfc22a63d3a39dfc9`.

## Persisted decimal-machine theorem

The root agent then assigned the persistent composition, now freshly compiled
and frozen in these new files under `Lean/DiophantineConsistency/`:

| Module | Lines | SHA-256 |
|---|---:|---|
| DecimalMachineZFC.lean | 30 | 778af71680ec6aadd9858d30ace87c25012ac6b9dac02e2a483094401fc06107 |
| DecimalMachineZFCChecks.lean | 25 | 598220ac30d8d4700c0918974cf4658fe4fec7041d64ab4896b4badec47424d0 |

The two closed theorems are
`DecimalMachineZFC.blank_halts_iff_zfc_refutation` and
`DecimalMachineZFC.blank_nonhalting_iff_conZFC`. The latter uses exactly the
existing `DiophantineConsistency.ConZFC` definition imported from `Bridge`,
not a new consistency predicate. Both modules were fully read and freshly
compiled with `lake env lean -j1 -o ...`. Their focused checks cover the
underlying syntactic predicate and both directions needed to use the endpoint.
The checks log SHA-256 is
`3dd4f56474a0f14c725589ef395907d508fef25ac3cc42df77696126129d00ae`;
the two final theorem reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The actual decoder conjugacy needs only `propext` and
`Quot.sound`.

For the additional `Bridge` import, all 103 transitive custom-source files
were independently checked byte-identical to the 62ff worktree, with matching
toolchain and lake manifest. Only two missing bundles, `Computability` and
`Bridge`, were copied; no freshly checked machine object was overwritten.
That scoped receipt is
`/tmp/diophantine-bridge-identical-cache-receipt.json`, SHA-256
`faca1ea428aee9e862699500b093bc7c1dda7642e03e40188d41495d320dad86`.
This additional reuse does not change the 104/64 boundary of the machine
closure itself. This is an author/build receipt; independent review is a
separate step.

The current native Diophantine calibration and internal-ZFC equivalence
are separate obligations. This work checks the current machine endpoint
needed to compose the independently formalized decimal-machine decoder;
it neither proves the displayed equation unsolvable nor decides ZFC's
consistency.

## Subsequent object reauthentication and KZip replay

On 2026-10-26 UTC, ROOT's first full object reauthentication found exactly
one difference from the hashes recorded when the driver installed or
compiled each module: `BusyBeaver.ZFC.KZip`. That check stopped before
writing a successful receipt. The driver's final check covered sources
and the toolchain; it did not rehash every installed object. Consequently,
the original 104/64 totals describe the driver's actions and do not assert
that no concurrent job subsequently replaced an object.

The initially installed KZip object had SHA-256
`1230b602dbaba00b43662f984f143e466eb255ab27ffd3b4255706bca6e1e701`.
The later observed object had SHA-256
`2847c50892bafbe4e7a15442d5e07817f6499cad7cf9b19064e3c46e02040be8`.
Both were 454064 bytes. A read-only byte comparison found exactly four
differences, at offsets 446741 through 446744: the embedded absolute source
path's worktree identifier changed from `62ff` to `46be`. Independently
replacing the sole old source path in memory reproduces the entire second
hash exactly. This comparison wrote no compiled object.

The observed object's modification time was 2026-10-26 04:11:53 UTC,
during the driver interval 04:07:56 through 04:49:25 UTC. The adjacent Lake
trace records a compile of the current-worktree KZip source at that time.
No retained command log identifies which concurrent task produced that
object. Both peer agents report no explicit KZip copy or compile; one had
an authorized broad Lake build that could have rebuilt dependencies. That
possibility is not treated as established attribution. The KZip source
itself remained identical to the pinned source, SHA-256
`71edb0ca7a8cf160d9f8868f73c7ab52cffcd66301c35ad90f828cd4afb265a3`.

ROOT then read the complete current source, explicitly compiled KZip
freshly, and freshly replayed `DecimalMachineZFCChecks`; both commands
passed and the endpoint axiom reports remained standard. The new KZip
object is 457824 bytes with SHA-256
`5fc974ab21b7b445c2c8c195b447ccb4800d188498286a51b4acbf546255e0e6`.
The historical cache object was not restored to force a matching hash.

ROOT's completed receipt is `machine215-current-closure-completed.json`
in this review directory, SHA-256
`95734ad98c79b4413c83ccff3ffa2060f4b008878a7782de1ba9dacb8e98bd73`.
I independently rehashed all 168 sources and all 168 current objects
against that receipt after the replay: every hash matched. The resulting
claim is the original authenticated 104-cache/64-fresh run, followed by
the explicit fresh KZip and closed-endpoint recheck, not a fresh full
rebuild or an assertion that every object remained unchanged throughout.
