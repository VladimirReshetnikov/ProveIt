# Current K215 endpoint closure: authenticated reuse and serial rebuild

This review records a build in progress, started on 2026-10-25. It does not
claim a completed endpoint check. The current execution state is in
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

The original execution has unified-exec session **30231**, driver PID
**535234**, and persistent output in
`.lake/machine215-current-closure/driver.log`. The state file records the
active child PID, exact argument vector, log path, and completion history.
Observation timeouts must not trigger a restart or a duplicate build.

The current native Diophantine calibration and internal-ZFC equivalence
are separate obligations. This work checks the current machine endpoint
needed to compose the independently formalized decimal-machine decoder;
it neither proves the displayed equation unsolvable nor decides ZFC's
consistency.
