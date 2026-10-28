# Internal DAG loops: author checkpoint

26 October 2026. The controller agent authored and fully reread the final
187-line main and 55-line Checks, the exact executed driver and all six
unchanged prerequisite sources before the relevant execution. Final pair
PASS. Independent review/replay remains separate.

The generic transfer, two-destination copy and clear theorems use the actual
ArithmeticDagRun.IRun semantics for arbitrary represented run functions
satisfying the explicit zero/add/one/row-specification equations. Physical
register distinctness is explicit. The proofs construct Sigma1-definable
file invariants and invoke the existing internal Sigma1 iteration theorem;
source counters and elapsed times are arbitrary internal elements of every
IΣ1 model, including zero and nonstandard counters. There is no induction
on arbitrary Lean predicates or external-Nat runtime assumption.

The loop algebra is adapted from the previously existing ArithmeticL2Lib254
proofs and credited in the source. The new leaf imports only ArithmeticDagRun
and DagPerm; it imports neither the old fixed L2 interpreter nor its semantic
correctness theorems. The literal DagPerm instances are nodes 197 (p1→p2),
192 (ac→s1,s2) and 214 (clear tw), with actual physical register mapping.

Checks supply an actual two-row control table with a verified occurrence of
node 214 and a positive normal exit at control 3. For every internal initial
file the represented controlRun reaches that exit with tw cleared; the
zero-counter case and an unchanged unrelated register are checked. This is
a nonvacuous occurrence, not merely a conditional IRun statement. The other
two instances also specialize to actual represented controlRun for arbitrary
literal row tables with the generic row specification discharged.

The approved header closure contains 136 project modules, including 95
Foundation modules, and 39 explicit external package/toolchain boundaries.
130 modules/415 artifacts were reused with current source and recorded
object hashes. Six unchanged non-Foundation generic clients were explicitly
refreshed in topological order because their historical objects imported
older project-source versions. Those six historical objects were excluded;
no unchanged Foundation source was rebuilt. Current source/import pins and
all selected objects were authenticated, including the extra explicit
Lean.Elab.Tactic.Omega boundary. This is a mixed authenticated-cache/fresh
build, not a full closure replay.

One preflight failed before any Lean invocation: the original path guard
allowed package directories but not the accepted provider's explicit pinned
toolchain lib. The guard was corrected without adding a provider. All six
refreshes then passed cleanly. First new main failed only because a standalone
run_decPos intermediate needed explicit `(p := p)` in the generalized proof.
The next main passed; Checks required simp[Reach] to express cast control
numerals in the literal target. The final pair passes with unchanged theorem
statements. All three compiler attempts and the earlier preflight are retained.
The successful main from the second attempt is byte-identical to the final main.

Final main/check times: 16.934/2.252 seconds. Main diagnostics are empty;
eight final reports use only propext, Classical.choice and Quot.sound
(the occurrence certificate uses only propext and Quot.sound). The actual
command is pinned Lean4.32 with -M6000 -j1 -DElab.async=false, one thread,
private source snapshots, fresh regular outputs and a 512MiB reserve before
every invocation. Six refreshed sources and both new sources remained
unchanged during each corresponding invocation. The three attempt input
inventories contain 605/612/612 observations, rechecked after the final freeze.

- `BusyBeaver.ZFC.ArithmeticControlFile`: source `44a21e19025aa72f487e2c82c9e27bce13b79cdbff91b709c4d405a8d96746b8`, object `d47a7905e750af3a8a8f5c820e472c73d3cb682bfa55ebcd456e27e9311cbc91`, 12.798s.
- `BusyBeaver.ZFC.ControlCatalogue`: source `59817b2e544c870ca83b5331cf540e9da6dfe131145a568f9b7a920ae52f52af`, object `99624df846a97ccf6fad79896f84bdd649ab1e6e42d07ef57ead25a0ca2333ff`, 1.905s.
- `BusyBeaver.ZFC.ArithmeticControlBisim`: source `d7dbd8d4407eba785f1ef8461fad6c4f3366337fcce9ecbb2f61054a49a18cd9`, object `7db58088fc2a846e8f97758c7dfa2ee04770d391e2427d40af56b0d5f9073cbc`, 25.169s.
- `BusyBeaver.ZFC.Permutation252Frame`: source `63a3c9d9358a3a24edfef7889ffcc96d00f2aab3f2dd752c944c4f0e84236ae7`, object `ac047befee2d43055eb0822a604f5ccf65ceff5bb12cfe9bcf57db11c41b8ab8`, 1.215s.
- `BusyBeaver.ZFC.ArithmeticControlTable`: source `d7337bf240871fc0f72c3ada1fdfb024e7a504f7a3727a26bc93460ae69ff33b`, object `a0285b0b22c8cfb4b4ea5ed22605a63deb2889a6936ecc74c8f1fe774995ec7d`, 17.041s.
- `BusyBeaver.ZFC.ArithmeticDagRun`: source `11b39579a4fe0ab7900d5045f6e23f9a491b927809a8024508eb1c8abc273d27`, object `6079e46f28e59546d57dfc7e0840b08de4efad704c45a6ceb1935316166bed4c`, 10.634s.
- `BusyBeaver.ZFC.ArithmeticDagLoops`: source `f712b0cd8e90bc10cd1c67552efc26e73bff821df9862d25752f17994bdf6bb6`, object `f347338afbce8d179dce5a7f644bc82975c656a6c5a8b852a4e73381e43842ca`, 16.934s.
- `BusyBeaver.ZFC.ArithmeticDagLoopsChecks`: source `f3c16c59ed66acf252ab92d526771f1908a2b5c1d2b99615d0d9b6416e1b71e6`, object `841ec85ada605df13a409fcce72832f926c63e0517c05a734d5464a264248e38`, 2.252s.

Final new-leaf provider: `/tmp/arithmetic-dag-loops-controller-author-bzphpi2_/lib`.
Refreshed prerequisite provider: `/tmp/arithmetic-dag-loops-controller-author-i8jjuzib/lib`.
[Replay packet](arithmetic-dag-loops-replay.json) SHA `26c0ebcee1bad71b6b613a4ffeda3e4e912299bfbf71679104a79421087ee0e5`.
[Complete evidence manifest](arithmetic-dag-loops-author-replay/FILES.json)
contains 45 files, SHA `46838ee67858e306d2cb5c03f7701b7fb3fdbe61d3e2720a343c2d234c4c020e`.

The whole DagPerm root occurrence, command/scheduler composition, literal
215 control/site/boot simulation, positive-clock correspondence, source-ZFC
calibration, Pell arithmetization and final HA equivalence remain outside
this leaf. No accepted source or shared object was edited and no Git command
was used.
