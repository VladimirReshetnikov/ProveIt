# ArithmeticDagLoops: independent review and replay

26 October 2026. **PASS; no source or mathematical correction requested.**
The complemented47 reviewer independently read the complete new 187-line main
and 55-line Checks, all six refreshed prerequisite sources, the literal
DagPerm/Dag node definitions, the executed author and peer drivers, and the
cache inventory/provenance. Eight separate fresh private Lean invocations
passed; every object is byte-identical to the corresponding author object.

Frozen new sources:

- `BusyBeaver/ZFC/ArithmeticDagLoops.lean`: `f712b0cd8e90bc10cd1c67552efc26e73bff821df9862d25752f17994bdf6bb6`.
- `BusyBeaver/ZFC/ArithmeticDagLoopsChecks.lean`: `f3c16c59ed66acf252ab92d526771f1908a2b5c1d2b99615d0d9b6416e1b71e6`.

The independently reviewed author packet is
`arithmetic-dag-loops-replay.json`, SHA
`26c0ebcee1bad71b6b613a4ffeda3e4e912299bfbf71679104a79421087ee0e5`;
the author receipt is SHA
`9a704e1a252cff7e1b3189152ed76d610586b64ae38e1274ff41146ec3c342c3`.
All 45 author evidence files were authenticated against manifest
`46838ee67858e306d2cb5c03f7701b7fb3fdbe61d3e2720a343c2d234c4c020e`,
including prior failed attempts. Those author failures were not erased or
represented as independent replay failures.

## Mathematical scope

The generic `transfer`, `copy2`, and `clear` theorems retain the represented
run's Sigma1 definability and its explicit zero/add/one and literal row
specification assumptions. Required physical-register inequalities remain
premises. Their invariants are the actual nested register writes, with the
source decreased by the internal iteration count and each destination
increased by that same count. The zero-source case is included.

The prerequisite `ArithmeticDagRun.run_iterate` fixes an actual occurrence
before applying internal Sigma1 induction to bounded iteration/reachability.
The source count and elapsed witnesses are elements of the arbitrary IΣ1
model, not external natural times. Its definable invariant is `G`; the
intermediate `H` need not be definable because it is only used to supply a
per-pass reachability witness. No induction on an arbitrary Lean predicate,
standard-model oracle, or supplied runtime termination fact replaces this
argument.

I checked the actual logical-to-physical mapping and DAG rows. Node 197
uses node 191 to transfer logical register 4 into 5; node 192 uses nodes
187/188 to copy logical register 3 into 6 and 7; node 214 clears logical
register 1. The literal identities and distinct physical fields discharge
the generic structural premises. Attribution to the old ArithmeticL2Lib254
loop algebra is accurate, while the new imports do not use that module or
its fixed 254-interpreter semantics.

The focused two-row table really satisfies `Occ` for node 214. It tests
physical register 2, returns to its first control while positive, and exits
at positive control 3 when zero. `actual_clear` therefore supplies an
internal `controlRun` time for every initial file, rather than an IRun
statement whose occurrence remains hypothetical. The exit control being
outside this two-row table is harmless: the theorem reaches that live exit
and makes no claim about another step. The transfer/copy controlRun examples
still have the normal IRun meaning, conditional on whatever occurrence is
later supplied. They do not establish a whole-program occurrence.

## Independent build and provenance

The complete selected import DAG has 136 custom modules, including 95
Foundation modules, with 39 explicitly recorded package/toolchain boundary
names (including implicit Init and the explicit Omega boundary). Exactly
130 custom modules and their 415 recorded object artifacts were reused with
current source/header hashes and recorded object provenance. The six
historical generic-client objects were excluded and rebuilt in topological
order. No Foundation source or full dependency closure was rebuilt. External
objects/companions were authenticated as recorded; this is not a claim that
all package sources were freshly compiled.

Before execution, 2,528 hash observations authenticated the selected source
DAG, cached artifacts, author attempts, driver, and boundary evidence. A
separate final checker made 2,570 observations, including all fresh output,
snapshot and log hashes. Counts are observations, not distinct files. New
sources were fully read before execution and unchanged throughout.

The private provider is `/tmp/arithmetic-dag-loops-peer-v9mmg0s_/lib`.
Every compiler command uses the pinned Lean 4.32 executable with
`-M6000 -j1 -DElab.async=false`, one thread, a private explicit LEAN_PATH,
and a 512 MiB pre-command reserve. Cached artifacts are private links;
all eight new output objects are fresh regular files. No shared object was
replaced. Final free space was 1,916,973,056 bytes.

| Fresh module | Seconds | Peak RSS KiB | Exit | Object comparison |
| --- | ---: | ---: | ---: | --- |
| ArithmeticControlFile | 12.413 | 1829104 | 0 | identical |
| ControlCatalogue | 1.845 | 495412 | 0 | identical |
| ArithmeticControlBisim | 22.951 | 1909708 | 0 | identical |
| Permutation252Frame | 1.201 | 775940 | 0 | identical |
| ArithmeticControlTable | 16.404 | 1900496 | 0 | identical |
| ArithmeticDagRun | 10.903 | 1880296 | 0 | identical |
| ArithmeticDagLoops | 16.950 | 1876564 | 0 | identical |
| ArithmeticDagLoopsChecks | 2.225 | 1834820 | 0 | identical |

The first seven logs are empty. Checks reproduce exactly eight axiom
reports, using only `propext`, `Classical.choice`, and `Quot.sound`;
`clear_occurrence` uses only `propext` and `Quot.sound`. There are no
warnings, errors, or sorry axioms in any Lean log.

The initial peer wrapper stopped **after all eight successful Lean builds**
on Python tuple-versus-JSON-list equality of the axiom reports. Its FAILED
state and unchanged driver are retained. The first separate read-only
verification stopped on an overly strict metadata-dictionary comparison:
the peer source record also has a byte count, while the author record has
only path/hash. Its script and failure note are retained. The final checker
compares exact path/hash keys and normalizes report tuples to lists; it
passes all eight exact object/report comparisons and all final pins. No
Lean command was repeated, no proof changed, and neither bookkeeping issue
was a compiler or mathematical failure.

New main/check object hashes are respectively
`f347338afbce8d179dce5a7f644bc82975c656a6c5a8b852a4e73381e43842ca` and
`841ec85ada605df13a409fcce72832f926c63e0517c05a734d5464a264248e38`.
Full commands, source/object hashes, snapshots, logs, timings and the retained
wrapper states are in the [peer replay packet](arithmetic-dag-loops-peer-replay.json),
SHA `3ff36b6a6d02d9420fb486517813b7f2deb3867d6f64f45406e13f7ff8616077`.
The [35-file durable evidence manifest](arithmetic-dag-loops-peer-replay/FILES.json)
is SHA `c7fd4d125bfce9ac4df32b6a7e3c611c544512c291cccad0ea15c89013d59e35`.

## Independence and limits

I did not author these two new files or the six refreshed generic clients.
I previously authored some native and arithmetic215 prerequisites appearing
in accepted provider provenance; their authentication here is not an
independent mathematical re-review of my own earlier work. Foundation and
other unchanged cached prerequisites retain their stated trust/provenance
boundary.

The whole DagPerm root occurrence, command/scheduler composition, literal
215 control/site/boot simulation, positive-clock correspondence, source-ZFC
calibration and final HA equivalence remain unproved by this packet. No
source, shared documentation, display, or Git state was edited during this
review; only new peer evidence and private outputs were written.
