# Actual p215 control catalogue — author record

Author: `controller_certificate`. The 214-line main and 45-line Checks are frozen.
This is the author's full source review and fresh bounded compilation, not an
independent peer review. I read all proof code, Checks and the executed driver
before compilation. The complete large literal was also reconstructed from the
actual source nodes and every packed slot was decoded and compared.

The new module imports only accepted `ArithmeticDagControlPerm222` and the actual
`KSource215Program`. Its public `path` is definitionally `KSource215.p215`, whose
root is 178 and node count is 179. The table is parameter-free. It contains all
4,751 actual false-first catalogue rows with the physical register map
`[6,2,0,4,3,7,8,5,1]`; no copied program definition or caller-supplied table is used.

`entryAt_eq` proves that indexed tree traversal equals the actual `leafEntries`
lookup. Seventy-five kernel-checked blocks cover every index below 4,751, with
all remaining 15 indices in the final block. Quotient/remainder decomposition
and both exact lengths yield `table215_eq_catalogue` for the whole lists. The
separate `packed215_bound` proves that no bits remain above the last 36-bit slot.
These are kernel proofs, with no `native_decide`, sampled rows, increased caps,
or omitted high bits.

The literal has 171,033 bits / 42,759 hexadecimal digits. Its hexadecimal SHA256
is `d29cf44ffd860add644cea58c074686d5d2be5894c72676fe6445d15b541cfa2`;
the canonical reconstructed row-list SHA256 is
`7bbbab9793f6e6ec2b82593b9ad51b8845753b1a1658ca40517adf30a12c938f`.
The preserved generator parses all 179 literal source nodes, resolves all
break/continue successors, and round-trips all 4,751 complete packed slots.
That audit is corroborating data evidence; the Lean catalogue theorem is the
logical binding.

The represented internal interface defines `run215` and proves its instruction
specification, zero/one/addition laws, and absorbing-zero law over arbitrary
models of IΣ1. Checks verify its genuine Σ1 function instance and exercise the
actual first instruction with an arbitrary internal register file. No DagPerm
bisimulation certificate, structured command dispatch, Turing-machine
simulation, source-ZFC calibration, or HA equivalence is asserted by this leaf.

## Provenance and fresh pair

The exact selected closure is 140 custom modules, including 95 Foundation
modules, with 425 recorded artifacts and 39 external boundary modules. All are
reused; no prerequisite, Foundation module or broad closure was compiled. The
historical plan remains unchanged at SHA256
`2ad54bece693f305077d6f8c35fb5a6b8aec9769eb346cecba52bcd682f7883f`.
The explicit provider supplement selects the byte-identical root-accepted
`PackedTables` and `ArithmeticDagControlPerm222` objects from
`/tmp/arithmetic-dag-controlperm222-root-pjkuaj4u/lib`, acceptance commit
`c604775130`, root-state SHA256
`f3228324a345d488692b682ed23b44cff2ef6e017dddb52101db535dc84092eb`.
Original providers and the historical pending-status record remain retained.

The driver reauthenticated complete source headers, the exact reachable import
graph, all selected source/object pins, explicit external boundaries, actual
first object providers, and the pinned Lean 4.32.0 executable. It recorded 1,880
preflight and 2,589 total observations across 705 distinct original paths. The
durable freeze separately repeated 1,447 checks; repeated observations are not
additional dependencies or a full fresh closure claim.

Both invocations used `-M6000 -j1 -DElab.async=false`, one Lean thread, an explicit
private `LEAN_PATH` excluding the shared project cache, and a 512 MiB free-space
guard. Both outputs are fresh regular nonsymlink files. There was exactly one
attempt and no failed compiler or preflight invocation for this packet. The main
ran for 126.923 seconds (maximum RSS 2,063,252 KiB); Checks ran for 1.811 seconds.
The main log is empty. All nine axiom reports are contained in `propext`,
`Classical.choice`, and `Quot.sound`; the packed bound and table-length theorem
use only `propext`.

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| `ArithmeticControl215Table` | `124d6a19e02d8ac41cfc2fe859b142d015995db623f6ef073bd37ef72396d8a5` | `17cb0c07f10e81fc63f8ca6ff2fffb0358c2a190c2c28bef4b8142a957800995` |
| `ArithmeticControl215TableChecks` | `b5159cda362db63ffeab8dda3d108df52d89cb1eca5fd713eaf8b304aa8355c7` | `3e807152f48cef20791b5248e3282b667919f2b8aa53de5e3796de4d46a16f8f` |

The private provider is
`/tmp/control215-table-controller-author-_qqbud32/lib`.
The replay packet is `reviews/arithmetic-control215-table-replay.json`, SHA256
`7cd8b72d782569b9306553e11e99eb3b62292c0ab5a99ad34d166031a8991609`.
The 16-file evidence manifest is
`reviews/arithmetic-control215-table-author-replay/FILES.json`, SHA256
`c9ee0fa5429d51007d5023df4572debd52987ed19466135f7715af8f02e5ce4f`.
It retains exact inputs, source snapshots, executed driver, commands, logs,
timings, objects, generator, data audit and freeze authentication. No accepted
source, shared object, shared documentation, or Git state was changed by this
author. Independent acceptance and the separate bisimulation leaf remain next.
