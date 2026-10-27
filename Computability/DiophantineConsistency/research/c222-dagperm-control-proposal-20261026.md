# Actual DagPerm control catalogue and root occurrence: read-only proposal

26 October 2026. No new Lean source or compiler invocation in this audit.
ROOT requested the whole actual programme table/root certificate next.
The pending-independent DagLoops packet remains frozen.

1. Literal programme and finite measurements

The structured root is **node 0**, not 487. The four live source definitions
Dag222, Dag219, DagDom and DagPerm give 487 nodes, numbered0..486.
`KSource215.pathDagPerm = RMEquiv.ofDag DagPerm.dagPerm 487`; the number487
is its `nnodes` parameter. Its `ptree` uses fuel488. The source itself also
records root height178.

A new read-only audit parsed those four live Lean literal node definitions,
applying exactly their override order. It independently enumerated (a) the
false-first path catalogue with actual inc/strip/break/continue successor
resolution, and (b) the ArithmeticDagRun carExit/cdrExit occurrence layout.
The complete 4,751 rows agree. Maximum successor is4,751; every nonhalt
successor is positive. Physical registers are [6,2,0,4,3,7,8,5,1]. The old
36-bit PackedTables format suffices (3 opcode bits,4 register bits,13 per
successor); the candidate packed integer has171,033 bits. Canonical row-list
SHA256 is42bcd1c057e73b82f6e13d151dbe280f1d30e06784575e788dbe2a8430704dcd.
These are finite audit measurements, **not Lean theorems**. No historical
Python builder or archive programme was executed or imported.

2. Smallest coherent first implementation

Propose `ArithmeticDagControlPerm222.lean` +Checks, approximately100–150
logical source lines plus one fixed packed-row literal. Direct imports:
`BusyBeaver.ZFC.ArithmeticDagLoops` and `BusyBeaver.ZFC.PackedTables`.
No caller-supplied table, occurrence or simulation parameter.

Define fixed `packedRows : Nat`, `count := 4751`,
`table := PackedTables.table packedRows count`,
`rowsLit c := PackedTables.rowsOf packedRows count c`, and
`path := RMEquiv.ofDag DagPerm.dagPerm 487`.
The path expression is exactly the expression defining existing pathDagPerm;
no import of its huge certificate-data client is needed for this equality of
expressions. Do not claim a compiled cross-module alias theorem before that
module is imported in a later composition.

Required unconditional finite certificates:

```
table_eq_catalogue :
  table = (ControlCatalogue.leafEntries (RMBisim.ptree path)).map
    (ArithmeticControlTable.rowOf (RMBisim.ptree path))
root_occB : ArithmeticDagRun.occB DagPerm.dagPerm rowsLit
  488 (.node 0) 1 (fun _ => 1) = true
root_occ : ArithmeticDagRun.Occ DagPerm.dagPerm rowsLit
  488 (.node 0) 1 (fun _ => 1)
```

The rootOcc certificate checks every actual opcode, physical register and
successor under the literal DAG, including the modified selector/AX nodes;
there is no inference from conditional IRun alone. The catalogue equality
also pins the exact DFS numbering needed by a later p215 table bisimulation.
Expose table_length=4751 and the closed nonhalt-successor bounds if useful.
All ordinary root exits use control1; halt uses absorbing0 through leafRow,
not liveValue0. Positive root restart is therefore explicit.

Use the already kernel-proved `occ_of_occB`, `PackedTables.rowsOf_some` and
`ArithmeticControlTable.spec_get`. Fixed internal exports should be:

```
run := ArithmeticControlTable.controlRun table
spec : rowsLit c = some row ->
  stepValue table (liveValue (c:V) x) = sem regValue write liveValue row x
root_reach_normal : IRun DagPerm.dagPerm rowsLit run (.node 0) x .normal y ->
  exists k:V, run k (liveValue 1 x) = liveValue 1 y
root_reach_halt : IRun DagPerm.dagPerm rowsLit run (.node 0) x .halt y ->
  exists k:V, run k (liveValue 1 x) = 0
```

The last two are conditional *structured-run adapters*, clearly distinguished
from the unconditional root occurrence. Exact zero/add/one/absorption and
Sigma1 run graph/totality come from the fixed generic interpreter. Checks
must instantiate the just-proved real table and occurrence, including a
normal-return example and halt-exit shape; no arbitrary occurrence premise.

First try bounded kernel checks on the literal data, following the existing
root-occurrence pattern. If a monolithic finite check exceeds the cap, retain
it and split that same complete check into finite chunks with an explicitly
proved composition rule. No dropped rows, supplied certificate assumption,
unsafe native proof or cap increase. A generic structural table compiler is
a possible later optimisation, but would need its own list-offset/exit-map
proof; it is not needed before this concrete certificate is attempted.

3. Exact reuse and one proposed refresh

The frozen cache plan has138 custom modules including95 Foundation modules:
137 reusable modules/422 recorded artifacts and39 external boundaries.
It selects the six newly refreshed generic clients and the frozen DagLoops
main, with their still-pending root independent acceptance stated explicitly.
All source/object pins were rehashed. Future acceptance should be added as a
provider-selection supplement, without rewriting this historical plan.

Only `BusyBeaver.ZFC.PackedTables` needs a proposed fresh unchanged-source
prerequisite build. Its sole project import, ArithmeticControlBisim, is already
in the selected current closure. The complete PackedTables source was read;
no authenticated PackedTables provider was found in the consulted active
Diophantine inventories, so no arbitrary existing olean is selected. There
are no added Foundation modules or package boundaries. This plan authorizes
no execution by itself. Exact cache SHA is
b3ecbe703da86e953c2e06ed1dcca7b9f6e40598d8a8d82b3563c408ed45d729.

4. Concrete next integration after this checkpoint

Define the actual boundary file for pl,np,t,s,d,h by physical fields
`[s,pl,t,d,0,0,np,h,0]` and control1. The seed is pl0,np4,work0:
all registers except np are zero. In particular this is neither old candidate3
nor old d3. Reprove the actual register macros internally, starting with
fetch node133 and read_ac174/read_p1_175/read_p2_176, from generic loops and
actual node equalities. Existing Nat L2Perm/L2RootPerm and old fixed254
arithmetic files are source guides, not all-internal semantic assumptions.
The old fixed interpreter proofs do not instantiate to a new row table just
by changing a namespace.

Then the exact node139/141 dispatch must match current
ArithmeticCommandStepPerm222.effectValue: NIP0 (only h1 halts), DROP1,
MP2 (reads p=x and adds it to old d), AX k>=3 with c=k−3, a=d+q,
b=h+p, u=old d (payload p=y,q=x). Root node139 reads only the selector;
MP node484 reads its own field; AX nodes471/485/486 consume its two fields.
The helper-free gated bundle and growG output must match the current literal
stack, including collision0 and legal repeated/zero labels. No old four-payload
AX or primitive rho7 interface may be substituted.

The target internal `root_step` is a disjunction: actual EnumValue of the
encoded live state is0 plus a root IRun halt; or it is a new encoded live
state plus a normal root IRun to exactly its boundary file and the progress
condition pl'<pl OR np'=np+1. Actual Fetch.continuation_progress and the
literal candidate increment support strict boundary-file change. Together
with unconditional rootOcc this yields positive internal clocks. The generic
ArithmeticPositiveSimulation254 theorem can then provide both halting
directions for arbitrary internal times, using a genuine Sigma1 relation,
absorption and the clock lower bound; it needs no external-Nat simulation.

Still later: actual p215-to-pathDagPerm finite table bisimulation, literal
215 register/site/boot simulation and state relabeling to the decimal machine.
This proposal does not supply any of those, the source-ZFC calibration,
Pell arithmetization or the final HA proof-existence endpoint.
