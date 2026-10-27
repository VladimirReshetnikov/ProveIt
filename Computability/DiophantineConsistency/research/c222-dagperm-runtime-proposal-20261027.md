# Actual enumerator → DagPerm → p215: next internal runtime checkpoint

This is a read-only proposal, after ROOT accepted `ArithmeticControlBisimPerm215`
in commit `17aee9ea3a`. No Lean source, object, overlay, dependency build, or Git
state was changed for this audit. It proposes actual program proofs, not a new
assumption that structured execution agrees with the enumerator.

## Exact remaining premise

`ArithmeticDagControlPerm222.root_reach_normal` and `root_reach_halt` now use the
unconditional root occurrence at node **0**, fuel **488**, in the literal
4,751-row catalogue. They still require an `ArithmeticDagRun.IRun` of the actual
structured `DagPerm.dagPerm`. The accepted bisimulation then transfers halting
of this control run to `ArithmeticControl215Table.run215`, for every internal
register file. It does not construct that first structured execution.

The current actual arithmetic sources already define `effectValue`, `stepValue`,
`fetchValue`, `enumValue` and `ArithmeticEnumRunPerm222.run` for arbitrary
internal values. `L2RootPerm.root_step` proves the desired program correspondence
only over standard `Nat`. The old internal `ArithmeticL2*254` proofs target a
different fixed DAG, different selector/read order and different AX body. Their
semantic theorems cannot supply the missing current premise.

## Concrete target and record convention

Use a new record with logical fields `(np,tw,ws,ac,p1,p2,s1,s2,pl)` and encode it
in the accepted physical order
`fileValue ![ws,pl,tw,p1,ac,s2,np,p2,s1]`. Define
`boundary pl np t S d h := ⟨np,t,S,0,d,h,0,0,pl⟩`.
Thus its physical fields are exactly `[S,pl,t,d,0,0,np,h,0]`.
These are arbitrary internal values in any `ORingStructure V` satisfying IΣ1.
`Clean st` means only `st.s1=0 ∧ st.s2=0`.

Abbreviate `IR` to the **actual** DagPerm, rows and represented run, and
`Rn e st st' := IR e (enc st) .normal (enc st')`.
The eventual root statement must have no caller-supplied structured-run premise:

```text
root_step pl np t S d h :
  (enumValue (liveValue pl np (stateValue t S d h)) = 0 ∧
    ∃ y, IR (.node 0) (enc (boundary pl np t S d h)) .halt y)
  ∨ ∃ pl' np' t' S' d' h',
    enumValue (liveValue pl np (stateValue t S d h)) =
      liveValue pl' np' (stateValue t' S' d' h') ∧
    Rn (.node 0) (boundary pl np t S d h)
      (boundary pl' np' t' S' d' h') ∧
    (pl' < pl ∨ np' = np+1).
```

The progress disjunction is essential: at the root occurrence normal exit
restarts at control 1. A nonzero scheduler step changes the record, so its
control clock cannot be zero. Merely obtaining an existential possibly-zero
clock is not enough for the reverse halting implication.

## Recommended first leaf: actual data and macro executions

Propose `ArithmeticDagMacrosPerm222` + focused Checks, importing only accepted
`BusyBeaver.ZFC.ArithmeticDagControlPerm222`. This is the smallest coherent
program-bound prerequisite package for the complete root proof. It should
prove the actual pairing/unpairing walks and all 13 AX macro contracts, plus
fetch. It is larger than the previous generic three-loop leaf (roughly 500–750
source lines, depending on factoring); it does not require a new generic
simulation framework. If size warrants a split, freeze actual pair/unpair/read
first, then the formula macros, rather than assuming any macro contract.

Required concrete endpoints, all on arbitrary internal records:

* `pair162 st`: node162 ends normally with `s2 += cantor s1 tw`, `s1=tw=0`.
* `unpair115 st`: node115 ends normally with `pl=0` and
  `(s1,s2)=(first M,second M)`, `M=cantor old_s1 old_s2 + old_pl`.
* `unpair116 st`: the same operation consumes `ws` instead of `pl`.
* For clean records, `read_ac174`, `read_p1_175`, `read_p2_176` replace `pl`
  by `second old_pl` and add `first old_pl` to the indicated destination.
* `push171`: `tw=0`, `ws=cantor old_tw old_ws`; parameter pushes at166/121/168
  instead load old `p1/p2/ac`, preserving that parameter.
* `cons119`: `tw=wim (first old_ws) old_tw`, `ws=second old_ws`.
  Nodes181/180/182 give `wel/wal/weq`; 218/178/183 give numeric `wn/wa/wex`.
  These are formula-code computations, not CProv claims.
* `fetch133`: for `pl=v+1`, replace `pl` by `v`; for `pl=0,s1=0`, set
  `pl=old_np,np=old_np+1`. Arbitrary dirty `tw,ws,p1,p2` are preserved.

Reuse the already accepted `ArithmeticDagLoops.transfer/copy2/clear` and
`ArithmeticDagRun.run_iterate`, with the actual fixed run/spec. Prove only
needed node instances, not duplicate the general loop algorithms. The Cantor
walk's represented invariant is the file with
`remaining=input−t`, `s1=first(M+t)`, `s2=second(M+t)`; it is a Σ1 function.
The pairing invariant uses `triangle` and bounded subtraction exactly as in the
source arithmetic guide. These are genuine internal Σ1 iterations; do not use
Nat recursion on `V` or arbitrary Lean-predicate induction.

All zero cases are retained: zero input to unpair, both pair inputs zero,
short/zero stacks, arbitrary original scratch values for pair/unpair, and
clean scratch assumptions only where a macro needs them. Fixed field update
and physical-map equalities must be proved, not inferred from register names.

## Next concrete dispatch/root package (separate approval)

After the macro package, `ArithmeticDagRootPerm222` can close the whole actual
root step in approximately 450–650 lines by three finite components:

1. Prove the **actual replacement equality test** at123/461–466. It clears
   logical registers6 and5, returning `.normal` iff the original values agree,
   otherwise `.brk 1`. Do not reuse the old internal 124–129 test: these are
   different nodes. For cancellation node463 use `N=min s1 p2`; if `p2≤s1`
   the final state is `(s1−p2,0)` with normal exit, otherwise a final decrement
   produces `(0,p2−s1−1)` and break. Node465 clears p2; the466 restart loop
   clears s1. The finite Nat `Dag219Bisim.eqA/eqR` proofs are guides only;
   the actual proofs use the represented loop invariant and `run_iterate`.
   Then derive actual MP150, NIP152 (including cache1 halt), and gate457.
2. Reuse the **syntax idea**, not the Nat run theorem, of `L2AxiomsPerm`:
   13 macro atoms, finite actual node-chain checker, literal AX word, and its
   fold. A kernel-checked finite certificate binds the complete word from236
   to457. Internal symbolic evaluation proves, for arbitrary `np,t,S,c,d,h,pl`,
   output `ac=p1=p2=s1=s2=0`, pointer `second(second pl)`, top
   `gateValue(d+first(second pl))(h+first pl)c`, and stack
   `axStackValue(d+first(second pl)) h (h+first pl) c d t S`.
   This explicitly preserves rho6(a,c), growG, the helper-free seed, old-d GEN,
   and old-d dominated rho8. All bundle collision cases, including c=0 and
   a=b, stay literal. No semantic truth of any pushed code is used.
3. Compose nodes139=(174,141), MP484=(175,150), and the actual selector tree:
   NIP0, DROP1, MP2, AX(c+3). The AX word itself reads y then x through
   changed nodes471/485/486. NIP/DROP read no payload; MP reads exactly one.
   Prove `command_step` against the existing actual `effectValue/stepValue`,
   then fetch133 + node139 gives `root_step` above. Split internal k into
   0/1/2 or k=c+3 using discrete arithmetic, never `Nat.cases` on internal k.
   The pointer bound is the accepted `continuation_progress`; new candidates
   have np'=np+1 even when raw candidate0 is executed.

This route directly constructs every structured execution that the accepted
root-control adapters require. The first macro package is a prerequisite to
this actual whole-root theorem, not an endpoint promotion by itself.

## All-internal halting transport after root_step

Define the fixed Σ1 relation between the actual scheduler live code and
`ControlFile.liveValue 1 (enc boundary)`. Derive its step/halt obligations from
`root_step`, actual root occurrence, and record progress. Genuine Σ1 induction
on internal scheduler time then yields both halting directions; positive clocks
make the reverse direction valid beyond any proposed internal control time.
`ArithmeticPositiveSimulation254.halts_iff` is a suitable **generic** theorem
(the full 114-line source was read), but it is not in the selected cache union.
A separate import requires authenticated existing provenance or explicit
permission for one unchanged-source refresh; no old254 concrete endpoint is
needed. One may instead put its small concrete induction in the later endpoint.

Compose with accepted `ArithmeticControlBisimPerm215.halts_iff` to obtain
`EnumRun` halting iff `run215` halting from the same internal file. At the actual
seed, the file is `[0,0,0,0,0,0,4,0,0]`, with old d=0 (not the old254 seed3/d3).
The eventual closed arithmetic sentence must mention the fixed represented
actual run graphs and this literal seed, not a supplied simulation premise.

## Separate 215 binary/tape/boot boundary

The accepted control bisimulation is already all-internal and needs no further
INC-commutation lemma. It does **not** identify its register file with an
internal binary tape run of the literal 215 machine.

`KSites215.all_sites/covered`, `KEndpoint215.tm215_box`, `KSim.sim_step/halts_iff`,
`KBoot215.boot`, `KDense215.commutes`, and `DecimalMachine215.action_conjugacy`
are existing valuable finite data/standard-Nat endpoints. `KSim.Rel` uses
external paths, Nat register lists, gap and spare blocks; `KSim.halts_iff`
uses ordinary Nat induction. They are not already PA-internal simulations.
`KBoot215` gives the exact 95,714-step boot to state84, gap65, nine physical
registers with np4, then forty spare blocks1. This must be bound to a represented
215 tape run (a finite standard trace can be internalized once that run exists).

Existing `ArithmeticMachinePerm252`, `ArithmeticSymbolicTapePerm252`,
`ArithmeticControlFrame254` and `ArithmeticControlSimulation254` show genuine
internal scans/site clocks and fixed Σ1 frames, but they use the different
Perm252 machine, the 6,460-row254 catalogue and its spare convention. Reusing
pure tape algebra is plausible; their concrete runtime theorems cannot be
instantiated with 215 by a namespace change. The next later work must bind the
actual tm215 table, all 4,751 p215 site entries, actual register box behavior,
internal gap/spare evolution and strictly positive local clocks. Then derive
both directions using represented simulation/absorption, internalize the fixed
boot, and separately bind the exact 715-digit decoder's state renaming. This
audit found no existing `Arithmetic*215` source beyond the newly accepted table
and bisimulation pair. No claim of an exhaustive theorem-name search follows
from that filename observation.

## Authenticated selection and review scope

`c222-dagperm-runtime-cache-plan-20261027.json` contains three exact reachable
DAGs with re-read headers, topological orders, source/object hashes, preserved
parent provenance and accepted ROOT provider supplements:

| Planned imports | Custom (including Foundation) | Foundation | Recorded artifacts | External names | Refresh |
|---|---:|---:|---:|---:|---:|
| DagControl only: first actual macro checkpoint | 139 | 95 | 424 | 39 | 0 |
| DagControl + actual EnumStep: dispatch/root | 148 | 95 | 433 | 39 | 0 |
| Bisim + actual EnumRun: later run endpoint | 152 | 95 | 437 | 39 | 0 |

All package boundary primaries were resolved against the preserved package-only
search paths; 117 companions per profile were additionally observed and pinned
as current observations, not retroactively asserted historical build captures.
There were 658 distinct authenticated provenance/provider paths, plus 30 pinned
source guides. The first selected ROOT DagControl provider is
`/tmp/arithmetic-dag-controlperm222-root-pjkuaj4u/lib`; the later Bisim provider is
`/tmp/control-bisim-perm215-root-1czao7t5/lib`, accepted in17aee9ea3a. Existing
source-identical alternative provider records remain recorded, not overwritten.
No overlay was created, so this is selection/preflight evidence, not a claim of
new compiler-loaded providers. The generic PositiveSimulation source is pinned
only as a guide, not silently counted as a reusable compiled prerequisite.

The complete current Nat L2Perm/AX/Root sources, actual arithmetic command/fetch/
enumerator sources, generic DagRun/Loops, and relevant old internal macro/control
proofs were read. Tape/frame/site files were inspected at their indicated
contracts and proofs; this is not a full audit of every binary runtime dependency.
One read-only planner preflight failed on a boundary record's nested `object`
schema; the preserved v1 is followed by the corrected successful planner. No
compiler was involved. All future execution requires separate ROOT approval,
full source/driver reading and the existing capped/private/reserve protocol.
