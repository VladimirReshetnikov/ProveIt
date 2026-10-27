# Actual 215 register boxes, then sites and control

27 October 2026. Read-only proposal; no new Lean source, compiler invocation,
overlay or prerequisite refresh is performed by this packet. Tape215 is now
ROOT-accepted in e28f94bba6. Its accepted independent provider is selected
directly, preserving the original author and ROOT records.

## First substantive checkpoint

Propose `DiophantineConsistency.ArithmeticRegisterBoxes215` and focused
`Checks`, importing exactly `ArithmeticMachineTape215` and the unchanged
numeric `BusyBeaver.ZFC.ArithmeticTapePrefix254`. The endpoint is execution
of all four actual register-box operations, for each of the nine selectors,
with arbitrary internal register values, left tape and spare count. It
does not take a box execution, structured run, or old252 simulation premise.
An estimated 750–1100-line main includes the arithmetic scans and spare
iteration needed by these concrete endpoints. A split would be reported
before expanding the approved leaves.

Work in an arbitrary `V` with `ORingStructure V` and `V ⊧ IΣ1`. Let
`F(q,L,R) = ArithmeticMachineTape215.frameSparse q L R` and
`FL(q,L,R) = F(q,L/2,L%2+2*R)`. The latter is the exact left-facing zipper,
including L=0, not a change of the sparse-state encoding. All execution
equations use the accepted actual215 `runFrom`, retaining the final write
and head move. Sparse84 is arithmetic24 and sparse230 is terminal code0;
no statement identifies every unsupported sparse label with a live state.

Use the existing numeric `onesPrefix(n,z)=2^n*(z+1)-1` and define the zero
prefix `2^n*z`. Prove the needed actual self-loop scans through
`Tape215.sparse_step`, with finite actual tm215 row equations. Read and
write bits are separate parameters in this helper: the increment carry
changes bits. The public box theorems discharge every row equation with
the concrete table; they have no caller-supplied row hypothesis.

The file representation is explicit:

* `block(v,z)=2*onesPrefix(v+1,z)` encodes `0,1^(v+1)`.
* `repeat3(d,0,z)=z`, `repeat3(d,n+1,z)=d+8*repeat3(d,n,z)` is a fixed
  PR blueprint, with genuine Sigma1/Delta1 total graphs, independent of V.
  Digits6,3,5 represent the plain, reversed and carried spare-one blocks.
* For nine internal values `v : Fin 9 → V`, `plain(v,k)` is the fixed
  nine-block fold onto `repeat3(6,k,0)`. Thus k is an internal number of
  spare blocks holding one, not the length of an external Lean list.
* `marked(r,v,k)` replaces only block r by
  `4*onesPrefix(v r,rest)`, namely `0,0,1^(v r)`. The other eight blocks
  and the complete spare suffix are preserved.

Require `0<k`. This supplies a following block even when r=8 and v r=0.
It is preserved because INC changes k to k+1 and DEC leaves k unchanged.
The representation matches the actual boot's nine physical values and
forty spare blocks1. It deliberately differs from the old252 spare policy.
The fixed finite nine-tuple may be displayed as `List.ofFn v`, but none
of its values, k, scan lengths or execution clocks are restricted to Nat.

Write `ReachPos x y := ∃ clock : V, 0<clock ∧ runFrom clock x=y`.
The proposed public conclusions, with only `r : Fin 9` and `0<k`, are:

```text
mark: ReachPos (F(sk r,L,plain(v,k)))
               (FL(markExit r,L,marked(r,v,k)))
inc:  ReachPos (F(64,L,marked(r,v,k)))
               (FL(40,L,plain(update v r (v r+1),k+1)))
dec0: v r=0 → ReachPos (F(0,L,marked(r,v,k)))
                         (FL(97,L,plain(v,k)))
decp: 0<v r → ReachPos (F(0,L,marked(r,v,k)))
                         (FL(40,2*L+1,plain(update v r (v r-1),k)))
```

Here `sk=[51,36,25,48,32,33,22,55,60]`; `markExit 0=1`, and the other
eight exits are3. DEC's positive extra left bit is retained. INC ends by
the actual bypass `tm215 198 false = some (true,false,40)`. The finite
engine agreement covers all44 `KTape.boxRows` and this additional bypass
row; these will be actual kernel-checked row equalities, not an imported
Nat `KTape.boxLemmas` proof or a copied old252 semantic hypothesis.
Their finite row list is materialized in the new leaf from the actual
table already imported by Tape215; KTape and KTable230 are not added as
imports merely to state this agreement.

For induction, fix the total internal length and initial halves, and
advance a bounded progress index i. The invariant is an actual runFrom
graph equality at the accumulated clock, with remaining prefix n-i and
the transformed prefix already on the opposite half. All involved
functions have Delta1 graphs, so the bounded progress invariant is
Sigma1. This applies both to unary scans and to the internal spare-block
count. An alternative exact-clock uniform scan invariant is explicitly
Pi1, supported by `ISigma1.pi1_succ_induction`; a universal existential
clock predicate is not silently treated as Sigma1. Finite nine-register
composition then exports existential clocks. No IΣ2 strengthening or
arbitrary Lean-predicate induction is proposed. Positive box clocks can
also be checked from distinct actual entry/exit state codes and
`runFrom_zero`; intermediate normalization or empty scans may take zero.

Checks should cover all nine selectors, zero values including the last
primary with k=1, positive DEC of one, L=0, INC count growth, the exact
positive-DEC left bit, symbolic nonstandard parameters, actual checker
witnesses, and the two different DEC exits. A final ordinary-Nat binding
of the fixed representation to `sepsR` is algebraic, not a Nat-to-model
execution shortcut. No complete control/tape equivalence is claimed here.

## Exact first-leaf cache decision

`cache-plan.json` reconstructs the complete current header DAG for those
two imports. It selects accepted ROOT Tape215, all unchanged Tape215
prerequisites, and proposes one explicitly fresh unchanged helper:

* 147 prerequisite modules total: 146 cached and one refresh;
* 95 Foundation modules, all cached, with no new Foundation import;
* 431 cached custom artifacts;
* 41 package/stdlib boundary primaries plus123 companions,164 artifacts;
* 595 selected first artifact providers before the helper refresh;
* after approval only three fresh commands: Prefix254, Boxes215, Checks.

The helper source SHA is
`396b573e4e94058859608ffa74be668f1d29a092f4853bdeafc0702da222cd55`.
Its full86-line source was read. It imports only ArithmeticCantor and
Foundation's Exp. Both direct source pins match the selected current
closure, but nine of the eleven custom sources in its historical run1
record differ from current accepted sources. The historical successful
4.32 build and object are pinned as history only. That object is expressly
excluded from the selected providers. The one unchanged-source refresh
must be reviewed/approved; no Foundation or wider dependency rebuild is
proposed. The package path excludes the shared project output directory.
Every new invocation would retain the usual M6000/j1/async=false caps,
fresh regular outputs, source snapshots, failure records and512MiB guard.

## Remaining concrete route after this freeze

1. **Actual K symbolic execution and home.** Interpret the existing
   `KRuntimeCore.Seg`, `SConf`, `norm`, `sMatches` and
   `KHomeReady.stepper/exec` at an internal gap, the above nine values,
   and k>0. Affine run lengths remain `a*gap+c`. Prove recentering and
   normalization preserve the entire numeric configuration, including
   only the exterior zeros removed by normL. Prove actual box oracle
   clauses using the four new endpoints. The home proof must scan the
   exact states2,3,5,9,15,23,34,50 with the checked less-than-eight zero
   streak, then execute the actual18-step marker-boundary transition to
   sparse84. The already checked `ready tm215` Boolean may be reused as
   finite data; its Nat `Reach` soundness is not an arithmetic premise.
   The new StepOk carries an internal clock and preserves the checker's
   moved flag: true entails positive clock. Empty scans and recentering
   are permitted to have zero clock. Thus successful `exec` starting
   false and requiring moved=true produces a positive clock.

2. **Literal per-site contracts.** Bind the existing actual
   `KSim.checkEdge tm215`, fuel4000, path bound48 and distance64, including
   all INC/DEC/break/continue/halt effects. Its physical order is
   `[2,8,1,4,3,7,0,5,6]`, inverse `[6,2,0,4,3,7,8,5,1]`; prove its finite
   equality with the map used by `ArithmeticControlTable.rowOf`.
   INC appends a spare1; positive DEC adds a blank distance cell and does
   not append a spare. Overflow adds its exact further blank cell.
   Reuse all4751 existing site checks (`KSites215.all_sites`,105 kernel
   blocks in nine batches), as checked Boolean data. No omitted/sampled
   sites or assertion that their Nat simulation is already internal.
   Canonicalizing outgoing paths must account for tree descent and
   zero-padding using `ControlCatalogue.entry_at_crank`, not assume
   literal equality of outgoing paths and next canonical paths.

3. **Actual represented control relation.** Use the accepted equality
   `Control215Table.table215_eq_catalogue` and `spec215`. Define a fixed
   Sigma1 entry graph for numbered canonical paths and a relation
   `∃ pc,file,k,gap, validPC pc ∧ 0<k ∧ logical=liveValue pc file ∧
   binary=entry215 pc file k gap`. The finite PC classification is
   separate from arbitrary internal data/times. The preceding site
   theorem must supply each live-step positive clock and every halt
   endpoint, with no root IRun or site execution premise left. Resolve
   the initial empty path to control1 and preserve its zeros in the
   distance calculation. The boot binding is the actual physical file
   `![0,0,0,0,0,0,4,0,0]`, count40 and gap1 (64+1 blank cells).

4. **Halting equivalence, then existing runtime composition.** Apply
   the already accepted parametric `ArithmeticPositiveSimulation254`
   with actual controlRun and Tape215.runFrom, the concrete relation,
   positive site clocks and Tape215's full halt absorption. This proves
   both directions at internal times, without a clock upper bound.
   The substantive target is
   `∃t,Control215Table.run215 t (liveValue 1 seedFile)=0 ↔
    ∃t,first(MachineRun215.run t)=0`.
   Only then compose accepted BisimPerm215 and RuntimePerm222 to obtain
   actual Enum(live0,4,0) versus actual literal215 blank halting. The
   decimal row/state binding and exact95714 boot are already Tape215
   theorems. None of this settles source-ZFC, polynomial arithmetization,
   or the final HA proof-existence endpoint.

Later source/certificate pins and existing accepted provider leads are
recorded separately; they are not first-leaf imports or launch approval.
The old252 uniform scans/boxes/site/control code was inspected as a proof
guide only. Its concrete states, spare conventions and semantic endpoints
are not interchangeable with the actual215 program.
