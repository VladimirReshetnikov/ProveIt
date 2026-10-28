# Actual 215 sites, canonical reentry and control/tape integration

27 October 2026. Read-only proposal. No new Lean source, overlay, compiler
invocation or dependency refresh is performed here. Home215 was accepted
while this draft was being prepared; the final plan selects ROOT's
independent `/tmp/home215-root-gwo_lm6e/lib` provider directly. Its author
history is retained without treating the earlier pending state as accepted.

## First useful leaf: actual site execution

Propose `DiophantineConsistency.ArithmeticSite215` and focused `Checks`,
importing exactly `ArithmeticHome215` and `BusyBeaver.ZFC.KSites215`.
An estimated 220–330-line main can close the uniform instruction endpoints
without also introducing the canonical control-frame graph. This is a
concrete instruction package, not another assumed execution interface.

Work in arbitrary `V` with `ORingStructure V` and `V ⊧ IΣ1`. The register
tuple `v : Fin 9 → V`, spare count `k`, gap and clocks are internal.
Only source paths, operations and checker fuel are finite external syntax.
Use `startValue gap v k Q := interpret gap v k (KSim.start Q)` and the
existing `interpret` for targets. Require `0 < k`; do not require a positive
gap, positive register values or a standard execution time.

The local checker adapters should have these exact logical shapes:

```text
runTo_actual:
  KSim.runTo tm215 br Q target = true → BranchValid br v → 0 < k →
  ReachPos (startValue gap v k Q) (interpret gap v k target)

runHalt_actual:
  KSim.runHalt tm215 Q = true → 0 < k →
  ∃ clock : V, 0 < clock ∧ first (runFrom clock (startValue gap v k Q)) = 0

source_checked:
  SiteCoverage.LeafAt KSource215.t215 Q e → KSim.checkEdge tm215 Q e = true
```

`runTo_actual` extracts the actual `some` result of the fuel4000 checker
and uses `Home.exec_matches_actual`, with initial moved flag false.
`runHalt_actual` uses `Home.exec_actual`, then the actual target predicate
`s.1 == 230`. Both left-facing and right-facing interpretations have first
projection zero at sparse230; the terminal write and move remain in the
full configuration. The halt claim is about `first`, not scalar config=0.

`source_checked` follows directly from `SiteCoverage.allSites_sound` and
the closed `KSites215.all_sites`. The final six source clients take only
actual `LeafAt` membership, `0 < k`, and the relevant internal DEC branch:

| Source operation | Target path | Overflow | Box effect |
| --- | --- | --- | --- |
| INC r | incPath Q | allOnes Q | plain (inc (physOf r)) |
| DEC r, value=0 | breakPath 1 Q | allOnes (stripPath false 1 Q) | plain none |
| DEC r, value≠0 | incPath Q | allOnes Q | plain (dec (physOf r)) |
| break j | breakPath j Q | allOnes (stripPath false j Q) | plain none |
| continue j | continuePath j Q | false | plain none |
| halt | actual arithmetic halt | — | — |

The targets are literally `KSim.tgtConf`; their distance is
`64 + overflow.toNat + KSim.growth effect - targetPath.length`, plus the
internal gap. Positive DEC has growth1. INC changes the spare count to
k+1; both DEC branches retain k. Physical r<9 is derived from the actual
source check, and the invalid-index fallback of `boxTail` is never used
for a certified operation. The first leaf can also expose these updated
tuple/spare identities without introducing the packed control table.

The `LeafAt` hypothesis identifies a finite source leaf. It is not a site
correctness oracle: the closed actual source certificate supplies every
check and the new arithmetic proof supplies every execution. Later a
canonical `Fin 4751` catalogue adapter discharges even this syntax argument
through `ControlCatalogue.leafEntries_sound`.

Focused checks should expose arbitrary internal parameters, gap0, k1,
zero and positive DEC, all physical indices, the full updated tuple/spare
suffix, terminal first-projection zero, the positive clock, and the fact
that neither branch validity nor a desired execution has been assumed at
the source endpoint. No new 4751-row computation is needed for this leaf.

## What the finite certificates already establish

`KSites215.all_sites` joins all105 blocks from nine batch modules into a
check over the complete literal `KSource215.t215`. Those blocks use
`decide +kernel`; `KFastSites215.allSites_of_fast` transfers the balanced
lookup through the proved all-state equality `fast_eq`, not through an
external evaluator result. No leaf is sampled. The actual tree has4751
leaves, independently bound to the accepted packed control table.

The new leaf does not recompile these certificates or infer arithmetic
simulation from `KSim.runTo_sound`, `KSim.sim_step` or `KSim.halts_iff`.
Those are ordinary-Nat theorems and are not used as internal premises.
Their sources are inherited through the finite checker import, but their
conclusions are not being substituted for the new uniform proof.

`ArithmeticControl215Table.table215_eq_catalogue` already identifies all
4751 packed rows with `leafEntries t215` mapped by actual `rowOf`.
Its complete high-bit/75-block checks are accepted. The later canonical
adapter should reuse this identity and structural catalogue lemmas; it
must not materialize another table, assume a supplied row equality or
interpret equal leaf counts as a simulation theorem.

## Second checkpoint: canonical paths and represented frame

This is a separate proposed leaf after the site package. Its exact cache
union must be reviewed then; only existing provider leads are pinned here.
No Rotation240/Perm252 execution module is proposed as an import.

Define the finite `Control := Fin 4751` in false-first catalogue order,
`source i` as its actual `(Q,e)`, and `number i = i.val+1`. Prove all source
paths have length≤48 using the closed site check, all entries are real
leaves, and the packed successors are exactly `crank (annotate t215)` of
the outgoing path, plus1. `entry_at_crank` returns the consumed path,
including implicit trailing zeros; it does not assert equality with the
unconsumed outgoing path.

The physical layout is already fixed on both sides. KSim's order is
`[2,8,1,4,3,7,0,5,6]` and its inverse is `[6,2,0,4,3,7,8,5,1]`.
`ArithmeticControlTable.registerOf` already applies
`Permutation252Frame.physOf` when constructing an INC/DEC row. Prove its
literal agreement with `KSim.physOf`, then interpret the packed file as
`v p = ArithmeticControlFile.regValue file p`. Do not permute that physical
file a second time. The finite nine-way comparison suffices; all file
contents remain arbitrary internal numbers.

Use a fixed finite lookup graph `pcValue` for the actual path bits, with
total default0 outside the catalogue, and define the canonical entry:

```text
entry q file k gap = frameSparse 84 1
  (pcValue q + bitPrefix false 64
    (bitPrefix false gap (2 * plain (fun p => regValue file p) k + 1)))
```

All functions have fixed Σ1/Delta1 graphs independent of the ambient
model. The finite nine-value fold is defined from the represented file
projections. Invalid q must be excluded in the simulation relation by the
actual opcode/support guard; a total lookup default is not a live control.
The halt instruction itself remains a valid entry until its next step.

The rebase proof is finite path algebra plus internal numeric equalities.
For outgoing P, set budget=64+overflow.toNat+growth. `execute_clean` gives
the zero suffix after the next consumed depth. Its dummy ordinary-Nat
registers merely select the finite zero/positive path branch; they do not
replace the internal register value. `allSites_walk_total` gives a real
next leaf; `allSites_walk` bounds its consumed path by48. Then
`RegisterPathClean.gap_consume` gives equality of the complete padded
bit lists, including when the next depth exceeds P.length. Numeric
`bitsPrefix_affine` and `bitPrefix_add` transport this equality to the
entire tape with its unchanged suffix. The new gap is exactly
`gap + digit overflow + growth`, and the updated spare count is as above.
Neither trailing zero cells nor the marker/register suffix may be dropped.

## Third checkpoint: actual control/tape simulation and boot

Instantiate the actual table spec `spec215` with the canonical entry and
the six proved site endpoints. A suitable fixed Σ1 relation is

```text
Related logical binary :=
  logical ≠ 0 ∧ opcodeValue table215 (controlValue logical) ≠ 0 ∧
  ∃ k gap, 0 < k ∧
    binary = entry (controlValue logical) (fileCodeValue logical) k gap.
```

The table's finite support lemma converts an internal nonzero opcode into
an actual finite source index. It does not convert internal data or time
to Nat. Prove `related_live`, `related_active`, the positive-clock
`related_step`, and `related_halt`; every semantic premise is discharged.
All site executions begin with moved=false, so Home supplies their
positive clock even if normalization or a zero-gap scan takes zero time.
The invalid initially-moved=true shortcut is not available. Active entries
have state24, whereas halt is first(config)=0, with full halt absorption.

The already accepted, genuinely parametric
`ArithmeticPositiveSimulation254.halts_iff` then provides both internal
halting directions. Its induction invariant is Σ1 and carries a clock at
least the logical index; it needs no clock upper bound or first-exit
oracle. Its classical Lean metatheory is not itself an HA derivation.

Finally derive the concrete numeric boot binding, not a new bootstrap run:
control1 has zero PC bits; file=`![0,0,0,0,0,0,4,0,0]`, k=40, gap=1.
The fixed margin64 plus gap1 is the exact65-zero boot region. Use the
accepted Symbolic `plainNat`/sepsR equality and Tape's fixed-graph lifting
to identify this entry with bootCode. The accepted95714-step boot already
proves `blank_halts_iff_boot`, including early-halting exclusion. The
literal decimal/sparse transition binding is also already Tape's theorem.

This supplies the substantive target

```text
(∃ t : V, run215 t (liveValue 1 seedFile) = 0) ↔
(∃ t : V, first (ArithmeticMachineRun215.run t) = 0).
```

Only after that result should accepted `BisimPerm215.halts_iff` and
`RuntimePerm222.seed_halts_iff` be composed to connect actual
Enum(live0,4,0) with actual literal215 blank halting. Their control graphs,
physical file and both arbitrary internal times are retained verbatim.

## Cache and scope boundaries

`cache-plan.json` is the exact first-leaf import closure. It reuses the
Home plan, accepted independent ROOT Home main and the accepted NativeAdaptive
Current peer's source-matching KSites215 closure. It selects173 cached
custom modules, including95 Foundation modules,458 custom artifacts,
41 boundary primaries plus123 companions:622 first providers. There is
zero refresh and no new Foundation import. The19 added site/path modules
and every shared source/object comparison are explicit in the JSON.
The existing unequal but source-identical KZip alternate is retained as
provenance, not mislabeled byte-identical. Actual external first providers
are checked in package-only path order; the shared project cache is absent.

The proposed future pair uses fresh regular outputs, Lean4.32,
M6000/j1/async=false and a512MiB reserve, after ROOT approval of this scope.
Both inputs must be snapshotted before each attempt and all
failures retained. No such build is performed by this planning packet.
Later table/runtime providers are pinned as leads, not smuggled into the
first import closure or counted as an authorized future union.

The author of this plan also authored Home, Symbolic, Boxes, Tape and
several control/runtime prerequisites. This is implementation planning,
not an independent peer review of those dependencies. The complete HA
goal remains open: the source-ZFC/actual-C222 proof calibration and the
internal equation/Pell witness equivalence must both be completed and
bound to the exact current coefficients before the existing PA-to-HA
transfer can yield the requested actual HA proof-existence theorem.
