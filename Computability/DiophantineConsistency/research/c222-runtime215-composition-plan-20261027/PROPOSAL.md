# Actual scheduler / decimal215 runtime composition

Read-only proposal, 27 October 2026. No new Lean source, overlay or compiler
is authorized by this document. The smallest complete next pair is
`DiophantineConsistency.ArithmeticRuntime215` and its Checks, approximately
190–240 main lines plus 50–65 focused check lines. It closes the actual
internal scheduler-to-blank-machine runtime bridge, using the accepted
canonical frame, both control interpreters and the fixed boot graph.

## Imports and exact boundary

The proposed main imports only:

1. `DiophantineConsistency.ArithmeticControlFrame215`;
2. `BusyBeaver.ZFC.ArithmeticControlBisimPerm215`;
3. `BusyBeaver.ZFC.ArithmeticDagRuntimePerm222`.

The generic `ArithmeticPositiveSimulation254` is already an accepted
source-matching dependency of RuntimePerm222. No refresh is proposed.
The anticipated exact union is 207 cached modules, including 95 Foundation,
492 custom artifacts, 41 boundary primaries plus 123 companions and 656
first artifact providers. The accompanying metadata planner must confirm
these counts, every actual source header and all provider bytes. The Frame
ROOT provider is /tmp/control-frame215-root-90hncefu/lib, selected from
the accepted f1a02e20... packet and 63965283... thirteen-file manifest.
Its receipt SHA is 36a41c17...; the full pins are in the planner and inventory.

This pair does not import the source-ZFC/calculus interpretation, internal
Pell/polynomial proofs or an external Nat machine-equivalence endpoint.
All arithmetic execution statements quantify over arbitrary ORing models
of IΣ1 and arbitrary internal clocks. No source-validity, reflection or
HA theorem is a premise. The fixed source tree, finite control indices,
literal 95714 boot prefix and finite graph syntax remain standard data.

## A represented invariant with valid control support

Use the actual accepted functions and fixed entry graph. Define:

```
Related l b := ∃ q f k gap,
  0 < k ∧ opcodeValue table215 q ≠ 0 ∧
  l = liveValue q f ∧ b = entryValue q f k gap
Halted b := first b = 0
```

Here every quantified value is internal. A fixed `relatedDef` is declared
before ambient-model variables: existentially expose q, f, k, gap and op,
use the actual opcode graph with op≠0, the literal `liveDef`, and the fixed
`entryDef`. Its realization is Sigma1. The conjunction does not say merely
that l≠0: a nonzero live code with invalid control remains excluded.
The total entry graph itself is not treated as proof of valid control.

The finite `opcode_supported q` theorem obtains a real `i : Fin 4751`
with q=(number i:V). This applies even when q was initially an arbitrary
internal value; compact lookup support, rather than an assumed boundedness
or standardness premise, supplies that finite witness.

Required concrete theorems, all from this defined invariant:

- `related_live hr : l ≠ 0`, by actual `live_ne_zero`.
- `related_active hr : first b ≠ 0`, by `entry_active` and 24≠0.
- `related_step l b hr (hn : stepValue table215 l ≠ 0)` returns
  `∃ t, 0<t ∧ Related (stepValue table215 l) (runFrom t b)`.
  Resolve q with opcode_supported, invoke Frame.entry_step, unpack its
  ReachPos clock and repack the successor relation. Frame supplies the new
  valid Control, file, positive spare count and gap; opcode_nonzero supplies
  its support. No incoming or outgoing execution is assumed.
- `related_halt l b hr (hz : stepValue table215 l = 0)` returns
  `∃ t, first (runFrom t b)=0`, via Frame.entry_halt. Its positive-clock
  strengthening can be exposed directly from the same theorem.
- `halt_persists b hb t` follows from the stronger actual equality
  `runFrom_halted t b hb : runFrom t b=b`. The full terminal configuration
  and payload are retained. Neither Halted b nor its preservation means b=0.

No new semantic induction is needed for these finite adaptations. The
actual source gates, physical register permutation, complete suffix rebase,
zero-gap/DEC cases and positive site clocks have already been discharged
by Frame; this leaf does not add a source/site correctness hypothesis.

## Actual control run / tape run equivalence

For any actual finite Control i, arbitrary internal f, k, gap and k>0:

```
(∃ n, run215 n (liveValue (number i:V) f)=0) ↔
(∃ t, first (runFrom t (entryValue (number i:V) f k gap))=0)
```

A supported-q version is useful and may be the underlying helper, with only
`opcodeValue table215 q≠0` and k>0; the actual finite and seed clients discharge
both premises. There is no claim about arbitrary nonzero control codes.

Instantiate the accepted generic `ArithmeticPositiveSimulation254.halts_iff`
with logicalStep=`stepValue table215`, logicalRun=`run215 · (liveValue q f)`,
binaryRun=`runFrom`, Related above, and Halted=`first ·=0`. Discharge every
parameter with actual `controlRun_zero`, `controlRun_succ`, `runFrom_zero`,
`runFrom_add`, initial relation, the four related lemmas, and full absorption.
The logical run is Sigma1 by the accepted actual control-run graph; runFrom
and Related have their actual Sigma1 graphs.

The generic induction predicate is exactly
`∃ clock, n≤clock ∧ Related (logicalRun n) (runFrom clock initial)`.
It is Sigma1; its continuation condition stays external to that induction.
Strictly positive site clocks imply an internal clock at least n. In the
reverse direction, choose n equal to the alleged binary halt time and use
full absorption to reach a related active configuration at a later clock.
No upper clock bound, arbitrary predicate induction, IΣ2 strengthening or
restriction to Nat clocks is required.

## Exact seed frame equals the accepted boot code

Define the internal seed file as
`fileValue ![0,0,0,0,0,0,4,0,0]`, in the already physical order. The frame is
control1, k40, gap1. Do not permute this vector again.

First prove the standard finite algebraic identity:

```
entryValue (V:=Nat) 1 seedFile 40 1 = bootCode
```

The first actual source is `[false,false,false]`, DEC logical register8,
physical1. Check that finite first source with kernel `decide`, or reuse
an available public exact first-source theorem. Its numeric path word is0.
`entry_format` therefore gives 64 zero cells plus the internal gap1, then
one marker and the entire file/spare suffix. Use `plain_nat` (already
proved in SymbolicCore), `reg_file`, and `bitsCode_prefix` to identify this
with `KBoot215.bootRight = replicate 65 false ++ true :: sepsR bootVs`,
where `bootVs=[0,0,0,0,0,0,4,0,0] ++ replicate 40 1`.
`bootCode_frame` and actual Cantor coding finish the equality. Keep the
208-bit tape numeral opaque; do not compute a 95k-step run or unfold a giant
packed table to prove this algebraic identity.

Then define one fixed Sigma1 `seedEntryDef` using `fileDef` at those nine
literal coordinates and `entryDef` at 1,40,1. Use the familiar one-input
function interface with a single ignored parameter, evaluated at zero.
Prove its functional realization both over Nat and arbitrary V. Apply the
accepted Sigma1 function absoluteness theorem to this same graph at ![0],
obtaining `entryValue 1 seedFile 40 1=(bootCode:V)`. This lifts a finite
literal encoding identity, not an external Nat simulation theorem. The
graph is fixed identically in both models; no model-dependent formula or
supplied standardness property for internal data is used.

## Complete runtime composition in the same pair

Use the actual closed first control support, k40>0 and the boot equality
to derive:

```
(∃ n, run215 n (liveValue 1 seedFile)=0) ↔
(∃ t, first (ArithmeticMachineRun215.run t)=0)
```

The right-hand passage uses the accepted `blank_halts_iff_boot`, including
its exclusion of early halting by full absorption and live state24 at the
exact 95714 checkpoint. The literal clock and all 13 boot chunks are
retained in that accepted theorem; none is rerun or replaced here.

Finally compose, with the identical seed file and zero offsets:

1. `ArithmeticDagRuntimePerm222.seed_halts_iff` from EnumRun on live0,4,0
   to actual DagPerm control1;
2. `ArithmeticControlBisimPerm215.halts_iff seedFile` to actual p215 control1;
3. the preceding actual control-to-blank-machine equivalence.

Public endpoint:

```
(∃ n:V, ArithmeticEnumRunPerm222.run n
  (ArithmeticEnumStepPerm222.liveValue 0 4 0)=0) ↔
(∃ t:V, first (ArithmeticMachineRun215.run t)=0)
```

Both directions concern the actual represented functions in every IΣ1
model, including nonstandard witnesses. The reused bisimulation compares
both exact packed 4751-row tables using its full 2850-entry segment
certificate. It does not identify their 512 differing rows. RuntimePerm222
already discharges actual whole-root occurrence/dispatch; no root IRun
premise is reintroduced.

This is the complete runtime composition boundary. A separate leaf may
encode this equivalence as a closed arithmetic sentence and invoke Type0
completeness for an IΣ1/PA proof, or compose actual C222 refutation soundness
with the same endpoints. Neither those syntactic clients nor source-ZFC,
Pell witnesses or the final HA equation/ConZFC equivalence are silently
included in this proposed pair.

## Validation and retained provenance

Focused Checks should cover the fixed Related graph, invalid control
exclusion, genuine control1/seed support, gap0 on a generic valid entry,
nonstandard-clock theorem signatures, full terminal-payload absorption,
exact65-zero boot prefix/k40/physical NP4 and the final actual Enum/decimal
orientation. Include standard-only axiom audits for the public boundary.

Before any future approved build: authenticate the immutable exact union,
all actual headers/providers and accepted ROOT Frame selection; read every
final source and driver, snapshot both inputs, then run only two fresh
regular outputs under Lean4.32 -M6000 -j1 -DElab.async=false and 512MiB guards.
All failed attempts must remain. There is no Foundation or prerequisite
refresh, received-builder execution, source mutation or Git operation in
this read-only proposal.
