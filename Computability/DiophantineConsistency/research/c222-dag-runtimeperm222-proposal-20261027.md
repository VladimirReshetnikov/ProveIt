# Actual internal enumerator/control halting bridge

27 October 2026. Read-only proposal following the frozen author RootPerm pair.
No new Lean source, compiler, overlay or Git action was performed. ROOT's
independent RootPerm acceptance is still pending at this plan snapshot.

## Smallest coherent next leaf

Propose `ArithmeticDagRuntimePerm222` + focused Checks, approximately180–220
main/40–55 check lines, after explicitly refreshing the unchanged114-line
`ArithmeticPositiveSimulation254` generic theorem. Its name is historical;
its statements quantify arbitrary represented logical/control runs and a
Sigma1 relation, and contain no concrete old254 runtime premise. The complete
source and the old `ArithmeticL2Endpoint254` source were read. Only the generic
transport may be imported after explicit refresh authorization; the old
endpoint is a source guide and is not an import or semantic premise.

Direct imports:

```
BusyBeaver.ZFC.ArithmeticDagRootPerm222
DiophantineConsistency.ArithmeticEnumRunPerm222
BusyBeaver.ZFC.ArithmeticPositiveSimulation254
```

This derives both halting directions for arbitrary internal IΣ1 values and
then specializes to the actual seed. It does not assume a root `IRun`, a
finite standard execution bound, a simulation relation supplied by the caller,
or correctness of the ordinary Nat enumerator.

## Exact represented relation

Abbreviate actual `ArithmeticEnumStepPerm222` as E, actual EnumRun as ER,
DagControlPerm222 as D, and ArithmeticControlFile as CF in this note only.
Keep the accepted `boundary pl np t S d h` unchanged. Define:

```
controlOf pl np t S d h := CF.liveValue 1 (enc (boundary pl np t S d h))
Related l c := ∃pl np t S d h,
  l = E.liveValue pl np (stateValue t S d h) ∧
  c = controlOf pl np t S d h
```

Give a fixed `relatedDef : Σ1.Semisentence 2` with those six unbounded
existential variables, an actual working-code witness via `stateDef`, an
actual enumerator live-code witness via `E.liveDef`, and the literal
`CF.fileDef` arguments `[S,pl,t,d,0,0,np,h,0]`, followed by `CF.liveDef` at
control1. Prove its realization directly from the existing graph instances;
no new interpreter or arbitrary predicate induction. `enc_boundary` is the
exact eight nested Cantor pairs, or equivalently the accepted fileValue tuple.

Both sides of Related are live: the scheduler live code and the control live
code have the form Cantor+1. Thus Related implies `l≠0` and `c≠0`. In particular
true halting zero is distinguished from a live state whose control number is0.
All relation parameters and witness clocks are values of the ambient model.

## Concrete root obligations, including positive clocks

Use the following new concrete lemmas, not caller hypotheses:

```
boundary_ne_of_progress
  (hp : pl' < pl ∨ np' = np+1) :
  enc (boundary pl np t S d h) ≠ enc (boundary pl' np' t' S' d' h')

related_step (hr : Related l c) (hn : E.enumValue l ≠ 0) :
  ∃k, 0<k ∧ Related (E.enumValue l) (D.run k c)

related_halt (hr : Related l c) (hz : E.enumValue l = 0) :
  ∃k, D.run k c = 0
```

For boundary inequality, apply actual physical projections1 (pl) and6 (np)
to any putative file equality. The two progress alternatives contradict,
respectively, strict pointer decrease or `np<np+1`. No other register needs
to change and no bound on internal data is added.

For related_step, unpack Related and apply the actual frozen `root_step`.
Its halt branch contradicts hn. Its live branch supplies the exact next
scheduler scalar, normal structured execution, and progress. The accepted
`D.root_reach_normal` uses unconditional `root_occ` at actual node0/fuel488/
control1 to produce a control clock k. If k=0, `D.run_zero`, injectivity of
`CF.liveValue 1`, and physical file projections contradict the proven
boundary inequality. Therefore k>0. A positive clock is proved for every
nonhalting step, not assumed from the existence of a structured derivation.

For related_halt, the live branch contradicts hz since a live scheduler code
is nonzero; the halt branch uses `D.root_reach_halt`. No clock positivity is
required by the generic halt premise, although it follows from the live input.
Control halt absorption is precisely accepted `D.run_halted` and `D.run_add`.

## Actual internal time transport

Instantiate the genuine generic `halts_iff` with:

* logicalStep=E.enumValue;
* logicalRun n=ER.run n (E.liveValue pl np (stateValue t S d h));
* binaryRun=D.run (the generic name does not assert a binary-tape simulation);
* Related as the fixed represented relation above;
* Halted c=(c=0), initial control=controlOf pl np t S d h.

Use actual ER.run_zero/run_succ and D.run_zero/run_add; the two actual runs
already have Sigma1 graphs. The proof's only induction invariant is
`∃clock, n≤clock ∧ Related (logicalRun n) (D.run clock initialControl)`.
It is Sigma1 because clock and graph witnesses are existential and the bound
is atomic. Its universal continuation condition is a separate theorem premise,
not smuggled into the induction predicate. Each positive increment gives
clock(n)≥n, including nonstandard n. Thus reverse transport can reach beyond
any alleged internal control-halting time. Absorption then contradicts Related
activity if the logical run never halts. Forward transport uses the actual
related_halt branch; it never infers logical nonhalting from one zero-length
clock. No upper bound, least-time search, Nat induction or IΣ2 strengthening is
needed. The generic proof uses classical Lean reasoning externally; this is
not itself an HA proof construction.

The primary endpoint is:

```
halts_iff (pl np t S d h : V) :
  (∃n, ER.run n (E.liveValue pl np (stateValue t S d h)) = 0) ↔
  (∃k, D.run k (controlOf pl np t S d h) = 0)
```

Its actual seed specialization, with no parameter or validity premise, is:

```
seed_halts_iff :
  (∃n, ER.run n (E.liveValue 0 4 0) = 0) ↔
  (∃k, D.run k (CF.liveValue 1
    (CF.fileValue ![0,0,0,0,0,0,4,0,0])) = 0)
```

`stateValue 0 0 0 0=0` is the literal Cantor-zero identity. The seed keeps
candidate4 and counter0; it is not the old candidate3/counter3 seed. Focused
checks should expose exact physical seed coordinates, arbitrary dirty working
registers, normal progress excluding zero clock, true-zero absorption, and the
two general/seed directions. No source-refutation or HA endpoint should be
printed as if this leaf established it.

## Exact selected cache and necessary refresh

The frozen inventory records152 prerequisite modules in the resulting graph:
**151 cached custom modules,95 Foundation,436 cached artifacts,39 external
boundary names and117 current companions, plus one proposed fresh unchanged
custom module**. The resulting artifact count after that refresh would be437.
The new pair itself is separate. There is no new Foundation module or build.

RootPerm's source/primary are provisionally selected from its author PASS
packet: source0aae5535e9c02c3685ae0996db759ebad2485a8f57d609c680d8e3af0ebd03a8,
objecte26655bd289a1ba913a5d4db93f05b1473827476ef3a47af95905cf039d0eded,
provider `/tmp/dag-rootperm222-controller-author-fgelf5nf/lib`. Once ROOT
accepts/replays it, add a separate accepted-provider supplement before any
compiler, preserving this historical selection.

The only additional accepted runtime primary is EnumRunPerm222, source
95b68fa875feda9d29bf10413235666493508fe16e118104367fb9358f436fbb,
object3181d0fb572a271280a6c76769691a58d8f2c7ca79282b512392cfe1080c64f2,
provider `/tmp/enum-runperm222-independent-u1m6486p/lib`. Its actual headers
add no missing foundational prerequisite.

The current generic PositiveSimulation source has SHA256
ec9c249013345061fb2dd99b1cb387f10dfd5d69447100465ff2b7558e949290.
It matches the preserved successful4.32 source in
`/tmp/zfc-positive-simulation/run4/verification.json`. However9 of its11
explicitly recorded custom prerequisite sources differ from today's selected
closure, and all11 selected object hashes differ. Therefore that old object is
**excluded**, despite identical leaf source. A single explicit current refresh
is proposed, not yet authorized or performed. Its two imports (ArithmeticCantor
and Foundation HFS.PRF) and all their current dependencies are already cached.
No broad historical closure refresh is proposed.

All source headers, reachable graph, selected source/object hashes and first
package-boundary providers are authenticated in the companion plan. No old
object from PositiveSimulation is a selected premise. The historical record
is evidence for the reuse decision, not proof of compatibility. Subsequent
execution requires ROOT's approval of this exact one-refresh scope, full
source/check/driver reading, private fresh regular outputs, -M6000 -j1
-DElab.async=false,512MiB reserve, and preserved failures.

## Later boundaries

The accepted BisimPerm215 theorem can subsequently transfer this control
halting result to the actual p215 control table using its exact internal
register-file relation; importing it adds three already-authenticated custom
modules, but is not necessary to this minimal first bridge. No tape or boot
claim follows from that table equality. Literal215 tape/site clocks, the fixed
boot trace and decimal state renaming remain separate internal simulations.
The actual source-ZFC interpretation, represented Pell/polynomial reductions,
and final existence of an HA equivalence proof also remain outside this leaf.
