# Actual internal Home execution for the 215 checker

27 October 2026. Read-only proposal for ArithmeticHome215 and focused Checks.
No Lean source, compiler call, dependency refresh or object overlay is part
of this audit. Frozen SymbolicCore bytes are unchanged. Proposed direct
imports are DiophantineConsistency.ArithmeticSymbolicCore215 and
BusyBeaver.ZFC.KHomeReady. The latter's actual definitions are reused; its
ordinary-Nat execution theorems are not used as runtime premises.

## Public endpoints

For every ORing model V of IΣ1, with gap,k:V and v:Fin 9→V:

```text
home_actual:
  KHome.home s = some t ->
  ReachPos (interpret gap v k s) (interpret gap v k t)

stepper_actual (hk : 0<k) (hv : BranchValid br v):
  KHomeReady.stepper tm215 br s = some(t,m) ->
  StepOk gap v k s t m

exec_actual (hk : 0<k) (hv : BranchValid br v):
  KHomeReady.exec tm215 br target fuel s false = some t ->
  target t = true and
  ReachPos (interpret gap v k s) (interpret gap v k t)
```

The home endpoint needs neither k>0 nor a branch assumption: a successful
home scan reads only finite bit/run syntax and never consumes a box. Its
right tail is arbitrary and is restored exactly. The stepper and executor
retain the existing positive-spare/branch premises needed by their fallback
to the actual symbolic oracle. The public endpoints take no Home execution,
row agreement, BoxLemmas, structured IRun or old252 simulation premise.

Also export the literal closed `ready tm215 = true` certificate, and an
exec-to-matching-target client combining the successful exec with the
accepted matches_actual equality. This is the smallest substantive leaf
needed by later KSim.runTo/runHalt consumers. It does not import KSim or
claim all 4751 sites in this checkpoint. A generic helper may expose the
full moved-flag statement of execWith_actual, but the public positive-clock
client must start with moved=false.

All data values, affine gaps, spare counts, right tape halves and resulting
clocks are internal model elements. The source segment spine, small scanner
counter, successful checker result and finite executor fuel are ordinary
finite syntax. This is not a theorem restricted to standard register values.

## Literal row and boundary facts

KHome.state is exactly [2,3,5,9,15,23,34,50] on indices below 8.
Kernel-check all eight true/reset rows and seven false/next rows. These are
finite table equalities, not supplied semantic assumptions. The boundary
uses exactly three additional distinct rows: 50/false→75 left unchanged,
75/false→75 right unchanged, and 75/true→84 right unchanged.

The fixed boundary theorem is:

```text
boundary_actual (R:V):
  runFrom 18 (leftFrame 2 0 (2*R+1)) = frameSparse 84 1 R
```

Starting from leftFrame 2 with an empty left half places the head on a zero
immediately left of the marker. Eight zero/left steps visit states
2,3,5,9,15,23,34,50 and reach 75 at the eighth zero to the left. Nine 75/false
right steps traverse positions -8 through 0, and one 75/true right step
crosses the marker at 1 to state 84/head 2. The original ten specified cells
are unchanged. Algebraically, the eight left steps leave nine zero prefix
bits before 2*R+1; the accepted internal right scan removes those nine bits,
and the final literal step yields left half 1/right half R. All steps are
proved from the actual sparse_step/box scan API, so R is arbitrary internal.
No FramedWindow.arbitrary_tape or KZipTape.run_reflect theorem on Nat tapes
is substituted for this internal identity.

The data audit reconstructs all 226 rows of the literal KTable215 list,
checks the fifteen scanner rows, and records the complete 18-step restored
window trace. That Python audit is only a source/data cross-check. The new
Lean source must kernel-check every required actual table equality and the
literal ready certificate; the audit is not an external proof assumption.

## Numeric scanBound invariant

Use a new local flatValue_append law on arbitrary numeric tails. The main
finite-syntax induction has this exact shape, where i,j,bound are Nat:

```text
scanBound_actual (h : KHome.scanBound i xs = some bound)
  (hi : i<8) (hj : j<=i) (L R:V):
  exists j', j'<=bound and j'<8 and
    Reach
      (leftFrame (KHome.state j) (flatValue gap v k xs L) R)
      (leftFrame (KHome.state j') L
        (flatValue gap v k xs.reverse R))
```

Bits use actual unchanged-write left steps. A false run is accepted only
when its affine coefficient a=0 and i+c<8, so its c finite steps stay in
known states. A true run has internal length n=(a:V)*gap+c. Split n=0 from
n>0. The zero case implies c=0 and preserves the actual counter; the positive
case resets in one actual step and uses the accepted internal state 2/true
scan for the remaining n-1 steps. When c=0 the source checker conservatively
retains bound i, and a nonempty true run may lower the actual counter to 0.
Do not assume that every true run is nonempty or that gap>0.

Every box case is rejected by scanBound, before any interpretation of its
file payload. Reversing a retained bit or constant-bit run is represented
by the same prefix function, so the above output is the precise numeric
reverse fold. No ordinary-Nat list expansion is required for the internal
run lengths. The internal induction already resides in the accepted scans;
this new induction is only over the finite source segment list.

## stripBlank and composition

Prove directly, for arbitrary internal gap/v/k:

```text
KHome.stripBlank l.reverse = some u ->
  flatValue gap v k l 0 = flatValue gap v k u.reverse 1
```

The recursive discarded prefix contains only false bits/false runs.
After reversal these are exterior segments applied to tail 0 and evaluate
to 0, regardless of their possibly nonstandard lengths. The stopping literal
true bit contributes exactly 1. A true run is not silently accepted as that
literal marker; a box also cannot be stripped.

For successful home, q=2 and onLeft=true are literal guards. Apply the scan
invariant to u.reverse, with L=1 and R=flatValue r 0. Its ending state is
state(j') for j'<8. Execute the actual true/reset row once on that marker,
then boundary_actual. The result is exactly
frameSparse 84 1 (flatValue u (flatValue r 0)), which equals interpretation of
(84,false,[bit true],u++r). This composition has a positive clock because
its final boundary has clock 18, even if every prior scan is empty.

For stepper_actual, unfold the actual ready decision once. The ready branch
uses the proved home_actual whenever home succeeds, with flag true; home
failure uses the accepted sstep_actual. The unsupported-table fallback is
irrelevant to the fixed table but can be handled by that same actual step
proof, so no readiness correctness oracle enters the public conclusion.
Then instantiate SymbolicCore.execWith_actual and preserve its moved flag.

Checks should exercise zero gap, empty true runs with nonzero conservative
counter, a genuine nonstandard-length true run, rejection of a box and of
an unbounded false run, stripping only exterior zeros, both failed-home
fallback and successful-home positive flag, boundary R=0, arbitrary R,
actual target matching, and moved=false versus initially true. No examples
may replace the uniform symbolic soundness proof.

## Cache and boundary

Expected closure: 153 cached custom modules, 95 Foundation modules,
438 custom artifacts, 41 boundary primaries plus 123 companions, 602 actual
first providers, zero refresh. This is the accepted Symbolic/Boxes closure
plus exactly KHome, FramedWindow, KZipTape and KHomeReady. Their current
sources and selected objects were already authenticated in the independent
NativeAdaptiveCurrent2011 peer inventory. Complete current import headers
and transitive closure will be rechecked in the accompanying planner.

That native inventory uses a source-identical alternate KZip object:
1230b602... versus the existing Symbolic closure's 5fc974ab.... The source
hash 71edb0ca... is identical. Retain the accepted Symbolic KZip selection,
record the alternate observation explicitly, and do not claim byte identity
for that inherited overlap. There is no new source or logical-interface
change and no Foundation dependency enlargement. The Home module's old
"source-only candidate" comment is historical prose; the selected accepted
objects and source hashes, rather than that comment, determine provenance.

The final plan selects the accepted ROOT Symbolic provider
`/tmp/symbolic-core215-root-d4b0mp1m/lib`, with packet
8102b4470b0f939c6f88ff551eb5a41d165be8113f3cc8c000b538c2059dce26
and manifest 867910edf7f17797ebb39808990fc5074e95f96427a0e707aaf8052f3a0ad12f.
Its full ROOT receipt was read; its two objects match the author exactly.
This proposal itself does not authorize an overlay/compiler. The estimate is
roughly 350–550 lines plus 60–90 focused Checks. Any import enlargement or
refresh requires a revised explicit inventory. Every authorized compiler
would remain private, pinned 4.32, M6000/j1/async=false with the 512MiB reserve,
both input snapshots first and all failed attempts retained.

Home does not establish all-site certificates, physical-register reordering,
canonical-path table agreement, control-to-tape simulation, source-ZFC
interpretation, internal Pell/equation equivalence or an HA proof endpoint.
Those remain later, separately scoped constructions.
