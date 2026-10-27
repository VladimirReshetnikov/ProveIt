# Actual 215 symbolic execution after register boxes

27 October 2026. This is a read-only proposal. It creates no Lean source,
compiler invocation or object overlay. The proposed first pair is
`ArithmeticSymbolicCore215` and focused Checks, importing only
`DiophantineConsistency.ArithmeticRegisterBoxes215`.

The accepted ROOT Box provider is
`/tmp/register-boxes215-root-hzd4elpy/lib`. Its frozen ROOT replay is
`db5dc321c4511cfe6c8388c1e51c16a54caf61f24b7c8aa4a07cc353ad9f7c8f`;
the 15-file manifest is
`a068d6dedfafe2ac8f1368ae5a7d519cf067bb7e2a55ee8d857990f2db2a33ec`.
This follows the independent clean Prefix/main/Checks triple, with all
objects, full logs and 14 reports identical to the final author attempt.
The old pre-final warning and its source snapshot remain historical.

## First useful theorem

Interpret the actual `KRuntimeCore.Seg`, `SConf`, `sstep tm215`,
`execWith`, `norm`, `normL` and `sMatches` in arbitrary internal arithmetic.
Use only their syntax and finite recursion; do not use their ordinary-Nat
execution theorems. The public endpoint should have this shape:

```text
variable {V} [ORingStructure V] [V models IΣ1]
gap : V, v : Fin 9 -> V, k : V, 0 < k
br : KRuntimeCore.Branch, BranchValid br v

sstep tm215 br s = some (s', moved) ->
  Reach (interpret gap v k s) (interpret gap v k s') and
  (moved = true -> ReachPos (interpret gap v k s) (interpret gap v k s'))

exec tm215 br target fuel s false = some s' ->
  target s' = true and ReachPos (interpret gap v k s) (interpret gap v k s')

sMatches s e = true -> interpret gap v k s = interpret gap v k e
```

The configurations, segment spines, branch and fuel are finite checked
syntax. Register values, spare count, affine gap and resulting execution
clocks range over the model, including nonstandard values. This theorem
does not restrict them to Nat or assume an execution premise. The finite
executor induction is on its source-level fuel; the needed internal scan
inductions have already been proved in Boxes under IΣ1.

## Exact representation and proof obligations

For a tail z, use the fixed nine-block fold followed by `repeat3 6 k z`.
For a selected primary r, marking erases its first one; increment updates
v(r) and uses k+1; decrement updates v(r)-1 and keeps k. These agree with
the accepted four Box endpoints at tail0. A box occupies the complete
right tail whenever the actual executor invokes its oracle.

Define a total interpretation of all finite box syntax. For indices
outside 0..8 use an explicitly documented plain-file fallback. This
fallback is not asserted to match the old Nat `boxList` there. All actual
oracle-success cases prove r<9 from `skipTarget_sk` or the literal guard;
the remaining raw-head step only needs every interpreted box to begin
with zero. Thus no unproved physical-index premise is hidden in the
public `sstep` theorem. Alternatively, an implementation may retain an
explicit syntactic safety predicate and prove it is preserved, but must
report that interface change before broadening the scope.

Interpret a bit as `b + 2*z`; a run as `bitPrefix b (a*gap+c) z`.
Interpret a segment list by folding these functions onto zero. Interpret
the left-head flag with the exact accepted `leftFrame` zipper,
`F(q,L/2,L%2+2*R)`, and the right-head flag with `frameSparse`.
`BranchValid` reads an actual primary value when r<9, with a total zero
fallback otherwise. It imposes exactly the stated zero/nonzero branch,
and no unsupported r can pass the oracle's guard.

The complete `sstep` case proof has four ingredients:

1. Recentering a bit or an empty left half is numerical equality. Peeling
   a run uses `(a*gap+c)+1 = a*gap+(c+1)`. These may have zero clock.
2. A literal machine bit step follows `Tape215.sparse_step` with the
   actual `tm215 q bit` equality obtained from `sstep`. Its clock is1,
   including the final write/move before terminal state230. The existing
   supported-row binding handles sparse-state holes.
3. Self-loop runs use the accepted internal `scan_left`/`scan_right` with
   length a*gap+c and exact written bit. A zero-length run is legal and
   the checker marks these cases false.
4. Oracle success uses `box_mark`, `box_inc`, `box_dec0`, or `box_decp`,
   with the exact positive-DEC extra left bit and incremented spare
   count. Its checker flag remains false although the proved clock is
   positive. Oracle failure followed by a zero/read-left transition uses
   the proved zero head of the complete file, not a supplied box axiom.

Prove a numeric `StepOk` and a finite `execWith` composition lemma. The
public `exec` client discharges the latter's step premise with the above
actual215 proof. The generic helper is not a caller-supplied correctness
premise at the public endpoint. Preserve the moved flag exactly: only
starting false and successfully satisfying `moved && target` yields the
positive-clock theorem.

For normalization, interpret `Tok` numerically and prove push/fold laws
using prefix addition. `normL` drops only exterior zero runs; their tail
is zero, so the *entire* arithmetic configuration is equal. No tape-trim
or ordinary-Nat semantic theorem substitutes for this equality.

Include the ordinary-Nat algebraic client left open by Boxes: for every
Nat tuple, spare k and valid primary r, `plain` and `marked` equal
`bitsCode (sepsR ...)` and `bitsCode (sepsM r ...)` on
`List.ofFn v ++ List.replicate k 1`. Likewise bind the increment/decrement
forms, retaining the appended spare1. These are finite-list/bit-code
identities, not the proof of internal execution. Existing syntax-only
`KRuntimeCore` is already reachable through the selected cache. No KTape
or old252 execution import is needed for these statements.

Expected main size is about450–650 lines, including total interpretation,
normalization and the ordinary-Nat algebraic client, plus60–90 Checks.
Checks should include zero gap and zero-length runs, all primary r,
last-primary DEC0 with k=1, INC and positive DEC representations, both
head orientations, fallback-only boxes, final terminal move, and the
strict moved=false/start requirement. No all4751-site conclusion is
claimed merely by testing a few symbolic configurations.

## Exact proposed cache

The accompanying planner selects only the accepted Box main and its
current reachable header closure. It replaces the formerly refreshed
Prefix by the accepted fresh ROOT Prefix object, and retains original
historical provenance as data. Expected counts are148 cached custom
modules,95 Foundation modules,433 custom artifacts,41 package/stdlib
primaries plus123 companions,597 first artifact providers. No dependency
refresh or Foundation build is proposed. Only two fresh regular outputs
would be compiled after approval, with M6000, j1, async=false and the
512MiB guard; inputs and failed attempts would be preserved.

## Subsequent coherent checkpoints, not this implementation

* **Home.** Prove actual states2,3,5,9,15,23,34,50 consume the symbolically
  bounded zero streak, using internal true-run scans and the checked
  state successor/reset equations. Then prove the exact18-step boundary
  from the left-facing state2 marker to sparse84. Interpret the existing
  `KHomeReady.stepper/exec` using the first leaf. `stripBlank` must remove
  only numeric exterior zeros. No box may be swallowed by a home scan.
  Adding KHomeReady/KHome/FramedWindow syntax and data will require its
  own exact source/object/import audit; it is not an implicit import here.
* **All4751 sites.** Consume every actual `KSites215` Boolean certificate
  (105 blocks, nine batches), with physical order
  `[2,8,1,4,3,7,0,5,6]`. Prove physical-file reorder and the complete
  edge contracts, including c=0/branch distinctions, path overflow,
  positive-DEC gap growth and INC spare growth. The current statement's
  finite fuel4000 remains source syntax; execution clocks are internal.
  No caller-supplied row/site correctness or ordinary-Nat simulation.
* **Canonical control relation.** Bind each accepted Control215Table
  entry to its canonical path via the genuine catalogue lookup/crank
  theorem, retaining path zero-padding. Relate live control pc/file to
  the exact arithmetic tape frame with internal k>0 and gap. Boot is the
  accepted95714-step state84 frame, gap1,40 spare ones and physical tuple
  `[0,0,0,0,0,0,4,0,0]`. Prove positive actual site clocks and halt
  preservation before applying the accepted positive simulation theorem.
  This yields control halt iff actual215 blank halt at arbitrary internal
  times, then composes BisimPerm215 and RuntimePerm222. Source-ZFC,
  arithmetic Pell/equation and final HA proof existence remain distinct.

This proposal is authored by the Box/Tape author. It requests no independent
acceptance claim for its own new work and makes no compilation claim.
