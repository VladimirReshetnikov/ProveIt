# Geometry proposal: bound the whole initial strip by one period

## Result

Add `initial_width_le_period` in `WangTiles942StripGeometry`:

```lean
theorem initial_width_le_period {T : ℤ → Tile} {N L R : ℕ}
    (h : InitialStrip T N L R) (hperiod : Function.Periodic T (N : ℤ)) :
    L + R ≤ N := by
  have hN : 0 < N := lt_of_lt_of_le h.left_pos h.left_le
  by_contra hwidth
  apply (initial_vertical_nonseam h (-(L : ℤ) + (N : ℤ)) (by omega) (by omega)).1
  exact (congrArg Tile.north (hperiod (-(L : ℤ)))).trans h.wall_north.1
```

`InitialStrip` already supplies a seam at `−L` and excludes seam colors strictly
between `−L` and `R`. Periodicity supplies the same seam at `−L+N`. If
`L+R>N`, that translated seam is strictly inside the interval; contradiction.
Positivity of N follows from `0<L≤N`, so no new instance or positivity premise
is required in the project statement.

This is the specialization of the small abstract result `gap_le_period` in the
fixture: for an arbitrary function `T : ℤ → α`, arbitrary predicate `Seam`,
positive integer period p, a seam at l, and no seam in `(l,r)`, one has `r−l≤p`.
There is no need to introduce this generic helper in production; the direct
four-line body is sufficient.

## Payoff and limits

The current `WangTiles942SoundnessChecks.marked_period_gt_two` derives N>2 from
`marked_halts_before_period` and the concrete machine's liveness at times 0
and 1. Instead, obtain `InitialStrip`, use `L+R≤N`, and combine its existing
`L≥1` and `R≥2`. This makes the obstruction available from StripGeometry,
before operating-row simulation and machine soundness, while preserving the
existing public theorem as a one-line alias.

This is primarily a stronger theorem and a reduction in proof dependencies.
The included candidate patch changes the old client body from 9 lines to 1,
but adds two reusable declarations, so the total source grows by 11 lines.
Do not claim a net code-size reduction or measured speedup. The existing
SoundnessChecks module still imports Soundness for its other declarations;
only new clients can import the earlier geometry layer alone.

## Boundaries and assumptions

* The inequality is non-strict: if `L+R=N`, the translated seam equals the
  right boundary, where seams are permitted. The uncompiled larger fixture
  includes a candidate InitialStrip with N=3,L=1,R=2 and period 3.
* The period need not be minimal; no coprimality, unique Start, temporal
  matching, machine transition or halting fact is used by the width proof.
* The abstract gap theorem needs positive p: p=0 is always a period and
  cannot bound a nonempty gap. The actual InitialStrip premise already
  excludes N=0 via `left_pos` and `left_le`.
* The width proof uses only the left seam and the seam-free interior.
  There is no implicit assumption that left/right seams occupy distinct
  residues. The right-wall field remains unchanged.
* Do not remove or weaken InitialStrip fields as part of this proposal.

## Source anchors

Pinned source: 553a5f7a463cbaab8800ff8148fef0bc5a9e1b22.

* WangTiles942InitialStrip.lean:23–33: exact fields; 132–137: `wall_north`;
  140–146: `marked_initial_strip` and its horizontal-period adapter.
* WangTiles942StripGeometry.lean:22–48: exact interior classification and
  nonseam theorem.
* WangTiles942Periodic.lean:71–74: `plane_horizontal_period`.
* WangTiles942SoundnessChecks.lean:28–40: current period obstruction.

Soundness already imports StripGeometry transitively through RowStep,
HeadBounds, OperatingRow and RowEncoding, so the preserving alias needs no
new import. The patch is supplied for review and was not applied.

## Novelty audit

No proposed seam-gap/strip-width/period comparison was found in the six initial
placed packets, twelve initial incoming archives, or the three packets added
at closing (s-u). Earlier finite cyclic
coordinate, propagation and boundary-color proposals do not establish this
geometric spacing inequality. This is a corpus-scoped finding, not a claim of
mathematical novelty beyond the repository review.

## Validation

**Checked:** `StripWidthCore.lean` imports only Lean.Elab.Tactic.Omega and
proves the generic Int/Nat seam-gap theorem with an iff-periodic seam
predicate, then the numerical consequence N>2. It compiles with pinned
Lean 4.32.0 (`-j1`), exit status 0. Both reported axiom lists are exactly
`[propext, Quot.sound]`; neither contains sorryAx or a custom axiom.
See `core-validation.json` and `StripWidthCore.log`.

**Not checked to completion:** `StripWidthKernel.lean` imports pinned
Mathlib, copies the exact Tile/start/InitialStrip/wall_north/initial_tile/
initial_vertical_nonseam declarations into a local namespace, and contains
the candidate direct proof, a factored generic version, and an explicit
period-3 equality-boundary example. Its first narrow-import run timed out
after 300 seconds under shared CPU contention without diagnostics. A
longer retry was stopped to avoid unproductive repeated compilation.
The fixture is supplied as reviewable source, not successful kernel evidence.
The equality-boundary candidate in that file must not be called compiled.

**Production integration remains unverified:** the complete WangTiles
module chain was not rebuilt. The exact source adapter and API-preserving
patch have been reviewed against the pinned statements. `validation-summary.json`
records these separate levels. No project theorem was introduced as a new axiom.
