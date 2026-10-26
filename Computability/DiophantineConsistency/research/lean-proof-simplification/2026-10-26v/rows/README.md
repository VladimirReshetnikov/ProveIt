# Two new Wang-row simplifications after the virtual adoption baseline

Pinned source: `22e020937caa81d0cb72a4f63071d6c0bcc1eba9`.

**Status:** concrete **uncompiled** Lean proposals and textual patches, not
validated Lean changes. No speedup, kernel acceptance, axiom-audit result or
full-project compilation is claimed. The source snapshot is untouched.

The prior-work audit screened both proposals against the six placed packets,
five incoming ZIPs, and round-two ideas. Neither repeats the copied-field
direction descriptor, finite-table certificates, optional masks, or NorthView.
In particular, the new edge abstraction concerns a *spatial bond*, not the
direction-specific rail alphabet or copied native-field offsets.

## R1. Guarded integer induction replaces two natural offset recursions

Target: `WangTiles942ResetRows.lean:43–73`, `interval_propagate`.

Keep its exact signature. For the translated coordinate `z`, induct on

```
l < x₀+z → x₀+z < r → P (x₀+z).
```

The positive successor uses the rightward local rule. The negative predecessor
uses the leftward local rule. The hypotheses `l < x₀` and `x₀ < r`, together with
nonnegativity of the natural branch index, provide the opposite intermediate
bound in the two branches. Finally use `z = x−x₀`.

This removes both explicit `Nat` recursions, both `.toNat` endpoint witnesses,
and the final sign split. It does **not** remove either propagation direction,
weaken open-interval guards, or assume reset behavior outside the strip.
`Int.induction_on` is already used with the same `zero/succ/pred` branches in
`WangTiles942SeamColumns.lean:43–49`; this is a new guarded client, not a new
unverified library API. Existing reset/finish propagation clients are unchanged.

With the declaration signature counted, the replacement span is 31 → 23
nonblank code lines and 1,416 → 950 UTF-8 bytes. Its proof body is 26 → 18
lines. There is no helper overhead elsewhere. These are textual, not
elaborated proof-size or runtime measurements.

## R2. One spatial bond pulse shares both edge proofs

Target: `WangTiles942StepConstruction.lean:116–148`.

Let `h` be the old head, `h'` the actual moved head, `d` the actual action
direction, and `r` its actual target rail. Define the left endpoint

```
b = if d then h else h'
E(x) = if x = b then r else 0.
```

The simultaneous constructor lemma derives

```
(stepTile cfg q x).west = E(x−1)
(stepTile cfg q x).east = E(x).
```

For a right move `h' = h+1`, the transition east and receiver west share
the bond beginning at `h`. For a left move `h' = h−1`, the transition west
and receiver east share the bond beginning at `h'`. All other edges are
zero. The helper first proves the single translated support equivalence,
then reduces the **existing** transition/receive/pass constructors in one
shared old-head/new-head/direction case split. `nextHead_ne` excludes the
impossible old-and-new-head branch. No horizontal matching premise is used.

Horizontal matching then follows from `(x+1)−1=x`, rather than another
case split by action direction. Neither the 942-tile table, action decoding,
rail arithmetic, `stepTile`, `receiveTile`, tape, target set nor the whole-row
construction changes. Target 215 and both action directions remain included.
No finite-strip conclusion or absence-of-finish claim is added.

### Exact API and size trade-off

The leanest patch normalizes `stepTile_west` and `stepTile_east` to the pulse
formulas above. Their *names* remain, but their statement forms change.
All other public theorem statements, including `stepTile_horizontal` and
`step_row`, remain unchanged. A pinned-source search found these two edge
lemmas used only by the old horizontal proof and by `#print axioms` commands.
Unknown external callers still require a migration check or legacy adapters.
Such adapters are **not** included in the quoted size comparison.

All new definitions and paired-lemma overhead are included: the replaced
span is 33 → 33 physical lines, 28 → 29 nonblank code lines, and
1,912 → 1,553 UTF-8 bytes. Thus this is **not a line-count reduction**.
Its value is one shared edge certificate and making matching a translation
identity. The source has two separate 8-branch constructor proof trees and
one 2-branch geometric proof; the proposal has one 2-branch support proof
and one shared 8-branch constructor tree. This is a syntactic branch count,
not measured tactic execution or proof-term complexity.

## Files and evidence

- `IntervalPropagationCandidate.lean`, `BondPulseCandidate.lean`: standalone
  review probes importing the unmodified pinned modules. Every proposed public
  theorem has a fully qualified `#print axioms` command; none was executed.
- `proposed/`: complete proposed modules, retaining the rest of each original.
- `*.lean.patch`: source-relative integration diffs.
- `build_patches.py`: regenerates the full proposals, patches, and `METRICS.json`.
- `check_semantics.py`, `SEMANTIC_CHECKS.json`: **bounded Python QA only**.
  All 430 parsed action-cache entries were sampled at four head coordinates,
  both plain/receiver bits and nine local positions: 30,960 edge-and-matching
  checks, including 5,904 left-move and 72 halt-entry samples. The target lists
  were compared with the actual parsed action cache. 2,582 finite
  interval/predicate/seed instances were checked; all 84 satisfying the
  original premises obeyed propagation. These checks neither elaborate Lean
  nor replace the all-integer proof or existing decoder certificate.

## Integration acceptance gate

1. Run Lean with the pinned toolchain and dependencies on both probes and the
   two patched modules. Resolve any elaboration issue without widening the
   statements or replacing an actual construction by its desired specification.
2. Run both original `WangTiles942ResetRowsChecks` and
   `WangTiles942StepConstructionChecks`, plus dependent strip/run checks.
3. Inspect fully qualified axiom audits: no `sorryAx`, new axioms, or native
   decision trust introduced by these proposals.
4. Search the full adoption branch and downstream clients for uses of the two
   normalized edge APIs. Retain legacy wrappers if needed and recount overhead.
5. Only after successful compilation consider removing now-unnecessary local
   resource options. None is removed or credited here.
