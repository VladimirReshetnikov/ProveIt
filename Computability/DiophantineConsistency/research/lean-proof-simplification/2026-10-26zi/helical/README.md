> FINAL NOVELTY OVERRIDE: H1/H2/B1 are superseded comparison evidence, not new proposals. See `../late_review/` and the final report. This original source-only review does not incorporate the late novelty screen.

# Helical/cycle candidates H1 and H2

**Status: research-complete; Lean uncompiled.** No Lean runtime, package installation, or upstream source edit was attempted. Proposed files and replay copies are separate from the pinned source snapshot. These two patches compose and introduce no import changes.

## Findings first

- **H1 — signed helical transport by an existing periodicity theorem.** `WangTiles942HelicalQuotient.row_zero_of_helix` can reuse `Function.Periodic.zsmul` on `ℤ × ℤ`, removing its private positive/negative-time induction. The original theorem's arbitrary `w : ℤ`, `x : ℤ`, and `t : ℤ` remain unchanged. Body: 16 → 7 physical lines; entire file: 147 → 138.
- **H2 — one concrete band descent certificate.** Add `WangTiles942CycleBand.band_quotient_properties`, whose witness is *the literal existing* `quotientWord (extend (band L H) ...) ...`, and whose conclusion bundles matching with every original-band tile binding. The existential endpoint and the uniquely marked canonical endpoint become projections of this same result. Original endpoint bodies total 40 lines; replacement bodies plus helper proof total 21. Full two-file size falls only 291 → 287 because all 15 lines of new statement/comment/spacing are charged. This is a maintainability simplification, not a claimed performance result.

Combined: 438 → 425 full file lines (−13); 56 → 28 selected proof-body lines (−28), including the added helper's proof. New definitions: 0. New theorem declarations: 1. Removed theorem declarations: 0. Original public signatures and `canonicalWord` definition preserved byte-for-byte.

## Exact source anchors

All ProveIt anchors refer to commit `e652d21c413de59e4821f6e8e9b6a3a077bf5bfe`; paths below are relative to `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| Candidate | Original target | Lines | Supporting original API |
|---|---|---:|---|
| H1 | `WangTiles942HelicalQuotient.lean`, `row_zero_of_helix` | 22–40 | `row_zero_period` 53–59; `quotientWord_binding` 87–95 |
| H2 | `WangTiles942CycleBand.lean`, `marked_word_of_halt` | 136–165 | `band_properties` 119–131; `extend_on_band` in HelicalExtension 52–56 |
| H2 | `WangTiles942BandMarker.lean`, `canonicalWord_properties` | 79–106 | unchanged literal `canonicalWord` 47–52; marker theorem 56–75 |

`candidate_manifest.json` gives direct line-anchored URLs and source blob/SHA-256 values. All three edited modules are new in the 608→637 active Lean-file delta from `22e020937caa81d0cb72a4f63071d6c0bcc1eba9` to this pin.

Library source: mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`, exactly the repository's `lake-manifest.json` pin. `Mathlib/Algebra/Ring/Periodic.lean` lines 155–158 define `Function.Periodic.zsmul` for any additive group. A byte-verified source copy is in `dependencies/Periodic.lean`; Git blob SHA-1 `71fcf017b9bc3e6a58d2520ebf317ad0abd69b9f`.

## H1 proof argument and implementation

Let `F (x,t) := T x t`. The supplied helix hypothesis is precisely periodicity of `F` under `(w,-1)`. The existing integer-multiple closure gives

`F ((x,t) + t • (w,-1)) = F (x,t)`.

The left argument is `(x+w*t, 0)`. Symmetry therefore gives exactly the old conclusion, including negative times and negative/zero widths. No finite quotient or coprimality construction is needed. The actual seven-line replacement is in `patches/H1.patch`; it uses two explicit `change` statements to keep product reduction and scalar normalization visible.

**Elaboration points still to verify in Lean:** product addition and integer scalar multiplication reduce as expected at the two `change` steps; `simpa only [zsmul_eq_mul, mul_neg, mul_one, add_neg_cancel, mul_comm]` normalizes the endpoint. The library theorem name and signature have been checked in pinned source, not merely guessed from current documentation. No elaborator result is claimed.

## H2 stronger shared conclusion

Previously `CycleBand.marked_word_of_halt` assembled all six extension properties, called the existential quotient endpoint, then restricted the binding to `[-L,R)`. Independently `BandMarker.canonicalWord_properties` assembled the same extension properties, called the concrete quotient endpoint, and repeated the same restriction. The new helper moves the common proof *before* existential packaging and marker enrichment.

Its conclusion deliberately binds the actual quotient word rather than saying that some word exists. Thus the second consumer can identify it by definitional reduction with `canonicalWord`; no word equality theorem, new choice, injectivity assumption, or uniqueness assumption is needed. The original `canonicalWord` body is unchanged. Proof irrelevance only handles the routine equality of proof arguments to unchanged definitions; the index function itself is the same expression.

**Preserved guards and geometry:** actual halt `hh`; independent bounds `T+2≤L`, `T+2≤R`, `T+2≤H`; `3≤H`; nonzero finite height/modulus; positive total width; signed arbitrary `t`; left wall included and right wall excluded; exact twisted boundary `(R-1,t)` to `(-L,t+1)`. No requirement that `L=R`, `H=L+R`, `gcd(L+R,H)=1`, or `uniqueStart` is added. Marker uniqueness remains separately proved by the unchanged marker theorem.

**Elaboration points still to verify in Lean:** the goal's leading `let a := ...` is reduced while constructing the conjunction; `hp.1` and `hp.2` elaborate against the unchanged `canonicalWord`; existential witness inference in `⟨_, hp.1, hp.2⟩`. If elaboration needs explicit `change` or witness annotations, count those lines in revised metrics rather than claiming the present count.

## Virtual-baseline increment and exclusions

The source corpus is not the novelty baseline. All proposals in `research/lean-proof-simplification`, `docs/incoming`, and the six round-three proposals are assumed already applied. The final prior-work audit of all 21 packet manuscripts and technical notes found no matching concrete helical/canonical-band assembly or signed-period client. H1 and H2 were retained under the narrow claims below.

H1 is specifically reuse of an existing integer-period closure in a **new** signed transport theorem; it does not claim a new generic quotient/action framework. H2 is specifically the **new** literal computation-band descent certificate used by two concrete construction endpoints. Neither proposal counts generic residue normalization, word wrappers, finite tile dispatch, NorthView classification, translated-interval induction, shared spatial bond pulses, or last-slot/control action normal forms as new work. Their selected target bodies survive those assumed transformations; source-sized deltas therefore measure the incremental patch, not a re-count of prior generic work.

Rejected/omitted as fresh headline ideas:

- `HelicalExtension` floor/remainder reconstruction and successor normalization: overlaps the residue/coordinate baseline.
- `HelicalMarker` or `BandMarker` replacing tile-equality branches by injectivity rewriting: a small local spelling change on an existing finite-tile API, not a new structural contribution.
- `CycleMarker` fusing constant-color case splits: finite dispatch/NorthView baseline overlap.
- `CycleBoundary.runTile_outer_blank` translated-interval or bound repackaging: translated interval/run-row baseline overlap; run-row semantic changes belong to the other researcher.
- `timeIndex` and seam-period normalizations: already short coordinate-wrapper proofs.

## Validation actually performed

Run from the round-four folder:

```sh
python helical/validation/test_candidates.py
```

An independent source-only review by the construction-bridges researcher found no semantic gap in H1/H2; it did not claim compilation. Ten tests passed: exact source identity against the final pinned manifest; proof targets are new active files; pinned mathlib blob identity/API; both patches apply together in disposable copies and reproduce proposed modules; unchanged old signatures/imports/word definition; no unsafe placeholders or new special guards; duplicate descent count 2→1; bounded signed group-action model; independent-dimension and signed-time quotient-binding model including the excluded right wall; literal full-file metrics.

The models do **not** prove Lean elaboration, actual-machine halting, actual tile membership/matching, or performance. No `lake`, `lean`, build, axiom-output check, or runtime timing was run. `validation/HelicalCandidatesChecks.lean` is a fully qualified check/axiom-audit target to run only in a separately authorized Lean checkout after applying the patches. The copied standard-library file is evidence only; it must not be added as a competing local mathlib module.

## Files

- `patches/H1.patch`, `patches/H2.patch`: independent candidate patches.
- `proposed/*.lean`: complete intended replacement modules.
- `build_proposals.py`: reproducible source-to-proposal/diff/metric generation.
- `metrics.json`, `candidate_manifest.json`: machine-readable accounting and anchors.
- `validation/test_candidates.py`, `test_results.txt`: non-Lean checks and observed result.
- `validation/HelicalCandidatesChecks.lean`: **unexecuted** Lean audit target.
- `helical_section.tex`: optional report fragment; parent controls final TeX/PDF/ZIP packaging.
