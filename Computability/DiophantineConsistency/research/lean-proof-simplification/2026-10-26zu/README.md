# Three further Lean proof simplifications

**For Vladimir Reshetnikov's ProveIt, 26 October 2026.**

Start with `report.pdf`; `report.tex` and `validation-summary.tex` are its
complete editable LaTeX source. This packet treats earlier simplification
proposals as already available. It contains three deliberately narrow
contributions, with patch files, complete candidates, proof cores, and an
exclusion audit. It does not claim that all candidates have passed a fresh
whole-repository build.

## Findings

| Direction | Contribution | Honest marginal source accounting |
|---|---|---|
| Shape balance | The two raw `Expr.splitNatural` trees have the same operation-labelled shape after erasing all leaf labels. A scalar fold replaces paired size metadata. | `ExpressionSize.lean`: 90 to 81 lines, including the scalar helper. The optional separate shape-theorem API is not included in this count. |
| Full-exponent growth | In `CurrentPackingRank2011.rank_gt_twice_window`, use `2u ≤ 3u < 2^(3u) = q^3` directly. | Complete module: 138 to 133 lines. No helper or import is added. |
| Monotone windows | Share an index-uniqueness lemma for half-open windows and use it in the residual square-pairing proof. Division is already prior work and serves only as compatibility evidence. | Against packet y: pairing 100 to 94, plus a new 22-line helper; **16 lines added overall**. Optional structural simplification. |

Line counts are physical lines in the stated files. They do not measure proof
term sizes or performance. These alternatives are not presented as a combined
net saving against an imaginary checkout containing every historical proposal.

The shape change preserves metadata values for every input, but changes a
computational definition. Consumers that rely on symbolic unfolding require
integration checks. The exact shape theorem applies to raw splitting and
leaf-insensitive interpretations, not to independently simplified trees,
semantic values, variable supports, or coefficient-sensitive costs.

## Provenance and non-repetition

The proof snapshot is
[`9d9d1123b39927d30363f1dcd53c23f0575c30ee`](https://github.com/VladimirReshetnikov/ProveIt/commit/9d9d1123b39927d30363f1dcd53c23f0575c30ee).
It selects Lean 4.32.0 and Mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`.

The initial exclusion audit covers all 36 placed packets (a through zj) and
all five incoming archives at that snapshot. See `audit/prior_art_inventory.json`,
`audit/prior_art_notes.md`, and `audit/prior_art_final_novelty.json` for exact
paths, hashes, rejected overlaps, and audit limits.

The final freshness cutoff is
[`60fcb2a69b7f1fdd4c3592ea5f164223cad50abe`](https://github.com/VladimirReshetnikov/ProveIt/commit/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe),
committed at 19:10:07 UTC on 26 October. The final registry contains **43 placed
packets**. All 36 original trees are unchanged; all 328 retained substantive
files in zk–zo match the five audited archives. The two new packets zp/zq were
reviewed through 40 blob-verified text/code files. Their additional ideas are
excluded too. All six direct target source files are unchanged. See
`audit/prior_art_refresh.md` and `audit/prior_art_refresh.json`; source freshness
does not mean a fresh dependency-closure build.

In particular, generic ordered-semiring division uniqueness is explicitly
treated as prior work. The window proposal is one shared boundary interface,
not two separate new ideas. Its main patch is rebased onto packet y and
preserves the earlier shell-cut and two-branch argument. Neither broad
metadata folding nor reuse of existing count projections is credited as new;
the additional invariant is exact shape equality and diagonal reachability.

## Files

- `shape/`: complete original/candidate metadata module; optional generic
  shape theorem; universal exact-source checker, generator, hashes, and logs.
- `growth/`: complete original/candidate rank module; one-theorem patch;
  standard-library arithmetic checker and its log.
- `windows/`: post-y baseline, patch, complete candidate/helper, generic
  namespace checker, preservation evidence, metrics, and logs.
- `windows/compatibility_current_head/`: explicitly uncredited illustrative
  adapters against the proof snapshot. Do not use their line counts as
  marginal savings and do not combine their patch with the main window patch.
- `audit/`: the exclusion review, independent shape review, and final freshness
  evidence.
- `checks/`: portable replay and patch-consistency tools.
- `SHA256SUMS`: hashes of all delivered files except this manifest itself.

Complete baseline and candidate Lean files contain material from the pinned
ProveIt source. The source links and hashes identify their provenance.

## What passed

1. `ShapeCore.lean`: exact hash-verified source extraction, with only documented
   notation normalization. Proves generic shape equality, erased-tree
   equality, equal raw counts/depths, scalar correctness, old-fold diagonality,
   and universal equality of the old/new metadata. Imports only
   `Lean.Elab.Tactic.Omega`.
2. Complete `SplitShape.lean` and candidate `ExpressionSize.lean`: elaborated
   and emitted objects using cached repository prerequisites. Two prerequisite
   sources predate assignment-proof refactors; pertinent definitions agree.
   This is not a fresh dependency-closure build.
3. Complete `OrderedWindow` helper and complete generic `MaxSquarePairing`
   namespace from the post-y candidate: compiled. The internal-natural wrapper
   was outside this check.
4. `FullExponentGrowth.lean`: compiled with the standard library, including
   the natural-to-integer endpoint under explicit lower/cast hypotheses and
   zero/one examples. The full packing-rank module was not rebuilt.
5. All three patches apply to their included exact baselines, and applying
   them in temporary trees reproduces the included candidates byte-for-byte.

Printed theorem audits contain no `sorryAx`. The reports distinguish the
usual `propext`, `Quot.sound`, and (for generic pairing) `Classical.choice`.
No fresh full repository build or measured performance gain is claimed.

## Replay without changing a checkout

Requirements: Python 3, Git, and Lean 4.32.0. From this packet's directory:

```sh
python3 checks/check_patches.py
python3 checks/replay_cores.py
```

An explicit compiler can be selected with `--lean /absolute/path/to/lean`.
The core replay requires no Mathlib or ProveIt dependency cache.

To regenerate the exact-source shape checker using the pinned checkout:

```sh
python3 shape/generate_shape_core.py --repo /path/to/ProveIt
python3 checks/replay_cores.py
```

The generator verifies the complete input file hashes before extracting.
It overwrites this packet's generated checker and manifest with regenerated
versions; it does not modify the checkout.

To replay the generic window checks with a configured ProveIt checkout and
its pinned Mathlib cache already available:

```sh
python3 checks/replay_windows.py --repo /path/to/ProveIt
```

This creates the new helper object in a temporary directory and checks the
generic pairing namespace. It does not claim to compile the internal wrapper.
The script requires the existing Lake environment; it does not set up or
download dependencies for the user.

## Applying proposals and integration checks

Review each patch independently. The shape and growth patches target the
proof snapshot. The main window patch targets the **included post-y baseline**,
not the unmodified maintained pairing file. Use an isolated working tree for
experimentation and preserve the prior shell-cut change.

After manually applying a candidate in a configured repository, focused
integration targets are:

```sh
lake build DiophantineConsistency.CurrentPackingRank2011
lake build DiophantineConsistency.ExpressionSize
lake build DiophantineConsistency.BoundedForallSize
lake build DiophantineConsistency.BoundedForallDepth
lake build DiophantineConsistency.ObjectPairingInjective
```

Run the relevant existing check modules and compare theorem axiom reports.
The report recommends the small growth patch first, then scalar metadata,
and the optional window abstraction last. These build commands are suggested
remaining integration work, not a record of successful checks in this packet.

## Rebuild the report

Use XeLaTeX with the packages named at the top of `report.tex`, and Latin
Modern, DejaVu Sans, and DejaVu Sans Mono fonts:

```sh
sh build-report.sh
```

Two passes resolve the table of contents and equation references. The
delivered PDF was rendered and visually checked; no compiled Lean dependency
caches are distributed.
