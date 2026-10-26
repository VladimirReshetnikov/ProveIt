# Further Lean proof simplifications

Prepared for Vladimir Reshetnikov, 26 October 2026.

Read `report.pdf` for the complete review; `report.tex` and `sections/` are the editable source.

## Three retained recommendations

| Proposal | Exact target | Measured source change | Check |
|---|---|---:|---|
| Reuse the integer Pell norm | `ThirteenFreshSeed.auxiliary_exists`, two norm goals | 217 → 210; 7 lines removed | Complete modified module passed |
| Consume the existing additive square identity | `SignedPellResidue.signed_residue_cases` before `Pell.eq_pell` | 102 → 99; 3 lines removed | Complete modified module passed |
| Decode with the canonical prime residue | `BoundedForallCertificate` and shared `MRDPCore` decoder | Combined 489 → 500; 11 lines added | Arithmetic helper and complete focused forward decoder passed; full real-module integration unverified |

The two Pell patches introduce no helper or import and preserve existing theorem statements. They save ten lines together. The residue proposal is an optional conceptual simplification, not net source compression: its 17-line helper replaces two 8-line client blocks by 5-line blocks. It leaves the certificate and polynomial expressions unchanged. It defines `j i := a i % p` after the original prime divisor has been selected.

The new arithmetic interface, with natural truncated subtraction, is:

```lean
p ∣ ∏ t ∈ Finset.range (u + 1), (a - t) ↔ a % p ≤ u
```

It assumes `p.Prime`; it does not assume `u < p`. Composite moduli do not work in general (`p = 6, a = 3, u = 1`). It removes the per-coordinate factor choice/minimum from the decoder, not selection of the prime or the reverse CRT construction.

## Novelty scope and frozen revisions

- Source and patch baseline: `96520cd1a5179f470b4da127bd47bc26a8d808ff`.
- Closing novelty/source comparison: `3b51c69d42ff99bc420698532af3fe1d1f9bd356` (commit time 2026-10-26 19:32:32 UTC).
- Exclusion screen: 43 research packets, the original incoming ZIP, and six ZIPs added during the closing interval, plus the relevant incoming README material.
- Optional, uncompiled and earlier related proposals are treated as already applied. Their adoption status is not used to manufacture novelty.
- The three target source files were unchanged between the two pins, and their closing bytes were checked independently.

The larger whole-support normalization candidate was withdrawn after a new incoming boundary-conservation proposal supplied its same architectural payoff under the required prior-applied assumption. Its checked numerical theorem and uncompiled adapter are retained **only as withdrawn audit evidence** in `screened_out/aggregate_safe_support/`. They are not a fourth recommendation, and no savings are credited to them.

The exclusion ledgers and `evidence/late-head-audit.md` explain the nearest-prior distinctions, not merely keyword absence. This review does not claim global mathematical originality or coverage of future commits.

## Verification boundaries

The compiler was Lean 4.32.0, release commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`; the repository pins Mathlib to `81a5d257c8e410db227a6665ed08f64fea08e997`.

Both full modified Pell modules compiled with cached baseline dependencies. Their direct imported source files match the pinned Git tree. These checks are not a clean transitive rebuild or a build of a hypothetical tree combining every earlier proposal.

`CanonicalResidue.lean` and `CanonicalDecoder.lean` both passed. The focused decoder retains prime selection, coordinate bounds, factorial separation, index congruence, polynomial congruence, and equality recovery. It exposes the existing encoded-product identity as a premise and omits the unchanged reverse CRT encoding/outer MRDP closure. The broader namespace required the explicit `Finset.mem_range.mp` qualification; the final focused file and real-module candidates include it. The minimal-import standalone helper uses the equivalent unqualified name.

Full actual `MRDPCore` compilation stopped at the missing cached object `Mathlib.NumberTheory.Dioph.olean`. The focused check compiled only the unchanged small `Mathlib.Data.Nat.Prime.Factorial` dependency. The combined canonical patch is therefore a reviewable integration candidate, not a claimed complete production build.

Inspected successful endpoints report only `propext`, `Classical.choice`, and `Quot.sound`. Final successful logs contain no `sorryAx`. Exact source hashes, command receipts, and compiler logs are under `validation/`. Recorded elapsed times are receipts, not speed benchmarks. No memory, object-size, or runtime improvement is claimed.

## Layout

- `report.tex`, `sections/`, `report.pdf`: complete report and editable source.
- `lean/pell/`: exact modified Pell modules and complete audit modules.
- `lean/canonical/`: checked helper and focused decoder, both real-module candidate sources, and the small unchanged Mathlib source used for the focused check.
- `patches/`: three unified patches against the pinned repository paths. The canonical patch edits both clients and adds the shared helper at the lower layer.
- `validation/`: final proof receipts, source/dependency manifests, compiler output, PDF build/inspection evidence, and structured results.
- `evidence/`: novelty ledgers, closing comparison, original-source provenance, and baseline source inventory. The baseline inventory records Git blobs even for binary artifacts, without redistributing the old archives.
- `screened_out/`: withdrawn work, explicitly excluded from recommendations.
- `scripts/`: replay, report build, and checksum validation helpers.
- `SHA256SUMS`: integrity manifest for all delivered files other than itself.

## Reproduction

Use a ProveIt checkout with the stated toolchain and dependency pins and build its ordinary dependencies first. Then run:

```bash
bash scripts/replay_checks.sh /absolute/path/to/ProveIt
```

The script checks the pins, invokes the four checked sources using `lake env lean`, and writes local replay logs. It does not apply patches or rebuild the whole project automatically. To validate integration, apply each relevant patch to the appropriate checkout and run the repository's normal target/check modules. The canonical actual-module pair still needs that step.

Rebuild this PDF with:

```bash
bash scripts/build_report.sh
```

This requires XeLaTeX plus P052, Nimbus Sans, and DejaVu Sans Mono fonts as configured in `report.tex`. Code is displayed with extra line wrapping where needed; line counts refer to the supplied source files, not the displayed snippets.

Verify the delivered archive after extraction, before rebuilding or editing it:

```bash
python3 scripts/verify_artifacts.py
```

No upstream files, branches, pull requests, or messages were changed by this review.
