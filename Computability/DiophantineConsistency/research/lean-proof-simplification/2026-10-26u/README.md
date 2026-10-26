# Further Lean proof simplifications for DiophantineConsistency

This bundle proposes **five new mechanisms**, with **four concrete checked main refactorings**, a checked generic design prototype, and one small trace-bound cleanup. Start with `report.pdf`; `report.tex` is the complete editable source.

## Scope and non-repetition

The source and patch baseline is ProveIt commit `4b3dd4efb10f1af27143a6142380322131968726`. The exclusion review was refreshed at `23f631ea07fff8632eb8cd92286f7621bbe051c0`. The seven patched source files and the shared-edge target are identical between these commits.

The final exclusion review covers **15 proposal packets**: six placed packets and nine incoming ZIP archives. It records **98 excluded mechanisms**, 2,216 incoming archive members and 2,048 extracted text/code/patch/metadata members. All prior proposals count as assumed applied, including deferred and uncompiled directions. The claim of novelty is relative to this inspected material, not the wider Lean literature or future changes to `main`.

A proposed small-square cleanup of `firstUnit_fundamental` was withdrawn after the freshness review found a prior general small-ordinate theorem that already replaces its target. Its patch and examples are deliberately absent from this bundle.

## Retained proposals

| Proposal | Main result | Status |
|---|---|---|
| Parameterized Pell ratio estimate | A common positive scale κ gives additive error κ/2; old estimates are κ=1 and κ=2 wrappers | Both complete changed modules checked; exact public signatures preserved |
| Sharper native-rank envelope | `(2*q-1)*(q^2-1) ≤ nativeRank`, with `q≥3`; implies rank≥40 and rank>3q | Both complete changed modules and endpoint audits checked |
| Integer induction around the seed | Interval propagation proof body 26→14 lines with the original axiom set | Complete module and existing focused client checked |
| Bounded first failure | One helper returns the first failure and its valid strict prefix | Complete module and existing focused client checked; 2 net module lines saved |
| Shared-edge Wang row | One edge function makes horizontal matching follow from index arithmetic | Generic kernel checked; actual `stepTile` equality and `Allowed` integration remain unimplemented |
| Small trace bonus | `le_abs'.mp` discharges the sign disjunction directly | Complete candidate and two endpoint audits checked; 5 lines saved |

The recommended interval proof retains `[propext, Quot.sound]`. A separate optional nine-line centered proof uses `Int.inductionOn'` and adds `Classical.choice`. Both preserve the exact statement. Only the recommended alternative belongs to the combined patch.

## Line-count interpretation

The ratio change reduces its two source files from 716 to 646 physical lines, including the common theorem and wrappers. The explicit earlier `set` cleanup reduces the counterfactual old total to 712, leaving **66 lines saved by the new factoring**.

The seven complete patched modules change from 1,937 to 1,845 lines, a raw reduction of 92. This is **not** an aggregate saving relative to every already-applied prior proposal. In particular, the rank patch's four raw saved lines include previously proposed Nat/Int conversion cleanup. Its new contribution is the stronger mathematical bound and shared nonlinear derivation.

## Contents

- `report.pdf` and `report.tex`: complete explanation, mathematical derivations, sources, evidence and limitations.
- `patches/combined.patch`: five compatible concrete patches across seven modules.
- `patches/individual/`: the five component patches for selective review.
- `patches/optional/`: the alternative centered interval proof; do not apply it together with the recommended interval patch.
- `candidate-source/`: seven complete candidate files, preserving repository-relative paths.
- `lean/`: ten checked standalone examples or endpoint audits, including the baseline and both interval alternatives.
- `evidence/`: compiler logs, measured source hashes, line counts, axiom outputs and integration receipts.
- `audit/`: exclusion ledger, source map, independent review and freshness comparison.
- `scripts/`: portable integrity checker and targeted replay driver.
- `provenance.json`: immutable source/toolchain identifiers.
- `MANIFEST.sha256`: checksums for all other delivered files.
- `UPSTREAM_LICENSE.txt`: license of the upstream code used in the candidate sources and patches.

Dependency object files and the previous proposal archives are not included. Their provenance and hashes are recorded in the corresponding receipts. Historical logs preserve actual execution paths; portable scripts do not depend on those paths.

## Validation boundary

Lean 4.32.0 compiled all seven changed modules in complete form, with focused Wang clients, isolated prototype examples and named axiom audits. The rank module pair was freshly rechecked after composing the final patches. Checks reused existing mathlib and project dependency artifacts; they are **not a clean build of the full repository**. The receipts distinguish the final successful checks from a resolved initial missing-import probe. Recorded elapsed times are diagnostic, not performance benchmarks.

The generic shared-edge record uses a separate type. Its successful kernel check does not establish membership in the actual 942-tile language or equality with the maintained step construction. The report explains the remaining obligations and the `liveCfg` device needed to preserve the existing unconditional APIs.

## Reproduce

See `REPLAY.md` for complete instructions. The default driver mode is read-only:

```bash
python3 /path/to/bundle/scripts/verify_bundle.py
python3 /path/to/bundle/scripts/replay.py --repo /path/to/pinned/ProveIt
```

Add `--apply` to apply the combined patch and run the targeted build and example checks, or `--check-existing` to check a checkout already matching the delivered candidates. The portable scripts were syntax-checked and the delivered manifest checker was run; a new full checkout replay using that driver was not performed during preparation.

Individual patches are alternatives for selective adoption, not an additional pass after the combined patch. To use the ideas after all prior refactorings, place the new facts in their already-established interfaces and recompile the affected clients; raw pinned-source line counts need not survive those adaptations.

## Rebuild the PDF

Run XeLaTeX twice from the bundle directory:

```bash
xelatex -interaction=nonstopmode -halt-on-error report.tex
xelatex -interaction=nonstopmode -halt-on-error report.tex
```

The report uses Latin Modern and DejaVu fonts, with common TeX packages. No shell escape or external graphics are required. For a pristine manifest check, direct generated TeX auxiliary files outside the extracted bundle or remove those newly generated files after recompilation.
