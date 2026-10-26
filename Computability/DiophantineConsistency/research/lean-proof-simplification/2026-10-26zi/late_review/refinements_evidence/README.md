# Four further Lean proof refinements

Prepared for Vladimir Reshetnikov, 26 October 2026.

## Read first

`report/lean-proof-refinements.pdf` is the complete research report.
`report/lean-proof-refinements.tex` and its two included `.tex` inputs reproduce it with pdfLaTeX.

The four proposals are:

1. Prove `AnnotatedClosure.formCode_ge` from outer-constructor minima, removing structural induction and nonlinear square-bound infrastructure.
2. Derive strict multiplication from canonical additive differences and no zero divisors, then use cancellation for the Boolean-root theorem before successor discreteness.
3. Replace the helix and seam bilateral integer inductions by period-one rigidity.
4. Prove the exact canonical band quotient's matching/binding properties before packaging it existentially, and reuse that proof in the marker module.

All four were screened against prior proposals, including optional, deferred, uncompiled, and notes-only directions. The initial review covered rounds a-r and three incoming ZIPs. The closing refresh covered rounds s-v; s-u are the three moved archives, and the additional round v does not repeat the four mechanisms. General module reordering and canonical-witness sharing already have precedents; the report confines its novelty claims to the exact new source reductions.

## Pins and source freshness

- Validated source/dependency snapshot: `1e2a853935a6155cbcf2aa199aaca51946c4fff9`.
- Closing novelty/target-source refresh: `f42d3f94f78eb63639316a33e25f2f69d12c651e`.
- All seven target source files are byte-identical at those two commits.
- Lean: 4.32.0.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`; all nine package pins were checked.

The seven files shrink from **795 to 744 physical lines**: **51 lines removed**, including imports, helper statements, comments, and blank lines. This is a local measurement against the pinned source, not a total saving against an unseen mechanically merged implementation of all prior reports. No general compilation-speed claim is made.

## Apply or review

`patches/` contains one patch per proposal and `all-refinements.patch`.
Paths are relative to the ProveIt repository root.
`overlay/` contains the complete seven replacement modules for inspection.

From a checkout whose seven target files match the pin:

```bash
git apply --check /absolute/path/to/packet/patches/all-refinements.patch
```

To integrate the reviewed changes, use `git apply` without `--check` after reviewing the patch. The two-file order patch must be applied together. External clients relying on the old transitive import from `ObjectNaturalOrderedSemiring` to `ObjectNaturalDiscrete` may need an explicit Discrete import. All maintained direct consumers were inspected, and the downstream pairing chain was compiled successfully.

For a newer checkout with different target bytes, rebase the patches. Do not overwrite accumulated changes with the full overlays.

## Replay without modifying the checkout

The replay script reads the checkout and the packet overlays and builds into an isolated output directory outside the checkout. It does not invoke Lake or apply the patch to the checkout, create commits, push, or run network setup. Install the checkout's pinned toolchain, packages, and mathlib cache beforehand using the repository's normal Lean setup.

Requirements: Python 3.11+, git, an installed Lean 4.32.0 compiler, and the pinned Lake packages. The script verifies the exact `lean-toolchain`, `lake-manifest.json`, and `lakefile.toml` hashes.

First check source hashes, overlay hashes, environment pins, and patch applicability:

```bash
python3 scripts/replay.py --repo /absolute/path/to/ProveIt --verify-only
```

Then compile the complete selected import closure and compare the eight expected axiom sets:

```bash
python3 scripts/replay.py --repo /absolute/path/to/ProveIt \
  --work-dir /absolute/path/to/an-empty-replay-directory
```

Omit `--work-dir` to create a temporary directory automatically. Both explicit and automatic output locations must be outside the source checkout. They may need substantial space for Lean objects. Supply `--lean /absolute/path/to/lean` to choose an installed compiler explicitly; otherwise the script resolves the checkout's installed compiler using `elan which lean`, falling back to `lean` on `PATH`. It resolves the installation prefix and uses that actual executable for every compilation, so changing source roots cannot select another toolchain. The script emits `replay-results.json` and per-module logs. It verifies all nine package commits and excludes old repository object directories from its import path.

The packet's portable replay script passed syntax and `--verify-only` checks. The recorded full validations were performed by the isolated build drivers represented in the supplied receipts; the portable replay entry point was not redundantly run for a second full build.

## Verification performed

- Structural/coding closure: 73 successful module records, including all three replacement modules and unchanged downstream pairing consumers. Forty-seven checked prerequisites came from this task's fresh builds; 26 additional compilations passed.
- Wang closure: 34 fresh baseline modules including four existing focused check modules. The candidate run recompiled nine affected modules; all four replacement modules and all four focused checks passed.
- Seven existing endpoint axiom outputs are identical before and after.
- The new exact-witness helper uses only `propext`, `Classical.choice`, and `Quot.sound`.
- No audited endpoint reports `sorryAx`.
- Standalone proof kernels also compiled.
- The combined patch passes `git apply --check` against the pinned sources.
- Independent source review found no changed public theorem statement, weakened conclusion, or altered computational definition in the seven overlays.

This is not a full-repository build. Compiler timing records are diagnostic, not benchmark evidence.

## Contents

- `report/`: PDF, LaTeX manuscript, metrics and validation inputs.
- `patches/`: four focused patches plus combined patch.
- `overlay/`: seven full replacement sources.
- `lean/`: standalone kernels and axiom-audit probes.
- `audit/`: exclusion ledger, independent review, 488-file prior-corpus manifest, incoming ZIP provenance, closing refresh evidence.
- `evidence/`: original target sources, source/overlay hashes, package pins, successful compiler receipts and axiom comparisons.
- `scripts/`: portable replay and packet-hash verification.
- `MANIFEST.sha256`: integrity hashes for every other packaged file.

Historical validation receipts retain the paths at which the experiments ran. They are evidence; use `scripts/replay.py` for portable paths.

## Rebuild the PDF

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error lean-proof-refinements.tex
pdflatex -interaction=nonstopmode -halt-on-error lean-proof-refinements.tex
```

## Verify the archive contents

```bash
python3 scripts/verify_packet.py
```
