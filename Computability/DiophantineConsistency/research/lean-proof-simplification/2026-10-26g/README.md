# Shorter Lean proofs for Diophantine consistency

Research review prepared for Vladimir Reshetnikov, 26 October 2026.

## Start here

- **`report.pdf`** is the complete article, with a prioritized portfolio of concrete changes, mathematical reasoning, source anchors, and migration constraints.
- **`report.tex`** is the complete LaTeX source. `validation-summary.tex` supplies its final experiment-status table.
- **`patches/Representation-refactor.patch`** is a checked, reviewable patch against the pinned source. The complete revised module is in `refactored-source/DiophantineConsistency/Representation.lean`.
- **`lean/`** contains the compiled experiment modules. Each is explicitly classified in `validation/status.json`; a checked general theorem is not a claim that all its proposed project consumers have been migrated.
- **`metrics/`** contains the source inventory, exact hashes, focused circuit measurements, and duplicate-proof candidates.
- **`validation/`** contains compiler outputs, axiom audits, and reproducibility receipts.
- **`scripts/`** contains replay, source-inventory, and report-build commands.

The source review is pinned to:

```text
Repository:  https://github.com/VladimirReshetnikov/ProveIt
Commit:      60e9c5d620c6c387d932876cfa2d9376f64ea56c
Lean:        leanprover/lean4:v4.32.0
mathlib:     81a5d257c8e410db227a6665ed08f64fea08e997
Active root: Computability/DiophantineConsistency/Lean
```

The copied `lean-toolchain` and `lake-manifest.json` record the upstream environment. This archive is an add-on review package, not a separate Lake project containing the entire repository or mathlib.

## Main findings

The active Lean subtree has **546 files and 73,971 physical lines**. The two dominant generated step files contain **999 local gate lemmas and 193 power lemmas**, occupying 6,567 lines. Much of that reasoning is already supported by `ArithmeticDAG.run_node_equation` and `ArithmeticDAG.run_power`. The largest proposal is to make systematic use of indexed, kernel-checked certificates while preserving named intermediate values and DAG sharing.

The complete checked `Representation.lean` patch reduces the module from **260 to 244 physical lines**, including all shared helper costs. Its three constructor declarations shrink from 71 to 22 lines, with 28 lines of shared helper declarations. The imported prototype proves equality of the full old and new representation results by `rfl`, including their witness counts and expression trees.

Other checked experiments establish a common scanner simulation kernel, a generic circuit invariant, commutative node-correspondence soundness, half-radix arithmetic, a shorter one-hot argument, normalized carry views, cyclic-field arithmetic, and the project-specific adapters recorded in the validation inventory. The report discusses larger unintegrated changes separately.

No whole-repository rewrite or performance speedup is claimed. The existing native/internal-ZFC formalization gaps remain exactly the separate mathematical obligations described in the pinned repository documentation.

## Replay the Lean experiments

Use a clean checkout at the exact pinned commit, with the repository's Lean toolchain and dependencies installed. Run compatibility checks **before applying the patch**. The script also extracts the pinned original source with `git show`, checks its SHA256, and gives its `.olean` precedence during the old/new compatibility check.

From this extracted archive:

```bash
python3 scripts/verify.py --repo /absolute/path/to/ProveIt
```

This checks the eight core experiment modules, compiles the unchanged original representation module, verifies the constructor compatibility results, checks patch applicability without applying it, and compiles the complete patched source to a distinct output path.

To include the additional current-equation adapters delivered in `lean/`:

```bash
python3 scripts/verify.py --repo /absolute/path/to/ProveIt --full
```

The script writes a new `replay/` directory and refuses to overwrite an existing replay. Use `--output /new/path` for another run. It invokes `lake build` for the selected dependency targets. On a fresh checkout, install/fetch mathlib's cache as usual before replaying to avoid unnecessary compilation. Network access may be needed to obtain the pinned dependencies; neither toolchain nor cached binaries are bundled.

The script records commands, return codes, source hashes, output hashes, and printed axiom sets. The included `validation/architecture-validation-commands.txt` is a historical transcript with review-machine paths; use `scripts/verify.py` for portable replay. All supplied successful printed audits use subsets of:

```text
propext, Classical.choice, Quot.sound
```

Some invariant proofs use no axioms. A source scan alone is not a substitute for these elaborated-declaration audits. Imported original modules emit some existing linter warnings; a successful build does not mean those unrelated source warnings were removed.

The full representation patch can subsequently be applied on a disposable branch:

```bash
cd /absolute/path/to/ProveIt
git apply --check /absolute/path/to/archive/patches/Representation-refactor.patch
git apply /absolute/path/to/archive/patches/Representation-refactor.patch
lake build DiophantineConsistency.Representation
```

No script in this archive pushes commits, changes remote branches, or automatically applies the patch.

## Reproduce the inventory

```bash
python3 scripts/audit_lean.py \
  /absolute/path/to/ProveIt/Computability/DiophantineConsistency/Lean \
  --output /new/path/metrics
```

The script is a comment/string-aware lexical inventory, not a Lean parser, a theorem correctness audit, or a profiler. It distinguishes physical lines, nonblank lines, lexical declarations, generated-header files, and audit/check files. Duplicate bodies are candidates for manual review. The archive's `metrics/scope.json` records that the 165 historical/candidate Lean files outside the active `Lean/` subtree were excluded from these totals.

## Rebuild the PDF

Requires XeLaTeX, latexmk, standard TeX packages, Latin Modern fonts, and DejaVu Sans Mono:

```bash
bash scripts/build_report.sh
```

The report is fully self-contained in `report.tex` and `validation-summary.tex`; source links point to immutable GitHub commit URLs. The shipped PDF was rendered and visually reviewed. `SHA256SUMS` records the final delivered file bytes.

## Scope of the larger proposals

The checked generic scanner has not replaced all four repository scanners. The checked commutative node relation has not replaced both complete translation proofs. The power adapter does not claim that the 193 generated power declarations have already been removed. Sparse row certificates, block proof generation, shared quartic packaging, and object-level definability wrappers are proposed integrations.

Preserve literal `Rep`/PR data where size theorems depend on it; retain raw-input soundness; keep the full cyclic modulus and carry conditions; preserve sharper cancellation-aware degree bounds; and continue to quantify over all model naturals in the object-language layer. These conditions explain what each proposed simplification must actually prove.
