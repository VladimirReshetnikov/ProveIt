# Lean proof simplification study

This package audits the active Lean development in ProveIt's
`Computability/DiophantineConsistency` topic and supplies a report, compiled
proof-refactoring examples, two complete patched modules, reviewable diffs,
and reproducible source/validation records.

## Read first

- `report.pdf`: the complete technical report with mathematical and code examples.
- `report.tex`: the LaTeX source used to produce that PDF.
- `validation/final-validation.json`: final compilation results, source hashes,
  Lean/Mathlib identities, and individual elapsed observations.
- `inventory/summary.json`: aggregate lexical measurements of the active Lean tree.

The report distinguishes complete checked patches, checked generic helpers
whose integration is still proposed, and unimplemented architectural ideas.
It does not claim a full downstream build or a new consistency equivalence.

## Exact source snapshot

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Commit: `60e9c5d620c6c387d932876cfa2d9376f64ea56c`
- Lean: `leanprover/lean4:v4.32.0`
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`
- Report date: 26 October 2026.

The original checkout was not modified. All replacements were compiled as
isolated full-module copies or additive prototypes. The largest source
reduction concerns the existing package-52 coefficient-parent module; it
does not identify that calibration with the distinct current length-2011 data.

## Contents

| Location | Contents |
|---|---|
| `patches/` | Two independent patches against the pinned checkout |
| `patched/` | Complete proposed `Representation.lean` and `NativeCoefficientBounds.lean` |
| `Lean/ProofSimplification/` | Six checked prototype/helper modules |
| `inventory/` | Per-file hashes, physical/code-line counts, declaration estimates |
| `validation/` | Compilation logs, axiom reports, metrics, and interface review |
| `scripts/` | Verification, inventory reproduction, coefficient metrics, PDF build |
| `provenance.json` | Snapshot, scope, and build metadata |
| `SHA256SUMS` | Checksums of package files other than this checksum file |
| `UPSTREAM-LICENSE` | License of the upstream code from which patches derive |

### Checked helpers

- `ArithmeticRefactors.lean`: block residue identities and scaled div/mod lemmas.
- `RotationRefactors.lean`: exact-signature alternatives for two original
  half-radix rotation results; neither invokes the target theorem it replaces.
- `ScannerCore.lean`: shared `Nat.rec` laws, fixed states and invariant preservation.
- `FinitePushforward.lean`: weighted finite-fiber summation with collisions retained.
- `RepresentationNaturality.lean`: shared assignment lemma, alternative constructors,
  and `rfl` equality proofs against the originals.
- `ListLookup.lean`: the pinned library API replacing a private lookup induction.

The helper modules carry their own `#print axioms` commands. No `sorry`, new
axiom, or native-evaluation shortcut was introduced. The scanner lemmas have
empty axiom sets; other reported sets are subsets of `propext`,
`Classical.choice`, and `Quot.sound`.

## Reproduce the verification

Use an existing checkout of the exact commit, with the pinned Lean toolchain
and dependencies installed. The script does not install packages or build the
entire repository. Its baseline module prerequisites are:

```bash
lake build DiophantineConsistency.Representation \
  DiophantineConsistency.NativeQuadraticParent \
  DiophantineConsistency.NativeCyclicRotation
```

Then run, replacing the two absolute example paths with your actual locations:

```bash
python3 /path/to/lean-proof-simplification-2026-10-26/scripts/verify.py \
  /path/to/ProveIt
```

The script checks the repository commit, Lean version, and Mathlib commit;
it assumes a clean checkout and unchanged built dependencies. It runs
`git apply --check` on both diffs, compiles all six helpers,
and compiles complete patched modules with axiom diagnostics appended. It
records return codes, source/log hashes, elapsed observations and axiom sets.
An unexpected axiom or failed command makes the replay fail. It leaves all
repository source files unchanged.

For an already configured separate Lake workspace whose project imports point
at the same clean source snapshot and built dependencies, use
`--lake-workspace /path/to/workspace`. Use
`--lake /absolute/path/to/lake` when Lake is not on PATH. The optional
`--output /path/to/evidence` chooses where the new replay logs and temporary
Lean objects go. By default they are written to `validation/replay/`.

The default module-level compile budget is unchanged except for the explicitly
scoped option in the coefficient patch. Read the report for the distinction
between source reduction and elaboration performance. Logged times were
observed under concurrent load and are not speedup measurements.

## Review or integrate the patches

Each patch is independent and retains the original public names. Review the
complete file in `patched/` alongside the corresponding diff. Apply it on a
branch of the pinned checkout only after review, then replay the direct consumers
appropriate to your integration target. The archive's checks do not claim to
have rebuilt every downstream consumer.

The representation patch preserves exact stored expression syntax and witness
counts; the additive prototype supplies equality proofs by reflexivity. The
coefficient patch preserves the original coefficient function, envelope and
all exported theorem signatures. Removing repeated private proof trees does
not change the underlying arithmetic construction.

## Reproduce the source metrics

```bash
python3 scripts/audit_inventory.py /path/to/ProveIt --output /tmp/proof-inventory
python3 scripts/audit_coefficient_refactor.py \
  --repository /path/to/ProveIt \
  --candidate patched/NativeCoefficientBounds.lean
```

The inventory is lexical, not a Lean elaboration or a transitive axiom audit.
Its comment stripper handles nested Lean block comments. Declaration lengths
are approximate lexical spans. The coefficient script separately compares
public declaration headers and counts repeated proof text and coefficient
expressions; this does not substitute for compilation.

## Rebuild the PDF

With a standard LaTeX installation containing `pdflatex`, Latin Modern,
`microtype`, `listings`, `hyperref`, `xurl`, and the listed ordinary packages:

```bash
bash scripts/build_report.sh
```

The PDF was compiled from the supplied TeX and visually reviewed after rendering.
Compiled Lean objects, downloaded dependencies, and the local compiler are not
included in this small archive.
