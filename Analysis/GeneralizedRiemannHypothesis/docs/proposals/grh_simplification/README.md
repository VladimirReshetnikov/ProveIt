# Two simplifications of the readable Lean RH / Dirichlet-GRH proof

Start with [grh_simplification.pdf](grh_simplification.pdf).
The complete editable report is [grh_simplification.tex](grh_simplification.tex)
and its five included section files.

## Recommendations

1. **Replace exact exchange-scalar modulus metadata with direct height certificates.**
   Port the compact edition's square-cost and determinant-first architecture
   to the readable proof. Add exact positive-power homogeneity for the actual
   common-multiplier height, so the current unsquared determinant bound is
   recovered without any factor-two loss. Carry arbitrary additive budgets,
   retaining exact complex scalars, nonvanishing arguments, the mixed ambient
   Gram identity, and the conductor Euler-factor cancellation.

2. **Replace the branching extended-tensor proof with a calibrated Gram adjoint.**
   Use the existing Schur commutant theorem to make the product of the branching
   map and its Gram adjoint scalar. Bound that scalar at the norm-one highest
   vector. The compact edition already uses this method with a Cartan
   multiplication bound; the readable edition already contains that bound.
   A direct port is the shortest practical route. The report also proves an
   alternative using one signed tensor coordinate, giving a stronger standalone
   norm criterion without the weight-compatibility hypothesis.

Both recommendations concern concrete internal arguments. They do not replace
the theta-lift proof by a new elementary proof, and no overall percentage or
measured net line reduction is claimed.

## Attribution and the exclusion constraint

The analysis covers all 18 proposal bundles in the requested directory at the
pinned revision. Their mechanisms and relevant future directions are listed in
the report and [the exclusion matrix](notes/proposal_exclusion_matrix.md).
Neither recommendation repeats a proposal in that corpus.

The broader methods have **compact-source precedents**:

- normalized squared scalar costs;
- existential mixed-Gram endomorphisms and factored determinants;
- the Gram-adjoint, Schur, and highest-vector branching argument.

They are explicitly credited to the pinned compact source. The additional work
here is the checked exact-power height bridge, guarded arbitrary-cost calculus,
exact crossing sums, source-specific migration and normalization checks, and
the direct unit-tensor calibration. This is not a claim of global mathematical
priority for any of the broader methods.

## What was checked

The following files were compiled successfully with Lean 4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679:

| File | Checked content |
|---|---|
| [HeightPower.lean](lean/HeightPower.lean) | The faithful generalized height definition; forward powers; exact positive-power descent; equivalent square and scaled forms; two applications. |
| [MatrixChainBudget.lean](lean/MatrixChainBudget.lean) | Determinant recurrence, exact triangular and arbitrary crossing sums, normalized squared-ratio multiplication, guarded product and chain costs. |

The printed axiom sets of the principal lemmas contain only
propext, Classical.choice, and Quot.sound.
See [the packaged-file check](evidence/package_lean_verification.log)
and the individual logs in evidence/.

These files have explicit assumptions. MatrixChainBudget takes the
matrix recurrence as an input; it does not prove the theta-lift adapter.
HeightPower abstracts only the local normed fields and maps of the source's
height definition, keeping its common multiplier and all quantifiers.

[HeightPowerIntegration.lean](integration/HeightPowerIntegration.lean) is a
specialization candidate using the exact New.HeightLe names. It has not
been compiled against the full source closure. The complete scalar-cost
migration and the branching replacement have mathematical proofs and
specific integration instructions, but are not finished source patches.

The original RH/GRH project was not rebuilt or independently replayed during
this work. Repository reports of such checks are cited as repository reports.
The public statement under review is RH for zeta and GRH for Dirichlet
L-functions.

## Source pins

- Readable repository: https://github.com/VladimirReshetnikov/ProveIt
- Commit: 9050b04000647d588d0c78d945180abcd3b0bcf7
- Reviewed subtree: Analysis/GeneralizedRiemannHypothesis/Lean/grh
- Subtree Git object: e8c80c2a260890eaf2c9410ce3a8b24951e80506
- Compact repository: https://github.com/lsernau/grh-lean
- Compact commit: 72fead102f663d5c7a407964a13dc0cf9d977207
- Lean: leanprover/lean4:v4.35.0
- Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679

The report uses immutable source links. File hashes and compact Git blob
identifiers are in [provenance.json](evidence/provenance.json).

## Reproduce the Lean checks

With an existing, built Mathlib checkout at the exact pin and Lean 4.35.0 on
the executable path:

    bash scripts/verify_lean.sh /absolute/path/to/mathlib

The script verifies the Mathlib revision, checks the Lean version, and
compiles both delivered files through that checkout's Lake environment.
The verification logs include the actual commands and paths used here.

Alternatively, with Elan/Lake installed and network access:

    bash scripts/verify_lean.sh

This initializes the pinned package dependency and requests Mathlib's cache,
then performs the same two checks. The included lakefile.toml and
lean-toolchain also permit a normal Lake build. The integration candidate
is deliberately outside the standalone build roots.

To check the source specialization, use a fully built checkout of the
readable proof and invoke its Lake environment on the absolute path to
integration/HeightPowerIntegration.lean. That is a remaining integration
gate, not a check already completed by this archive.

## Rebuild the PDF

Run with pdfLaTeX and the standard packages listed in the preamble:

    bash scripts/build_report.sh

Two passes resolve the contents and cross-references. No external images,
bibliography database, network calls, or proprietary fonts are needed.

## Reproduce the source measurements

From the archive directory, with a checkout at the readable commit:

    python3 scripts/source_audit.py /absolute/path/to/ProveIt --output /tmp/grh-audit
    python3 scripts/metadata_audit.py /absolute/path/to/ProveIt --output /tmp/grh-audit

The first script records file hashes, physical line counts, the syntactic
import graph, and external textual references to the branching helpers.
The second reproduces the conservative exact-modulus declaration count.
These are source audits, not proof-term or theorem-validity checks.

Measured figures in this snapshot:

- 803 Lean files and 477,020 physical source lines.
- All 803 files occur in the syntactic import closure of Main.
- 4,934 lines in the eight affected determinant/auxiliary modules.
- 27 selected legacy representation declarations: 136 physical body lines,
  or 198 including their immediately attached documentation.
- 291 gross lines in the targeted branching helpers, theorem body, and
  leading-minor definition; new proofs must replace part of that material.

None of these counts is a measured net saving. Overlapping source regions
must not be added together.

## Supporting material

- [Detailed height migration](notes/height_migration.md)
- [Detailed branching migration and compact attribution](notes/branching_migration.md)
- [Existing-proposal exclusion matrix](notes/proposal_exclusion_matrix.md)
- [Conservative source accounting](notes/source_accounting.md)
- [Rejected Fitting/Newton shortcuts and their obstructions](notes/rejected_shortcuts.md)
- evidence/proposal_manifest.tsv: hashes for 59 relevant proposal text files.
- evidence/source_manifest.tsv: hashes for all 803 readable Lean source files.
- SHA256SUMS: checksums for the delivered files, excluding the checksum file itself.

The complete ProveIt and Mathlib repositories are not bundled.

## Upstream notices

The height definition is reproduced/adapted from the readable proof, whose
upstream notice identifies Copyright 2026 Anthropic, PBC, under Apache 2.0.
The repository credits the proof to Levent Alpöge, with Claude.
The code here depends on Lean and Mathlib. The upstream license and notice
are included as LICENSE.upstream.txt and NOTICE.upstream.txt.
The new analysis, generic lemmas, and scripts are supplied as editable
research artifacts; the upstream attribution and license notices are
preserved for adapted source material.
