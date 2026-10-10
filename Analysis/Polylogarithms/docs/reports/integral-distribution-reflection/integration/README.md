# Proposed integration

The target snapshot is `28357e8ca63dd78327db91d9be239d75e4462879`. These instructions do not modify the repository automatically.

1. Place this report package at `Analysis/Polylogarithms/docs/reports/integral-distribution-reflection/`, preserving its internal layout.
2. Copy `integral-distribution-section.tex` to `Analysis/Polylogarithms/docs/manuscript/chapters/02-integral-distribution.tex`. Insert `\input{chapters/02-integral-distribution}` after the manuscript's distribution-module material, where the weighted presentation has been introduced. The insertion restates its definitions and can instead be placed at the end of Chapter 2. It uses only the manuscript's existing theorem environments and standard mathematical packages; all labels have the `intdist:` prefix.
3. Add the contents of `bibliography-entry.tex` inside the existing `thebibliography` environment in `references.tex`. The short insertion cites this report for the full resolution and reflection proofs; the standalone report itself supplies the primary-source bibliography.
4. Review the three focused changes in `CORRECTIONS.md` and update the research-status paragraph. These are targeted editorial proposals, not a blind patch against an evolving `main` branch.
5. Run the core verification commands in the report README, then compile the consolidated manuscript using its existing build process. The delivered standalone article was compiled and reviewed; the complete consolidated book was not rebuilt here.

The manuscript insertion gives the principal results and a proof outline. The full proofs remain in the accompanying article. No existing report is silently replaced, and historical numerical conjectures are not retroactively described as proved before their actual proofs.

## Suggested status ledger entry

**Integral distribution/reflection continuation (9 October 2026).** Proves a raw-row determinant-one minor and fixed original-symbol basis over the integral polynomial weight ring; all-ring base change follows. Gives an explicit weighted Anderson resolution and reduces integral reflection torsion to binary Koszul homology. Determines all scalar reflection Smith factors and the torsion of arbitrary one-variable integral jets. Adds exact all-order level-12 and level-30 polylogarithm identities and pole-cancelled derivative formulas at order one. Independent polynomial replay, raw integer Smith computations, and finite-field resolution checks accompany the proofs. No numerical period independence, proof-assistant formalization, or proof of the Gaussian `S_6` relation is asserted.
