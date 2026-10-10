# Integration notes

These files are proposed edits for maintainer review. They have not been applied to the remote repository or compiled as part of the full consolidated manuscript. The companion article itself was compiled and visually inspected.

A suggested new companion location is:

    Analysis/Polylogarithms/docs/distribution-jets/

The exact location is an editorial choice; preserve the internal relative layout when copying the package.

## Suggested edit sequence

1. Replace the observation `tower:thm:rank` and its following experimental-status paragraph in Chapter 8 with `ch08_distribution_rank.tex`. The original label is preserved. The new theorem explicitly defines its matrix instead of claiming to reconstruct absent scripts.
2. Replace the cubic-moment negative-result block in Chapter 7 with `ch07_cubic_correction.tex`; add `bibliography_addition.tex` inside the bibliography. The historical label `integral:neg:cubic` is preserved for link compatibility despite its old name.
3. Replace the mixed-point “all depth-two content” paragraph in Chapter 4 with `ch04_mixed_involution.tex`. Check the surrounding “every diagonal” wording for the same needed qualification.
4. Optionally append `ch04_S4_status.tex` after `gauss:eq:S4-closed`. Do not change the conjectured evaluation to a theorem on the basis of this contribution.

Update Chapter 10's surviving-research discussion: the canonical uniform distribution-rank problem now has a proof; integral/modular variants, higher-depth extensions, and numerical independence remain separate questions. The primitive-grid determinant and resonance discussion should be linked rather than mistaken for a full-quotient rank jump.

The snippets use ordinary LaTeX mathematics plus the manuscript's `theorem`, `result`, `remark`, and `Li` conventions. They are intended to be reviewed against the current preamble. New bibliography key: `distjets:BBB2015`.

## Preservation and review

Retain the code, certificate JSON, and data distinctions. The source baseline is recorded in `provenance.json`. Keep the claim-boundary table from the companion paper when summarizing the results. A successful integration should compile both the standalone companion and the consolidated manuscript, run the exact scripts, and independently review the analytic arguments.
