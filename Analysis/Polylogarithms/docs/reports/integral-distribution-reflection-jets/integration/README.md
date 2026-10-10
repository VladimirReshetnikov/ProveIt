# Integration plan

## Add the companion report

Copy the package to:

`Analysis/Polylogarithms/docs/reports/integral-distribution-reflection/`

Retain the existing `distribution-jets` report and its characteristic-zero conductor normal forms. This report extends the coefficient-ring and symmetry-quotient analysis; it does not replace those results.

## Manuscript insertion

A proposed new chapter-section file is:

`Analysis/Polylogarithms/docs/manuscript/chapters/08-integral-distribution-reflection.tex`

Use `manuscript-section.tex` as a compact insertion after the existing distribution-jets development. It uses ordinary LaTeX mathematical commands, the manuscript's theorem environments, and labels prefixed `ir:insert:`. It defines no global shorthand macros. Add the two bibliography entries in `bibliography-items.tex`, or map them to existing entries after checking that the cited works are the same.

The complete proofs are in the companion article: Sections 2–3 for integral freeness and the resolution, Section 4 for integer reflection torsion, Section 5 for characteristic-two support and the Smith/contact law, and Section 6 for the analytic identities and pole corrections. The article's split source is also supplied, but its preamble macros should be reconciled before importing entire section files into the book.

The chapter-10 research programme can mark the **specified depth-one presentation's** integral freeness, integer reflection torsion, all-field reflection rank locus, and one-parameter characteristic-two jet invariants as proved. Higher-depth modules, more general group actions, transition denominator ideals, and efficient certificate minimization remain open directions. Do not mark the S6 conjecture as solved.

## Apply the wording correction only after review

From a local clone:

```sh
python /path/to/package/integration/propose_clausen_correction.py /path/to/ProveIt
```

This is a dry run. The script prints a unified diff and the current source Git blob. To apply a reviewed diff at the inspected blob, add `--apply`; it keeps a backup. A changed blob requires a separate explicit `--allow-modified` override, and the anchor must still occur exactly once.

No remote write, commit, push, or edit to the original manuscript was performed in this delivery.

## Validate after insertion

Replay the exact scripts before importing the claims; compile the manuscript and check for duplicate labels or undefined references afterward. Preserve the attribution of ordinary distribution and ordinary sign cohomology to the classical literature. Keep numerical diagnostics clearly distinct from the exact polynomial replay certificates and the all-level proofs.
