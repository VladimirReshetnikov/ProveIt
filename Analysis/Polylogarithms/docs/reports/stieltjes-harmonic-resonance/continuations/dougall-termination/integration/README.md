# Suggested integration

This package is additive. No remote writes were made.

Suggested report destination:

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/dougall-termination/`

The compact `manuscript_addition.tex` is independent of the standalone article's macros. It requires amsmath, amssymb, amsthm and an existing `theorem` environment. Its labels use the `dterm:` prefix. A three-page pdfLaTeX preview is supplied. It does not reset theorem numbering, style, or macros.

The classification can be linked from `chapters/07-mixed-dougall-identities.tex` and the preserved centered-Dougall continuation. The harmonic and polylogarithmic formulas can be cross-referenced from the depth and integration chapters. Do not replace the canonical mixed-Dougall text wholesale: it contains different mixed-parameter identities.

The main report distinguishes the pre-existing all-resonance subtraction from the new classification. Preserve that distinction when merging. Also retain the normal-convergence arguments, the reciprocal-Gamma convention, the exact-formal-termination lemma, and the statement that a zero summed remainder does not imply termination.

For bibliography insertion, cite the full report under a locally unique key, together with DLMF §16.4, Eq.16.4.9, and the earlier centered-Dougall continuation. The exact path and repository pin are in `notes/SOURCE_AUDIT.md`.

Before promoting novelty claims, compare with the currently incoming reports and complete a broader literature review. The five ZIP archives visible during this work were inventoried, not unpacked. Nothing here settles S6, numerical period independence, or reductions of every individual colored multiple zeta value.
