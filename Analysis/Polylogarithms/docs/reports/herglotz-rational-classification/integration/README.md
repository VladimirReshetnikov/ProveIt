# Proposed manuscript integration

Suggested report destination:

`Analysis/Polylogarithms/docs/reports/herglotz-rational-classification/`

Copy the report package there, keeping `article.tex`, `sections/`, `references.tex`, the PDF, scripts, data, and ledgers together. The standalone source is optional for repository use.

The file `manuscript-fragment.tex` is an additive excerpt intended for `chapters/09-herglotz.tex`, after the existing section on the complete `J(2/q)` classification. Its labels use the prefix `hjr:`. It assumes the manuscript's existing theorem environments, `\Q`, and `\Li`; its displayed formulas need no new macro definitions. Add the item from `bibliography-entry.tex` to the manuscript's bibliography.

The fragment deliberately cites the full report for the complete proofs. It can be used as an insertion draft, not as an automatic patch. The `S(m)` notation agrees with the existing Herglotz chapter, but should be checked at the chosen insertion point.

In `chapters/10-discovery.tex`, update the sentence describing the general `J(p/q)` symbol problem as open: the formal classification is now Theorem 4.2 of this report. Retain the separate numerical period-injectivity question and the constructive full-certificate question.

Add an audit remark beside the direct boundary calculation: the finite-field three-term statement in the reviewed Radchenko–Zagier preprint fails at `p=7,n=2`; the direct boundary formula remains valid. No existing analytic Herglotz formula needs to be deleted because of that defect.

Do not update unrelated Gaussian or `S_p` conjecture statuses. Do not replace a qualified formal non-reduction statement by an unconditional assertion about numerical periods. No repository write, push, or commit was performed in preparing this package.
