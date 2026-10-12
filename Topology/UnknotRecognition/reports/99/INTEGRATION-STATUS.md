# Native integration and restricted-solver review (12 October 2026)

The native source-relative top reduction was already implemented before this
report arrived. The current integration adopts the fixed additive
retained-incidence objective also described by report 100, using the existing
source endpoint compiler and unchanged independent checker. Its heap-based
root growth finds a maximum-weight dual spanning tree without tree search.

The separate two-row-column polynomial solver was reviewed and probed from
an isolated copy. Its 18 tests pass. On 120 original source core matrices,
83 positive and two negative answers replay independently; 35 cases fall
outside the column hypothesis. It adds no bare-core completions over the
weighted selector on this bank. These are finite matrix conclusions, before
bundle-interface rows, not whole-cut or knottedness verdicts. This solver and
the general obstruction-guided tree search are not production defaults.

The maintained article and fresh evidence are in
`../../synthesis/weighted_top_forest.tex` and
`../../synthesis/data/weighted-forest-*`. Original delivered files remain
unchanged; the integration does not establish general quasi-polynomial
recognition or arbitrary boundary-pattern transport.
