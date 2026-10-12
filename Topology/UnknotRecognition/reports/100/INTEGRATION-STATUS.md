# Weighted forest integration (12 October 2026)

The maintained source-relative top reduction predates this report's intake.
This integration adopts the additive retained-incidence objective described
in this report and report 99. It extends the existing degree/xor queue with
a maximum heap, using exact raw passages outside the existing lower forest.
The independent source checker and whole-cut certificate format are unchanged.

`normal_cut_handlebodies(..., top_forest='max_weight')` selects the optimum
additive deletion tree; `top_forest='queue'` retains the earlier selector.
The low-level reducer retains its queue default for historical reproduction.
The two recorded loop-source misses now produce independently replayed
whole-cut certificates, with both boundary backends. Paired common-success
timings show no broad elapsed-time gain. The mathematical optimum is not
a completeness theorem for subsequent raw cancellation or knot recognition.

See `../../synthesis/weighted_top_forest.tex` and the corresponding
`../../synthesis/data/weighted-forest-*` source-pinned evidence. This change
does not integrate the separate homology-image algebra, a geometric chain
compiler, paired primal/dual optimization, or a global hierarchy theorem.
The delivered report files remain unchanged.
