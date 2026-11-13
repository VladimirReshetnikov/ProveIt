# Positive74 finite-field local search

`search.py` reads the SHA-256-pinned Lean-checked 74-gate list and uses three deterministic evaluations modulo 1,000,000,007 to prefilter local substitutions of each gate by one or two new binary arithmetic operations on previously available values. The permitted terminals include the 14 variables, four symbolic ports and integer constants −4 through 8. It recalculates live gates at the output after each replacement and records only strict reductions. The search includes first-gate squares and both subtraction orientations. The separately recorded positive control inserts two redundant gates and is detected.

`search_signs.py` repeats the same search for all 31 nonempty combinations of reversing the five residual subtractions whose values are squared. Reversal negates a residual and leaves its square unchanged; this is a zero- and value-preserving transformation over integers. The graph and terminal scope remain the same. All results were generated with `python3 -I -S -B`.

The recorded search found no strictly smaller candidate in this limited local family, in the original orientation or the 31 sign orientations. The baseline evaluated 746,845 first-gate recipes and 19,906 second-gate queries; the control found four one-gate and 17 two-gate reductions. This is only a finite-field prefilter: any reported candidate would need exact symbolic proof. It does not establish global optimality, exclude other algebraic/zero-equivalent transformations, or bind external JSON/PDF bytes in Lean. The separate paired-three-gate exploratory search is not part of this reproducible packet.

Independent source/graph/control/result review and rerun passed: `reviews/nine-sharing-sign14-positive74-local-search-independent/`.
