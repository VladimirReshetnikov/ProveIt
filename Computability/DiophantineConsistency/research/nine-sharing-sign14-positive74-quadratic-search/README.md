# Positive74 positive-definite quadratic-pair search

For each of the ten pairs of checked residuals `r,s`, replace their two squares with a binary quadratic form `Q = a r² + b r s + c s²`, leaving the other three squares. The tested 61 coefficient triples have `a,c` in 1..3, `b` in −4..4, and `4ac − b² > 0`. The exact integer-polynomial certificate in `exact-certificate.py` verifies

`4a Q = (2a r + b s)² + (4ac − b²) s²`.

Since `a` and `4ac−b²` are positive, `Q` is nonnegative on the integers and is zero precisely when `r=s=0`. Thus the changed single equation is zero-equivalent over the same 14 positive inputs and four integer ports. Its polynomial need not be identical.

`search.py` uses three deterministic samples modulo the checked prime 1,000,000,007 as a prefilter. For each of 610 pair/form combinations it searches for `Q` as an existing source-graph wire, one new arithmetic gate, or two new gates on available wires, including a doubled or squared first gate. Literals −4..8 are available as terminals. It reconstructs all 15 commutative addition-tree shapes for `Q` and the three other residual squares, merges commutative duplicate nodes, and counts the resulting live gates. A 76-gate control with an inserted `(r+1)−1` checks that the target-pair signature has an existing wire and that reusing that wire yields the original 74-gate circuit; the full search is not rerun on the modified graph. The search matched 1,516 modular recipes, checked 22,740 output trees, and found no circuit below 74.

This is a finite, sampled prefilter, not an exact-equivalence certificate for a hypothetical match or a global-minimality proof. Every match would need exact symbolic verification; no candidate arose. The independently Lean-checked 74-gate circuit and separate external JSON/PDF boundary are unchanged. Run both scripts from the repository root with `python3 -I -S -B`.

Independent review and rerun passed: `reviews/nine-sharing-sign14-positive74-quadratic-search-independent/`. The review independently checked the quadratic certificate, candidate-family boundaries, output-tree coverage and stated control scope. No exhaustive or minimality claim is made.
