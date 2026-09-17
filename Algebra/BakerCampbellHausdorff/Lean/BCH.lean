/-
# Baker–Campbell–Hausdorff: formalization root

This library accompanies the article in `docs/combined`. It formalizes,
in Lean 4 with Mathlib, results of the article with statements matching
the article's own, in the article's setting of real or complex unital
Banach algebras:

* `BCH.Commuting` — Proposition 9.1 (commuting case);
* `BCH.Central`   — Theorem 9.2 (central commutator), identities (9.2)–(9.4);
* `BCH.Campbell`  — Theorem 5.1 (Campbell's identity) and the braiding
  identities (5.3), (5.4);
* `BCH.Eigen`     — Theorem 9.4 (the relation `[X, Y] = sY`), identities
  (9.5)–(9.7);
* `BCH.Log`       — Proposition 7.1 (the Mercator logarithm `log(1 + U)` for
  `‖U‖ < 1`, `exp(log(1 + U)) = 1 + U`) and Corollary 7.2 (the BCH logarithm
  `Z = log(e^X e^Y)` with `e^Z = e^X e^Y` for `‖X‖ + ‖Y‖ < log 2`);
* `BCH.Series`    — the homogeneous BCH series `Zₙ(X, Y)` and Theorem 7.3 (i), (ii):
  for `‖X‖ + ‖Y‖ < log 2` the series `∑ₙ Zₙ(X, Y)` converges absolutely with
  the majorant `-log(2 - e^{ρ s})`, its sum `Z` satisfies `e^Z = e^X e^Y`, and
  the tail after degree `N` is at most `ρ^{-(N+1)} (-log(2 - e^{ρ s}))`.
-/
import BCH.Commuting
import BCH.Central
import BCH.Campbell
import BCH.Eigen
import BCH.Log
import BCH.Series
