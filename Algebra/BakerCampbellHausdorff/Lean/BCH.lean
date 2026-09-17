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
  the tail after degree `N` is at most `ρ^{-(N+1)} (-log(2 - e^{ρ s}))`;
* `BCH.LowDegree` — the components `Z₁, …, Z₄` in closed form (Proposition 4.3,
  equations (4.9)–(4.12), (4.15)–(4.17));
* `BCH.Remainder` — `‖e^C‖ ≤ ‖1‖ e^{‖C‖}`, the Lipschitz estimate
  `‖e^B - e^A‖ ≤ ‖1‖² e^{max(‖A‖,‖B‖)} ‖B - A‖`, and the exponential remainder
  estimate (7.5) of Theorem 7.3 (ii);
* `BCH.Trotter`   — Lemma 11.1 (tail bounds `c₀ σ²`, `c₀' σ³`) and Theorem 11.2: the
  Lie–Trotter formula `(e^{tX/n} e^{tY/n})^n → e^{t(X+Y)}` with its complete
  logarithmic error `∑_{k ≥ 2} t^k n^{1-k} Zₖ(X, Y)` and the explicit `O(1/n)`
  bound.
-/
import BCH.Commuting
import BCH.Central
import BCH.Campbell
import BCH.Eigen
import BCH.Log
import BCH.Series
import BCH.LowDegree
import BCH.Remainder
import BCH.Trotter
