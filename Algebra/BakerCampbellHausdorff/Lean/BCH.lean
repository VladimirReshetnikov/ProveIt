/-
# Baker–Campbell–Hausdorff: formalization root

This library accompanies the article in `docs/combined`. It formalizes,
in Lean 4 with Mathlib, results of the article with statements matching
the article's own, in the article's setting of real or complex unital
Banach algebras:

* `BCH.Commuting` — Proposition 9.1 (commuting case);
* `BCH.Central`   — Theorem 9.2 (central commutator), identities (9.2)–(9.4);
* `BCH.Campbell`  — Theorem 5.1 (Campbell's identity) and the braiding
  identities (5.3), (5.4).
-/
import BCH.Commuting
import BCH.Central
import BCH.Campbell
