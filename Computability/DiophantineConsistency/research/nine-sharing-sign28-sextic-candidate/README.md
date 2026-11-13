# 28-witness sextic candidate via three more positive cuts

This is an external candidate derived from the independently reviewed
[31-witness sextic AST](../nine-sharing-sign31-sextic-candidate/). It
successively removes `X`, `c2`, and `normalized_S2`, replacing each with
its defining product or square. The eliminated coordinates, at their
respective stages, are 16, 22 and 28; `seed.json` records each replacement
and the resulting shifted indices. The output is the sum of squares of 19
residuals in 28 natural witness coordinates, with unused input coordinate 0.

The maximum syntactic degree of the resulting residuals is 3, so the sum of
squares has degree at most 6. Its unchanged `q3` row has coefficient
`−beta³` on `x₁³` when all other variables are zero. The `x₁⁶` coefficient
of the full sum of squares is therefore a sum of integer squares at least
`beta⁶ > 0` for the fixed positive beta. This external argument gives exact
degree 6, not a Lean degree theorem. At the all-zero assignment, the same
row is `−(beta+1)³`, so the seed is nonzero there.

Each removed right-hand side is a natural product or square. A prospective
31-coordinate lift inserts them in reverse order. Conversely, the three
defining residuals of a zero force those natural coordinates to agree with
the corresponding products, subject to the ordered-ring and injective
embedding lemmas used in the earlier bridge. This is a mathematical
reconstruction argument, not a Lean proof. Neither equivalence for this
candidate nor an iPRA endpoint has been proved. The existing nine-variable
Jones theorem requires a quartic seed and does not apply directly to it.
Coefficient bytes and their relation to model ports are inherited from the
32-witness candidate.

`python3 -I -S -B build.py --check` reproduces the transformed AST, while
`python3 -I -S -B check.py` checks syntactic degrees and 16 finite reverse
reconstruction controls. Both commands exited 0; the controls are not an
all-model proof. SHA-256:

* builder `376b84ca8aa200ba6f4fccf8586539774b44d2cdb417488172c36c4c3df5a4dc`
* checker `2eaa625e76ca9e34d9253fa42223efdbc149f99b7996f198e82ea034563a6daa`
* seed `b5ea881fefc64c14dafa59c8639a0786224e81b75bb2517eccb1e0021fbb10aa`
* result `6220007f2309e1467f2a2175631fe62bca9eba142e0c0ceed3a7c95e752fdd23`

The [independent audit](../../reviews/nine-sharing-sign28-sextic-frontier-independent/README.md)
passed the sequential substitutions, coefficient paths and exact-degree
argument. The reconstruction remains conditional on the stated model
properties; no Lean bridge or iPRA endpoint is claimed.
