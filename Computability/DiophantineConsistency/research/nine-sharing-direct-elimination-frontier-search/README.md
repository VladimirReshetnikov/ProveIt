# Direct positive-gate elimination frontier from sign23

`search.py` enumerates every ordered sequence of direct positive single-variable
gate eliminations from the pinned external sign23 AST, up to five steps, using
only nonnegative syntactic right sides. The 65 visited ordered states cover the
four eligible gates `Y`, `E`, `kY` and `normalized_S`; no additional direct
positive gates become eligible in these branches. The best residual syntactic
degree bounds for 23, 22, 21, 20 and 19 witnesses are respectively 4, 6, 7,
10 and 22. Squaring gives upper bounds 8, 12, 14, 20 and 44: these reproduce
the existing sign23–sign19 candidate frontier. At 20 witnesses the best
three-gate set is E/kY/normalized_S in any order; at 21 it is kY/normalized_S.

This finite syntax search does not prove that these are optimal equations,
exclude other types of variable elimination, account for cancellation, bind
JSON to Lean, establish a model bridge, or prove exact algebraic degrees. The
source AST and coefficient-port sign conditions are inherited assumptions for
this exploration. The command `python3 -I -S -B search.py > result.json` exited
0. Source seed SHA-256:
`ee6079ea26dd120fab39789f83034947c18e0c8806945a1fc75fca62e1c65d41`;
search SHA-256:
`90c512bf37d0874b4dca1b5141b605819c9dd572cfa9e364ef2665ca6189a986`;
result SHA-256:
`effaeb5ca24866a2210077b9ed135104f07fe6a66dddbb55a9a2f141c5953397`.

The [independent audit](../../reviews/nine-sharing-direct-elimination-frontier-independent/README.md)
passed; the search packet is frozen.
