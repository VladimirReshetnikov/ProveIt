# Restricted sequential positive-cut survey

This external source-pinned survey starts with the 31-witness sextic AST. At
each step it considers a displayed positive cut whose right-hand side has
only nonnegative numerals, variables, natural ports, addition and
multiplication. It substitutes that right-hand side into the remaining
displayed residuals and retains the step only if their syntactic degrees are
at most 3. No cancellation, algebraic rewriting, alternative residual
encoding or signed-cut argument is attempted. Coordinate indices are kept
fixed, since the survey counts removed witnesses rather than constructing a
serialized smaller AST.

The complete search in this restricted space visits 27 sequence nodes and
has 12 terminal paths, all of length 3. The possible sets are
`{X, c2, normalized_S2}` and `{X, Dc2, normalized_S2}`; the independently
reviewed [28-witness candidate](../nine-sharing-sign28-sextic-candidate/)
constructs one of these paths with shifted coordinates. This is not a
semantic lower bound, a proof that the sextic cannot be reduced further,
or evidence of Lean equivalence or an iPRA endpoint.

The command `python3 -I -S -B survey.py` exited 0 and generated
`result.json`. SHA-256: script
`2a697e8b254011a6d33a777aeec71f24ae4b805aa4eb93dd11b0161e1d0dfda4`;
result `b6d4a736e8425fd70426d195bb36ecc7665f2885ab185174810dbb9963c4d434`.
The [independent review](../../reviews/nine-sharing-sign31-positive-cut-survey-frontier-independent/README.md)
reproduced the sequence nodes and terminal paths within the same restricted
syntactic scope.
