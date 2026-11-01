# Structural degree of the positive-coordinate offset

`PositiveOffsetSyntaxDegree.degree_decrement` proves that substituting
`x - 1` for every variable leaves the standard recursively computed syntax
degree exactly unchanged. Its [corrected paired replay](../../reviews/positive-offset-degree-model-replay-v2/README.md)
matched on a historical provider and Lean reports no axioms. The
[initial failed attempt](../../reviews/positive-offset-degree-model-replay/README.md)
is retained: its report parser incorrectly expected an axiom list for a theorem
that has none.

This is a syntactic-degree statement. Deriving an exact or upper bound for the
actual polynomial produced by a concrete gate compiler remains separate work.
