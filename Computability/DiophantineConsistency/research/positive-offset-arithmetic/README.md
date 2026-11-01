# Positive coordinates for arbitrary residual expressions

For an integer-expression syntax `e`, let `decrement e` replace each variable
by that variable minus one. `positiveShift_decrement_zero_iff` proves in every
IΣ₁ model that evaluating `decrement e` on coordinates shifted by one has the
same zero test as evaluating `e` on the original nonnegative coordinates.
The proof works through signed-pair equivalence, including subtraction, and
requires no positivity hypothesis on the original coordinates.

The [paired model replay](../../reviews/positive-offset-arithmetic-model-replay/README.md)
matched on a historical provider. This provides a generic positive-witness
adapter for future compilers; it is not an equation-specific equivalence or
an iPRA endpoint. The structural degree bound of this substitution is checked
separately by `PositiveOffsetSyntaxDegree`.
